//! DIMACS CNF parser.  Compressed inputs (gzip, bzip2, xz detected by their
//! magic bytes, and `.lzma` by the file name) are decompressed with pure
//! Rust decoders when the `compression` feature is enabled (the default).

use std::fs::File;
use std::io::{self, BufRead, BufReader, Read};

pub struct Header {
    pub vars: usize,
    pub clauses: usize,
}

/// Open a (possibly compressed) file for reading; `-` is standard input.
pub fn open(path: &str) -> io::Result<Box<dyn Read>> {
    if path == "-" {
        return decompress(BufReader::new(io::stdin()), false);
    }
    decompress(BufReader::new(File::open(path)?), path.ends_with(".lzma"))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Format {
    Plain,
    Gzip,
    Bzip2,
    Xz,
    Lzma,
}

fn detect(magic: &[u8], lzma: bool) -> Format {
    if magic.starts_with(&[0x1f, 0x8b]) {
        Format::Gzip
    } else if magic.starts_with(b"BZh") {
        Format::Bzip2
    } else if magic.starts_with(&[0xfd, b'7', b'z', b'X', b'Z', 0]) {
        Format::Xz
    } else if lzma {
        Format::Lzma
    } else {
        Format::Plain
    }
}

/// Wrap `reader` in the decoder for its format.
fn decompress<R: BufRead + Send + 'static>(mut reader: R, lzma: bool) -> io::Result<Box<dyn Read>> {
    let format = detect(reader.fill_buf()?, lzma);
    #[cfg(feature = "compression")]
    {
        let decoder: Box<dyn Read + Send> = match format {
            Format::Plain => return Ok(Box::new(reader)),
            Format::Gzip => Box::new(flate2::bufread::MultiGzDecoder::new(reader)),
            Format::Bzip2 => Box::new(bzip2::bufread::MultiBzDecoder::new(reader)),
            Format::Xz => Box::new(lzma_rust2::XzReader::new(reader, true)),
            Format::Lzma => Box::new(lzma_rust2::LzmaReader::new_mem_limit(
                reader,
                u32::MAX,
                None,
            )?),
        };
        Ok(Box::new(Pipelined::new(decoder)))
    }
    #[cfg(not(feature = "compression"))]
    match format {
        Format::Plain => Ok(Box::new(reader)),
        _ => Err(io::Error::other(
            "compressed input requires the `compression` feature",
        )),
    }
}

/// Runs a decoder in a separate thread (decompression and parsing overlap,
/// like a pipe from an external decompression tool).
#[cfg(feature = "compression")]
struct Pipelined {
    chunks: std::sync::mpsc::Receiver<io::Result<Vec<u8>>>,
    chunk: Vec<u8>,
    pos: usize,
}

#[cfg(feature = "compression")]
impl Pipelined {
    const CHUNK: usize = 1 << 20;

    fn new(mut decoder: Box<dyn Read + Send>) -> Pipelined {
        let (send, chunks) = std::sync::mpsc::sync_channel(4);
        std::thread::spawn(move || {
            loop {
                let mut chunk = vec![0; Self::CHUNK];
                let mut len = 0;
                // Fill the chunk (decoders may return short reads).
                let res = loop {
                    match decoder.read(&mut chunk[len..]) {
                        Ok(0) => break Ok(()),
                        Ok(n) => {
                            len += n;
                            if len == chunk.len() {
                                break Ok(());
                            }
                        }
                        Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
                        Err(e) => break Err(e),
                    }
                };
                chunk.truncate(len);
                let done = len == 0 || res.is_err();
                let msg = res.map(|()| chunk);
                if send.send(msg).is_err() || done {
                    return;
                }
            }
        });
        Pipelined {
            chunks,
            chunk: Vec::new(),
            pos: 0,
        }
    }
}

#[cfg(feature = "compression")]
impl Read for Pipelined {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if self.pos == self.chunk.len() {
            match self.chunks.recv() {
                Ok(chunk) => self.chunk = chunk?,
                // The decoder thread finished.
                Err(_) => return Ok(0),
            }
            self.pos = 0;
        }
        let n = buf.len().min(self.chunk.len() - self.pos);
        buf[..n].copy_from_slice(&self.chunk[self.pos..self.pos + n]);
        self.pos += n;
        Ok(n)
    }
}

struct Bytes<R: Read> {
    reader: BufReader<R>,
    buf: Vec<u8>,
    pos: usize,
    len: usize,
    line: usize,
}

impl<R: Read> Bytes<R> {
    fn new(reader: R) -> Self {
        Bytes {
            reader: BufReader::new(reader),
            buf: vec![0; 1 << 16],
            pos: 0,
            len: 0,
            line: 1,
        }
    }

    #[inline]
    fn next(&mut self) -> io::Result<Option<u8>> {
        if self.pos == self.len {
            self.len = self.reader.read(&mut self.buf)?;
            self.pos = 0;
            if self.len == 0 {
                return Ok(None);
            }
        }
        let c = self.buf[self.pos];
        self.pos += 1;
        if c == b'\n' {
            self.line += 1;
        }
        Ok(Some(c))
    }
}

fn err(line: usize, msg: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, format!("line {line}: {msg}"))
}

/// Parse a DIMACS file, calling `clause` for each clause (as DIMACS ints).
pub fn parse<R: Read>(
    reader: R,
    strict: bool,
    mut clause: impl FnMut(&[i32]),
) -> io::Result<Header> {
    let mut b = Bytes::new(reader);
    let mut header: Option<Header> = None;
    let mut lits: Vec<i32> = Vec::new();
    let mut parsed = 0usize;
    let mut c = b.next()?;
    loop {
        // Skip white space.
        while let Some(ch) = c {
            if !ch.is_ascii_whitespace() {
                break;
            }
            c = b.next()?;
        }
        let Some(ch) = c else { break };
        if ch == b'c' || (ch == b'%' && header.is_some()) {
            if ch == b'%' {
                break; // SATLIB style end marker
            }
            while let Some(ch) = c {
                if ch == b'\n' {
                    break;
                }
                c = b.next()?;
            }
            continue;
        }
        if ch == b'p' {
            if header.is_some() {
                return Err(err(b.line, "duplicate header"));
            }
            let mut line = Vec::new();
            while let Some(ch) = c {
                if ch == b'\n' {
                    break;
                }
                line.push(ch);
                c = b.next()?;
            }
            let line = String::from_utf8_lossy(&line);
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.len() != 4 || parts[1] != "cnf" {
                return Err(err(b.line, "invalid header"));
            }
            let vars = parts[2]
                .parse()
                .map_err(|_| err(b.line, "invalid variables"))?;
            let clauses = parts[3]
                .parse()
                .map_err(|_| err(b.line, "invalid clauses"))?;
            header = Some(Header { vars, clauses });
            continue;
        }
        let Some(h) = header.as_ref() else {
            return Err(err(b.line, "expected header"));
        };
        let negative = ch == b'-';
        if negative {
            c = b.next()?;
        }
        let mut value: i64 = 0;
        let mut digits = 0;
        while let Some(ch) = c {
            if !ch.is_ascii_digit() {
                break;
            }
            value = value * 10 + (ch - b'0') as i64;
            if value > i32::MAX as i64 {
                return Err(err(b.line, "literal too large"));
            }
            digits += 1;
            c = b.next()?;
        }
        if digits == 0 {
            return Err(err(b.line, "expected literal"));
        }
        if let Some(ch) = c
            && !ch.is_ascii_whitespace()
        {
            return Err(err(b.line, "expected white space after literal"));
        }
        if value == 0 {
            if negative {
                return Err(err(b.line, "invalid '-0'"));
            }
            parsed += 1;
            if strict && parsed > h.clauses {
                return Err(err(b.line, "too many clauses"));
            }
            clause(&lits);
            lits.clear();
        } else {
            if strict && value as usize > h.vars {
                return Err(err(b.line, "literal exceeds maximum variable"));
            }
            lits.push(if negative {
                -(value as i32)
            } else {
                value as i32
            });
        }
    }
    let Some(h) = header else {
        return Err(err(b.line, "missing header"));
    };
    if !lits.is_empty() {
        return Err(err(b.line, "last clause not terminated"));
    }
    if strict && parsed < h.clauses {
        return Err(err(b.line, "clauses missing"));
    }
    Ok(h)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_simple() {
        let text = "c comment\np cnf 3 2\n1 -2 0\n2 3\n-1 0\n";
        let mut clauses = Vec::new();
        let h = parse(text.as_bytes(), true, |c| clauses.push(c.to_vec())).unwrap();
        assert_eq!(h.vars, 3);
        assert_eq!(clauses, vec![vec![1, -2], vec![2, 3, -1]]);
    }

    #[test]
    fn detect_formats() {
        assert_eq!(detect(&[0x1f, 0x8b, 8], false), Format::Gzip);
        assert_eq!(detect(b"BZh91AY", false), Format::Bzip2);
        assert_eq!(
            detect(&[0xfd, b'7', b'z', b'X', b'Z', 0], false),
            Format::Xz
        );
        assert_eq!(detect(b"p cnf 1 1", true), Format::Lzma);
        assert_eq!(detect(b"p cnf 1 1", false), Format::Plain);
    }

    #[cfg(feature = "compression")]
    #[test]
    fn gzip_input() {
        use std::io::Write;
        let text = "c test\np cnf 3 2\n1 -2 0\n2 3 0\n";
        let mut enc = flate2::write::GzEncoder::new(Vec::new(), flate2::Compression::fast());
        enc.write_all(text.as_bytes()).unwrap();
        let data = enc.finish().unwrap();
        let reader = decompress(io::Cursor::new(data), false).unwrap();
        let mut clauses = Vec::new();
        let header = parse(reader, true, |c| clauses.push(c.to_vec())).unwrap();
        assert_eq!((header.vars, header.clauses), (3, 2));
        assert_eq!(clauses, vec![vec![1, -2], vec![2, 3]]);
    }

    #[test]
    fn parse_errors() {
        assert!(parse("1 2 0\n".as_bytes(), true, |_| {}).is_err());
        assert!(parse("p cnf 1 1\n2 0\n".as_bytes(), true, |_| {}).is_err());
        assert!(parse("p cnf 2 1\n1 2\n".as_bytes(), true, |_| {}).is_err());
    }
}
