//! DIMACS CNF parser.  Compressed inputs (`.xz`, `.gz`, `.bz2`, `.lzma`)
//! are decompressed through the corresponding external tool, like Kissat.

use std::fs::File;
use std::io::{self, BufReader, Read};
use std::process::{Command, Stdio};

pub struct Header {
    pub vars: usize,
    pub clauses: usize,
}

/// Open a (possibly compressed) file for reading.
pub fn open(path: &str) -> io::Result<Box<dyn Read>> {
    let tool = if path.ends_with(".xz") || path.ends_with(".lzma") {
        Some("xz")
    } else if path.ends_with(".gz") {
        Some("gzip")
    } else if path.ends_with(".bz2") {
        Some("bzip2")
    } else {
        None
    };
    match tool {
        Some(tool) => {
            let child = Command::new(tool)
                .arg("-dc")
                .arg(path)
                .stdout(Stdio::piped())
                .spawn()
                .map_err(|e| io::Error::other(format!("failed to run '{tool}': {e}")))?;
            Ok(Box::new(child.stdout.unwrap()))
        }
        None => Ok(Box::new(File::open(path)?)),
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
        Bytes { reader: BufReader::new(reader), buf: vec![0; 1 << 16], pos: 0, len: 0, line: 1 }
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
            let vars = parts[2].parse().map_err(|_| err(b.line, "invalid variables"))?;
            let clauses = parts[3].parse().map_err(|_| err(b.line, "invalid clauses"))?;
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
        if let Some(ch) = c {
            if !ch.is_ascii_whitespace() {
                return Err(err(b.line, "expected white space after literal"));
            }
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
            lits.push(if negative { -(value as i32) } else { value as i32 });
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
    fn parse_errors() {
        assert!(parse("1 2 0\n".as_bytes(), true, |_| {}).is_err());
        assert!(parse("p cnf 1 1\n2 0\n".as_bytes(), true, |_| {}).is_err());
        assert!(parse("p cnf 2 1\n1 2\n".as_bytes(), true, |_| {}).is_err());
    }
}
