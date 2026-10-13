//! DRAT proof output (text or binary format).

use crate::types::Lit;
use std::io::{self, BufWriter, Write};

pub struct Proof {
    out: BufWriter<Box<dyn Write>>,
    binary: bool,
    pub added: u64,
    pub deleted: u64,
    /// Internal variable -> external variable.
    pub map: Vec<u32>,
}

impl Proof {
    pub fn new(out: Box<dyn Write>, binary: bool) -> Proof {
        Proof {
            out: BufWriter::with_capacity(1 << 20, out),
            binary,
            added: 0,
            deleted: 0,
            map: Vec::new(),
        }
    }

    #[inline]
    fn external(&self, l: Lit) -> Lit {
        match self.map.get(l.vidx()) {
            Some(&e) => Lit::new(e, l.negated()),
            None => l,
        }
    }

    fn line(&mut self, tag: u8, lits: &[Lit]) -> io::Result<()> {
        if self.binary {
            let mut buf = [0u8; 5];
            self.out.write_all(&[tag])?;
            for &l in lits {
                let l = self.external(l);
                // Binary DRAT maps DIMACS literal l to 2*|l| + (l < 0).
                let mut x = 2 * (l.var() + 1) + l.negated() as u32;
                let mut n = 0;
                while x > 127 {
                    buf[n] = (x as u8 & 127) | 128;
                    x >>= 7;
                    n += 1;
                }
                buf[n] = x as u8;
                self.out.write_all(&buf[..=n])?;
            }
            self.out.write_all(&[0])
        } else {
            if tag == b'd' {
                self.out.write_all(b"d ")?;
            }
            for &l in lits {
                let l = self.external(l);
                write!(self.out, "{} ", l.to_dimacs())?;
            }
            self.out.write_all(b"0\n")
        }
    }

    pub fn add(&mut self, lits: &[Lit]) {
        self.added += 1;
        self.line(b'a', lits).expect("failed to write proof");
    }

    pub fn delete(&mut self, lits: &[Lit]) {
        self.deleted += 1;
        self.line(b'd', lits).expect("failed to write proof");
    }

    pub fn flush(&mut self) {
        self.out.flush().expect("failed to flush proof");
    }
}

impl Drop for Proof {
    fn drop(&mut self) {
        let _ = self.out.flush();
    }
}
