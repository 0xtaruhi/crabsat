//! End-to-end tests of the command line solver (run on every platform).

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

const SAT: &str = "c satisfiable\np cnf 3 3\n1 2 0\n-1 3 0\n-2 -3 0\n";
const UNSAT: &str = "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n";

fn temp_file(name: &str, data: &[u8]) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("crabsat-cli-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    std::fs::write(&path, data).unwrap();
    path
}

fn gzip(text: &str) -> Vec<u8> {
    let mut enc = flate2::write::GzEncoder::new(Vec::new(), flate2::Compression::fast());
    enc.write_all(text.as_bytes()).unwrap();
    enc.finish().unwrap()
}

/// Run the solver on `args` (and optional standard input): exit code and
/// standard output.
fn run(args: &[&std::ffi::OsStr], stdin: Option<&[u8]>) -> (i32, String) {
    let mut child = Command::new(env!("CARGO_BIN_EXE_crabsat"))
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut input = child.stdin.take().unwrap();
    if let Some(data) = stdin {
        input.write_all(data).unwrap();
    }
    drop(input);
    let out = child.wait_with_output().unwrap();
    (
        out.status.code().unwrap(),
        String::from_utf8(out.stdout).unwrap(),
    )
}

fn check_model(output: &str) {
    let model: Vec<i32> = output
        .lines()
        .filter_map(|l| l.strip_prefix("v "))
        .flat_map(|l| l.split_whitespace().map(|x| x.parse::<i32>().unwrap()))
        .collect();
    for clause in [[1, 2], [-1, 3], [-2, -3]] {
        assert!(clause.iter().any(|l| model.contains(l)), "{output}");
    }
}

fn os(p: &Path) -> &std::ffi::OsStr {
    p.as_os_str()
}

#[test]
fn plain_and_compressed_files() {
    let plain = temp_file("sat.cnf", SAT.as_bytes());
    let (code, out) = run(&[os(&plain)], None);
    assert_eq!(code, 10);
    assert!(out.contains("s SATISFIABLE"));
    check_model(&out);

    let gz = temp_file("unsat.cnf.gz", &gzip(UNSAT));
    let (code, out) = run(&[os(&gz)], None);
    assert_eq!(code, 20);
    assert!(out.contains("s UNSATISFIABLE"));
}

#[test]
fn standard_input() {
    let (code, out) = run(&["-q".as_ref()], Some(SAT.as_bytes()));
    assert_eq!(code, 10);
    check_model(&out);
    let (code, _) = run(&["-q".as_ref(), "-".as_ref()], Some(&gzip(UNSAT)));
    assert_eq!(code, 20);
}

#[test]
fn proof_file() {
    let cnf = temp_file("proof.cnf", UNSAT.as_bytes());
    let proof = cnf.with_extension("drat");
    let (code, _) = run(&["--no-binary".as_ref(), os(&cnf), os(&proof)], None);
    assert_eq!(code, 20);
    let text = std::fs::read_to_string(&proof).unwrap();
    assert!(
        text.lines().any(|l| l.trim() == "0"),
        "no empty clause: {text}"
    );
}

#[test]
fn invalid_input() {
    let bad = temp_file("bad.cnf", b"p cnf 1 1\n2 0\n");
    let (code, _) = run(&["--strict".as_ref(), os(&bad)], None);
    assert_eq!(code, 1);
}
