use crabsat::{Options, Proof, SolveResult, Solver, dimacs};
use std::io::{self, Write};
use std::process::exit;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

fn usage() -> String {
    format!(
        "usage: crabsat [ <option> ... ] [ <dimacs> [ <proof> ] ]\n\n\
         where <option> is one of\n\
         \x20 -q | --quiet          no messages\n\
         \x20 -v                    increase verbosity\n\
         \x20 -n                    do not print witness\n\
         \x20 --strict              strict DIMACS parsing\n\
         \x20 --time=<seconds>      time limit\n\
         \x20 --conflicts=<n>       conflict limit\n\
         \x20 --decisions=<n>       decision limit\n\
         \x20 --no-binary           text proof format\n\
         \x20 --threads=<n>         portfolio of <n> diversified solvers\n\
         \nand solver options (with defaults):\n{}",
        Options::usage()
    )
}

fn die(msg: &str) -> ! {
    eprintln!("crabsat: error: {msg}");
    exit(1);
}

fn main() {
    let mut opts = Options::default();
    let mut files: Vec<String> = Vec::new();
    let mut witness = true;
    let mut strict = false;
    let mut time_limit: Option<f64> = None;
    let mut conflicts: Option<u64> = None;
    let mut decisions: Option<u64> = None;
    let mut threads: usize = 1;
    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "-h" | "--help" => {
                print!("{}", usage());
                exit(0);
            }
            "-q" | "--quiet" => opts.quiet = true,
            "-v" => opts.verbose += 1,
            "-n" => witness = false,
            "--strict" => strict = true,
            "--no-binary" => opts.binary = false,
            _ if arg.starts_with("--") => {
                let body = &arg[2..];
                let (name, value) = match body.split_once('=') {
                    Some((n, v)) => (n, v),
                    None => match body.strip_prefix("no-") {
                        Some(n) => (n, "0"),
                        None => (body, "1"),
                    },
                };
                let parse_u64 = |v: &str| -> u64 {
                    v.parse()
                        .unwrap_or_else(|_| die(&format!("invalid value in '{arg}'")))
                };
                match name {
                    "time" => {
                        time_limit = Some(
                            value
                                .parse()
                                .unwrap_or_else(|_| die(&format!("invalid '{arg}'"))),
                        )
                    }
                    "conflicts" => conflicts = Some(parse_u64(value)),
                    "decisions" => decisions = Some(parse_u64(value)),
                    "threads" => threads = parse_u64(value).max(1) as usize,
                    _ => opts.set(name, value).unwrap_or_else(|e| die(&e)),
                }
            }
            _ if arg.starts_with('-') && arg != "-" => die(&format!("invalid option '{arg}'")),
            _ => files.push(arg),
        }
    }
    if files.len() > 2 {
        die("too many files");
    }
    if threads > 1 && files.len() > 1 {
        die("proofs are not supported with '--threads'");
    }
    let quiet = opts.quiet;
    let check = opts.check;
    let binary_proof = opts.binary;
    let mut solver = Solver::new(opts);
    let msg = |s: &str| {
        if !quiet {
            println!("c {s}");
        }
    };
    msg("crabsat SAT solver");

    if let Some(path) = files.get(1) {
        let out: Box<dyn Write + Send> = if path == "-" {
            Box::new(io::stdout())
        } else {
            Box::new(
                std::fs::File::create(path)
                    .unwrap_or_else(|e| die(&format!("can not write proof '{path}': {e}"))),
            )
        };
        solver.set_proof(Proof::new(out, binary_proof && path != "-"));
        msg(&format!("writing proof to '{path}'"));
    }

    let input = files.first().map(String::as_str).unwrap_or("-");
    let reader =
        dimacs::open(input).unwrap_or_else(|e| die(&format!("can not read '{input}': {e}")));
    let mut original: Vec<Vec<i32>> = Vec::new();
    let keep = check || threads > 1;
    let header = dimacs::parse(reader, strict, |c| {
        if keep {
            original.push(c.to_vec());
        }
        solver.add_clause(c);
    })
    .unwrap_or_else(|e| die(&format!("parse error in '{input}': {e}")));
    solver.reserve_vars(header.vars);
    // Fresh variables introduced by the solver are not part of the model.
    let original_vars = solver.num_vars();
    msg(&format!(
        "parsed {} variables {} clauses in {:.2}s",
        header.vars,
        header.clauses,
        solver.seconds()
    ));

    let flag = Arc::new(AtomicBool::new(false));
    solver.set_terminate_flag(flag.clone());
    if let Some(t) = time_limit {
        let flag = flag.clone();
        std::thread::spawn(move || {
            std::thread::sleep(std::time::Duration::from_secs_f64(t));
            flag.store(true, Ordering::Relaxed);
        });
    }
    solver.set_conflict_limit(conflicts);
    solver.set_decision_limit(decisions);

    let (res, model) = if threads > 1 {
        let r = solver.solve_portfolio(&original, threads);
        msg(&format!("portfolio winner: solver {}", r.winner));
        (r.result, r.model)
    } else {
        let res = solver.solve();
        let model = if res == SolveResult::Sat {
            solver.model()
        } else {
            Vec::new()
        };
        (res, model)
    };

    let stdout = io::stdout();
    let mut out = io::BufWriter::new(stdout.lock());
    match res {
        SolveResult::Sat => {
            if check {
                let model = &model[..original_vars];
                for c in &original {
                    if !c.iter().any(|&l| model[l.unsigned_abs() as usize - 1] == l) {
                        die(&format!("model does not satisfy clause {c:?}"));
                    }
                }
                msg("model checked");
            }
            writeln!(out, "s SATISFIABLE").unwrap();
            if witness {
                let mut line = String::from("v");
                for &d in model.iter().take(original_vars) {
                    let s = format!(" {d}");
                    if line.len() + s.len() > 78 {
                        writeln!(out, "{line}").unwrap();
                        line = String::from("v");
                    }
                    line.push_str(&s);
                }
                writeln!(out, "{line} 0").unwrap();
            }
        }
        SolveResult::Unsat => writeln!(out, "s UNSATISFIABLE").unwrap(),
        SolveResult::Unknown => writeln!(out, "s UNKNOWN").unwrap(),
    }
    out.flush().unwrap();
    if !quiet {
        print_statistics(&solver);
    }
    exit(res.exit_code());
}

fn print_statistics(s: &Solver) {
    let st = s.stats();
    let t = s.seconds().max(1e-9);
    let line = |name: &str, v: u64, extra: String| println!("c {name:<22} {v:>14} {extra}");
    println!("c ---- [ statistics ] ----");
    line(
        "conflicts",
        st.conflicts,
        format!("{:.0} per sec", st.conflicts as f64 / t),
    );
    line("decisions", st.decisions, String::new());
    line(
        "propagations",
        st.propagations,
        format!("{:.0} per sec", st.propagations as f64 / t),
    );
    line("search ticks", st.search_ticks, String::new());
    line(
        "restarts",
        st.restarts,
        format!("reused levels {}", st.restarts_reused_levels),
    );
    line("switched", st.switched, String::new());
    line("rephased", st.rephased, String::new());
    line(
        "reductions",
        st.reductions,
        format!("reduced {}", st.clauses_reduced),
    );
    line("chronological", st.chronological, String::new());
    line("learned", st.clauses_learned, String::new());
    let lits = st.literals_learned.max(1) as f64;
    line("literals deduced", st.literals_deduced, String::new());
    line(
        "literals minimized",
        st.literals_minimized,
        format!(
            "{:.1}%",
            100.0 * st.literals_minimized as f64 / st.literals_deduced.max(1) as f64
        ),
    );
    line(
        "literals shrunken",
        st.literals_shrunken,
        format!(
            "{:.1}%",
            100.0 * st.literals_shrunken as f64 / st.literals_deduced.max(1) as f64
        ),
    );
    line(
        "literals learned",
        st.literals_learned,
        format!("{:.1} per clause", lits / st.clauses_learned.max(1) as f64),
    );
    line("eagerly subsumed", st.eagerly_subsumed, String::new());
    line(
        "otfs",
        st.otfs_strengthened,
        format!("strengthened ({} subsumed)", st.otfs_subsumed),
    );
    line("units", st.units, String::new());
    line("eliminations", st.eliminations, String::new());
    line(
        "eliminated",
        st.eliminated,
        format!(
            "{:.1}% of variables",
            100.0 * st.eliminated as f64 / s.num_vars().max(1) as f64
        ),
    );
    line("resolutions", st.eliminate_resolutions, String::new());
    line("subsumed", st.subsumed, String::new());
    line("strengthened", st.strengthened, String::new());
    line("probings", st.probings, String::new());
    line("failed", st.failed, String::new());
    line(
        "transitive",
        st.transitive_reduced,
        "reduced binary clauses".to_string(),
    );
    line("substituted", st.substituted, String::new());
    line(
        "vivified",
        st.vivified,
        format!("of {} checked", st.vivify_checks),
    );
    line("probing ticks", st.probing_ticks, String::new());
    line("factorizations", st.factorizations, String::new());
    line("factored", st.factored, "fresh variables".to_string());
    line("factor ticks", st.factor_ticks, String::new());
    line("congruences", st.congruences, String::new());
    line("congruent", st.congruent, String::new());
    line("walks", st.walks, format!("{} flips", st.walk_flips));
    line(
        "sweeps",
        st.sweeps,
        format!(
            "{} units {} equivalences",
            st.sweep_units, st.sweep_equivalences
        ),
    );
    line("sweep ticks", st.sweep_ticks, String::new());
    for (name, v) in [
        ("eliminate", st.time_eliminate),
        ("probe (total)", st.time_probe),
        ("vivify", st.time_vivify),
        ("sweep", st.time_sweep),
        ("congruence", st.time_congruence),
        ("factor", st.time_factor),
        ("walk", st.time_walk),
        ("reduce", st.time_reduce),
        ("lucky", st.time_lucky),
        ("stable mode", st.time_stable),
        ("focused mode", st.time_focused),
    ] {
        println!(
            "c {:<22} {:>14.2} seconds {:5.1}%",
            format!("time {name}"),
            v,
            100.0 * v / t
        );
    }
    println!("c {:<22} {:>14.2} seconds", "process time", t);
}
