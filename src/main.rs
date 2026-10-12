use crabsat::dimacs;
use crabsat::proof::Proof;
use crabsat::{Options, SolveResult, Solver};
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
                    v.parse().unwrap_or_else(|_| die(&format!("invalid value in '{arg}'")))
                };
                match name {
                    "time" => {
                        time_limit = Some(
                            value.parse().unwrap_or_else(|_| die(&format!("invalid '{arg}'"))),
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
    let base_opts = opts.clone();
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
        let out: Box<dyn Write> = if path == "-" {
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
    let reader: Box<dyn io::Read> = if input == "-" {
        Box::new(io::stdin())
    } else {
        dimacs::open(input).unwrap_or_else(|e| die(&format!("can not read '{input}': {e}")))
    };
    let mut original: Vec<Vec<i32>> = Vec::new();
    let keep = check || threads > 1;
    let header = dimacs::parse(reader, strict, |c| {
        if keep {
            original.push(c.to_vec());
        }
        solver.add_clause_dimacs(c);
    })
    .unwrap_or_else(|e| die(&format!("parse error in '{input}': {e}")));
    solver.reserve_vars(header.vars);
    // Fresh variables introduced by the solver are not part of the model.
    let original_vars = solver.vars;
    msg(&format!(
        "parsed {} variables {} clauses in {:.2}s",
        header.vars,
        header.clauses,
        solver.seconds()
    ));

    let flag = Arc::new(AtomicBool::new(false));
    solver.terminate = Some(flag.clone());
    if let Some(t) = time_limit {
        let flag = flag.clone();
        std::thread::spawn(move || {
            std::thread::sleep(std::time::Duration::from_secs_f64(t));
            flag.store(true, Ordering::Relaxed);
        });
    }
    if let Some(c) = conflicts {
        solver.limits.conflicts = Some(c);
    }
    if let Some(d) = decisions {
        solver.limits.decisions = Some(d);
    }

    let (res, model, winner) = if threads > 1 {
        portfolio(&mut solver, &base_opts, &original, original_vars, threads, &flag, conflicts)
    } else {
        let res = solver.solve();
        let model = if res == SolveResult::Sat { solver.model() } else { Vec::new() };
        (res, model, 0)
    };
    if threads > 1 {
        msg(&format!("portfolio winner: solver {winner}"));
    }

    let stdout = io::stdout();
    let mut out = io::BufWriter::new(stdout.lock());
    match res {
        SolveResult::Sat => {
            if check {
                let model = &model[..original_vars];
                if std::env::var_os("CRABSAT_DEBUG_MODEL").is_some() {
                    debug_model(&solver, &original, model, 0);
                }
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

/// Options of the portfolio member `i` (member 0 uses the given options).
fn diversify(base: &Options, i: usize) -> Options {
    let mut o = base.clone();
    o.seed = i as u64;
    o.quiet = true;
    o.verbose = 0;
    o.check = false;
    match i % 8 {
        1 => o.stable = 2,
        2 => o.stable = 0,
        3 => o.phase = false,
        4 => o.target = 2,
        5 => o.chrono = false,
        6 => {
            o.stable = 2;
            o.phase = false;
        }
        7 => o.tier2 = 8,
        _ => {}
    }
    o
}

/// Run `threads` diversified solvers sharing units; the first result wins.
fn portfolio(
    main: &mut Solver,
    base: &Options,
    clauses: &[Vec<i32>],
    vars: usize,
    threads: usize,
    flag: &Arc<AtomicBool>,
    conflicts: Option<u64>,
) -> (SolveResult, Vec<i32>, usize) {
    let shared = Arc::new(crabsat::share::Shared::new(vars));
    let result: std::sync::Mutex<Option<(SolveResult, Vec<i32>, usize)>> = Default::default();
    let finish = |res: SolveResult, model: Vec<i32>, id: usize| {
        if res == SolveResult::Unknown {
            return;
        }
        let mut r = result.lock().unwrap();
        if r.is_none() {
            *r = Some((res, model, id));
            flag.store(true, Ordering::Relaxed);
        }
    };
    main.shared = Some(shared.clone());
    std::thread::scope(|scope| {
        for i in 1..threads {
            let shared = shared.clone();
            let flag = flag.clone();
            let finish = &finish;
            scope.spawn(move || {
                let mut s = Solver::new(diversify(base, i));
                s.reserve_vars(vars);
                for c in clauses {
                    s.add_clause_dimacs(c);
                }
                s.terminate = Some(flag);
                s.shared = Some(shared);
                s.limits.conflicts = conflicts;
                let res = s.solve();
                let model = if res == SolveResult::Sat { s.model() } else { Vec::new() };
                if res == SolveResult::Sat && std::env::var_os("CRABSAT_DEBUG_MODEL").is_some() {
                    debug_model(&s, clauses, &model, i);
                }
                finish(res, model, i);
            });
        }
        let res = main.solve();
        let model = if res == SolveResult::Sat { main.model() } else { Vec::new() };
        finish(res, model, 0);
        if res == SolveResult::Unknown && !flag.load(Ordering::Relaxed) {
            // Conflict limit reached: let the others stop too.
            flag.store(true, Ordering::Relaxed);
        }
    });
    result.into_inner().unwrap().unwrap_or((SolveResult::Unknown, Vec::new(), 0))
}

fn debug_model(s: &Solver, clauses: &[Vec<i32>], model: &[i32], id: usize) {
    for c in clauses {
        if c.iter().any(|&l| model[l.unsigned_abs() as usize - 1] == l) {
            continue;
        }
        eprintln!("solver {id}: violated {c:?} imported {}", s.stats.imported_units);
        let target: Vec<crabsat::Lit> = c.iter().map(|&d| crabsat::Lit::from_dimacs(d)).collect();
        s.debug_reconstruct(&target);
        for &d in c {
            let lit = crabsat::Lit::from_dimacs(d);
            let a = s.assigned[lit.vidx()];
            eprintln!(
                "  {d}: value {} level {} flags {} in-extension-as-witness {}",
                s.value(lit),
                a.level,
                s.flags[lit.vidx()],
                s.extension.iter().any(|&e| e & crabsat::solver::WITNESS != 0 && (e & !crabsat::solver::WITNESS) >> 1 == lit.var()),
            );
        }
        return;
    }
}

fn print_statistics(s: &Solver) {
    let st = &s.stats;
    let t = s.seconds().max(1e-9);
    let line = |name: &str, v: u64, extra: String| println!("c {name:<22} {v:>14} {extra}");
    println!("c ---- [ statistics ] ----");
    line("conflicts", st.conflicts, format!("{:.0} per sec", st.conflicts as f64 / t));
    line("decisions", st.decisions, String::new());
    line("propagations", st.propagations, format!("{:.0} per sec", st.propagations as f64 / t));
    line("search ticks", st.search_ticks, String::new());
    line("restarts", st.restarts, format!("reused levels {}", st.restarts_reused_levels));
    line("switched", st.switched, String::new());
    line("rephased", st.rephased, String::new());
    line("reductions", st.reductions, format!("reduced {}", st.clauses_reduced));
    line("chronological", st.chronological, String::new());
    line("learned", st.clauses_learned, String::new());
    let lits = st.literals_learned.max(1) as f64;
    line("literals deduced", st.literals_deduced, String::new());
    line("literals minimized", st.literals_minimized, format!("{:.1}%", 100.0 * st.literals_minimized as f64 / st.literals_deduced.max(1) as f64));
    line("literals shrunken", st.literals_shrunken, format!("{:.1}%", 100.0 * st.literals_shrunken as f64 / st.literals_deduced.max(1) as f64));
    line("literals learned", st.literals_learned, format!("{:.1} per clause", lits / st.clauses_learned.max(1) as f64));
    line("eagerly subsumed", st.eagerly_subsumed, String::new());
    line("otfs", st.otfs_strengthened, format!("strengthened ({} subsumed)", st.otfs_subsumed));
    line("units", st.units, String::new());
    line("eliminations", st.eliminations, String::new());
    line("eliminated", st.eliminated, format!("{:.1}% of variables", 100.0 * st.eliminated as f64 / s.vars.max(1) as f64));
    line("resolutions", st.eliminate_resolutions, String::new());
    line("subsumed", st.subsumed, String::new());
    line("strengthened", st.strengthened, String::new());
    line("probings", st.probings, String::new());
    line("failed", st.failed, String::new());
    line("transitive", st.transitive_reduced, "reduced binary clauses".to_string());
    line("substituted", st.substituted, String::new());
    line("vivified", st.vivified, format!("of {} checked", st.vivify_checks));
    line("probing ticks", st.probing_ticks, String::new());
    line("factorizations", st.factorizations, String::new());
    line("factored", st.factored, "fresh variables".to_string());
    line("factor ticks", st.factor_ticks, String::new());
    line("congruences", st.congruences, String::new());
    line("congruent", st.congruent, String::new());
    line("walks", st.walks, format!("{} flips", st.walk_flips));
    line("sweeps", st.sweeps, format!("{} units {} equivalences", st.sweep_units, st.sweep_equivalences));
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
    ] {
        println!("c {:<22} {:>14.2} seconds {:5.1}%", format!("time {name}"), v, 100.0 * v / t);
    }
    println!("c {:<22} {:>14.2} seconds", "process time", t);
}
