//! Solver options.  Defaults follow Kissat 4.0.4 (`options.h`).

macro_rules! options {
    ($( $name:ident : $ty:ty = $default:expr, $help:expr; )*) => {
        #[derive(Clone, Debug)]
        pub struct Options {
            $( pub $name: $ty, )*
        }

        impl Default for Options {
            fn default() -> Self {
                Options { $( $name: $default, )* }
            }
        }

        impl Options {
            /// Set an option by name from a string value.
            pub fn set(&mut self, name: &str, value: &str) -> Result<(), String> {
                match name {
                    $( stringify!($name) => {
                        self.$name = parse_value::<$ty>(value)
                            .ok_or_else(|| format!("invalid value '{value}' for option '{name}'"))?;
                        Ok(())
                    } )*
                    _ => Err(format!("unknown option '{name}'")),
                }
            }

            pub fn usage() -> String {
                let mut s = String::new();
                $( s.push_str(&format!("  --{}={:<12} {}\n", stringify!($name),
                    format!("{:?}", { let d: $ty = $default; d }), $help)); )*
                s
            }
        }
    };
}

trait ParseValue: Sized {
    fn parse_value(s: &str) -> Option<Self>;
}

impl ParseValue for bool {
    fn parse_value(s: &str) -> Option<bool> {
        match s {
            "1" | "true" => Some(true),
            "0" | "false" => Some(false),
            _ => None,
        }
    }
}

impl ParseValue for u64 {
    fn parse_value(s: &str) -> Option<u64> {
        // Accept "1e3" style values like Kissat.
        s.parse::<u64>().ok().or_else(|| s.parse::<f64>().ok().map(|f| f as u64))
    }
}

impl ParseValue for u32 {
    fn parse_value(s: &str) -> Option<u32> {
        u64::parse_value(s).and_then(|v| u32::try_from(v).ok())
    }
}

fn parse_value<T: ParseValue>(s: &str) -> Option<T> {
    T::parse_value(s)
}

options! {
    bump: bool = true, "enable variable bumping";
    bumpreasons: bool = true, "bump reason side literals too";
    bumpreasonslimit: u64 = 10, "relative reason literals limit";
    bumpreasonsrate: u64 = 10, "decision rate limit";
    chrono: bool = true, "allow chronological backtracking";
    chronolevels: u32 = 100, "maximum jumped over levels";
    decay: u64 = 50, "per mille scores decay";
    eagersubsume: u32 = 4, "eagerly subsume previous learned clauses";
    emafast: u64 = 33, "fast exponential moving average window";
    emaslow: u64 = 100_000, "slow exponential moving average window";
    minimize: bool = true, "learned clause minimization";
    otfs: bool = true, "on-the-fly strengthening";
    minimizedepth: u32 = 1000, "minimization depth";
    modeinit: u64 = 1000, "initial focused conflicts limit";
    modeint: u64 = 1000, "focused conflicts interval";
    phase: bool = true, "initial decision phase";
    phasesaving: bool = true, "enable phase saving";
    promote: bool = true, "promote clauses";
    reduce: bool = true, "learned clause reduction";
    reducehigh: u64 = 900, "high reduce fraction per mille";
    reduceinit: u64 = 1000, "initial reduce interval";
    reduceint: u64 = 1000, "base reduce interval";
    reducelow: u64 = 500, "low reduce fraction per mille";
    reluctant: bool = true, "stable reluctant doubling restarting";
    reluctantint: u64 = 1024, "reluctant interval";
    reluctantlim: u64 = 1 << 20, "reluctant limit (0=unlimited)";
    rephase: bool = true, "reinitialization of decision phases";
    rephaseinit: u64 = 1000, "initial rephase interval";
    rephaseint: u64 = 1000, "base rephase interval";
    restart: bool = true, "enable restarts";
    restartint: u64 = 1, "base restart interval";
    restartmargin: u64 = 10, "fast/slow margin in percent";
    restartreusetrail: bool = true, "restarts tries to reuse trail";
    seed: u64 = 0, "random seed";
    tumble: bool = false, "initial decision order by first occurrence";
    shrink: u32 = 3, "learned clauses (1=bin,2=lrg,3=rec)";
    stable: u32 = 1, "enable stable search mode (0=focused,1=switch,2=stable)";
    target: u32 = 1, "target phases (1=stable,2=focused)";
    tier1: u32 = 2, "learned clause tier one glue limit";
    tier1relative: u64 = 500, "relative tier one glue limit";
    tier2: u32 = 6, "learned clause tier two glue limit";
    tier2relative: u64 = 900, "relative tier two glue limit";
    // Simplification
    simplify: bool = true, "enable probing and elimination";
    mineffort: u64 = 10, "minimum absolute effort in millions";
    eliminate: bool = true, "bounded variable elimination BVE";
    eliminatebound: u32 = 16, "maximum elimination bound";
    eliminateclslim: u64 = 100, "elimination clause size limit";
    eliminateeffort: u64 = 100, "effort in per mille";
    eliminateinit: u64 = 500, "initial elimination interval";
    eliminateint: u64 = 500, "base elimination interval";
    eliminateocclim: u64 = 2000, "elimination occurrence limit";
    eliminaterounds: u32 = 2, "elimination rounds limit";
    ands: bool = true, "extract and eliminate and gates";
    ifthenelse: bool = true, "extract and eliminate if-then-else gates";
    xors: bool = false, "extract and eliminate XOR gates";
    forwardeffort: u64 = 100, "effort in per mille";
    subsumeclslim: u64 = 1000, "subsumption clause size limit";
    probe: bool = true, "enable probing";
    probeeffort: u64 = 20, "failed literal probing effort in per mille";
    probeinit: u64 = 100, "initial probing interval";
    probeint: u64 = 100, "probing interval";
    substitute: bool = true, "equivalent literal substitution";
    transitive: bool = true, "transitive reduction of binary clauses";
    transitiveeffort: u64 = 20, "effort in per mille";
    vivify: bool = true, "vivify clauses";
    vivifyeffort: u64 = 100, "effort in per mille";
    vivifyirr: u64 = 3, "relative irredundant effort";
    vivifytier1: u64 = 3, "relative tier1 effort";
    vivifytier2: u64 = 3, "relative tier2 effort";
    vivifytier3: u64 = 1, "relative tier3 effort";
    factor: bool = true, "bounded variable addition";
    factordelay: u64 = 4, "delaying factor";
    factoreffort: u64 = 50, "bounded variable effort in per mille";
    factoriniticks: u64 = 700, "initial ticks in millions";
    factorsize: u64 = 5, "bounded variable addition clause size";
    factorminreduction: u64 = 2, "minimum clause reduction of a factorization";
    preprocess: bool = true, "initial preprocessing";
    congruence: bool = true, "congruence closure on extracted gates";
    congruenceandarity: u64 = 1_000_000, "AND gate arity limit";
    congruenceands: bool = true, "extract AND gates for congruence closure";
    congruencebinaries: bool = true, "extract binary clauses from ternary ones";
    congruenceites: bool = true, "extract ITE gates for congruence closure";
    congruencexorarity: u64 = 4, "congruence XOR gate arity limit";
    congruencexors: bool = true, "extract XOR gates for congruence closure";
    walkeffort: u64 = 50, "walk effort in per mille";
    warmup: bool = true, "initialize phases by unit propagation before walking";
    lucky: bool = true, "try some lucky assignments";
    randec: bool = true, "random decisions (focused mode)";
    randecinit: u64 = 500, "initial random decisions interval";
    randecint: u64 = 500, "random decisions interval";
    randeclength: u64 = 10, "random conflicts length";
    reorder: u32 = 2, "reorder decisions (1=stable-mode-only)";
    reorderinit: u64 = 10_000, "initial reorder interval";
    reorderint: u64 = 10_000, "base reorder interval";
    reordermaxsize: u64 = 100, "reorder maximum clause size";
    sweep: bool = true, "enable SAT sweeping";
    sweepclauses: u64 = 1024, "environment clauses";
    sweepdepth: u64 = 2, "environment depth";
    sweepeffort: u64 = 100, "effort in per mille";
    sweepmaxsolves: u64 = 64, "maximum kitten calls per environment";
    sweepticks: u64 = 100_000, "kitten ticks limit per call";
    sweepvars: u64 = 256, "environment variables";
    // Output
    binary: bool = true, "binary proof format";
    verbose: u32 = 0, "verbosity level";
    quiet: bool = false, "disable all messages";
    check: bool = false, "check model against original formula";
}
