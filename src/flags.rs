//! Typed bit sets for per-variable flags.  Assignment flags (used during
//! conflict analysis) and variable flags (used by simplification) are
//! different types so that they can not be mixed up.

macro_rules! flag_set {
    ($(#[$meta:meta])* $name:ident { $($(#[$fmeta:meta])* $flag:ident = $bit:expr;)* }) => {
        $(#[$meta])*
        #[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
        pub struct $name(u8);

        $($(#[$fmeta])* pub const $flag: $name = $name($bit);)*

        // Not every flag set uses every helper.
        #[allow(dead_code)]
        impl $name {
            pub const EMPTY: $name = $name(0);

            /// Whether any flag of `f` is set.
            #[inline(always)]
            pub fn has(self, f: $name) -> bool {
                self.0 & f.0 != 0
            }

            /// Whether exactly the flags `want` of the flags `mask` are set.
            #[inline(always)]
            pub fn masked(self, mask: $name, want: $name) -> bool {
                self.0 & mask.0 == want.0
            }

            #[inline(always)]
            pub fn insert(&mut self, f: $name) {
                self.0 |= f.0;
            }

            #[inline(always)]
            pub fn remove(&mut self, f: $name) {
                self.0 &= !f.0;
            }
        }

        impl std::ops::BitOr for $name {
            type Output = $name;
            #[inline(always)]
            fn bitor(self, other: $name) -> $name {
                $name(self.0 | other.0)
            }
        }
    };
}

flag_set! {
    /// Flags of an assigned variable used by conflict analysis.
    AssignFlags {
        ANALYZED = 1;
        /// The reason is a binary clause (the other literal).
        BINARY = 2;
        POISONED = 4;
        REMOVABLE = 8;
        SHRINKABLE = 16;
    }
}

flag_set! {
    /// Flags of a variable used by simplification.
    VarFlags {
        /// Removed by elimination or substitution.
        ELIMINATED = 1;
        /// Candidate for variable elimination.
        ELIMINATE = 2;
        /// Candidate for subsumption.
        SUBSUME = 4;
        /// Already used as root of a sweeping environment.
        SWEPT = 8;
        /// Variable of a current assumption (must not be eliminated).
        FROZEN = 16;
    }
}
