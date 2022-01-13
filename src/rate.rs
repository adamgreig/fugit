use crate::helpers::{self, Helpers};
use crate::Duration;
use core::cmp::Ordering;
use core::convert;
use core::ops;

/// Represents a duration of time.
///
/// The generic `T` can either be `u32` or `u64`, and the const generics represent the ratio of the
/// ticks contained within the duration: `duration in seconds = NOM / DENOM * ticks`
#[derive(Clone, Copy, Debug)]
pub struct Rate<T, const NOM: u32, const DENOM: u32> {
    ticks: T,
}

macro_rules! impl_duration_for_integer {
    ($i:ty) => {
        impl<const NOM: u32, const DENOM: u32> Rate<$i, NOM, DENOM> {
            /// Create a `Rate` from a ticks value.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let _d = Rate::<", stringify!($i), ", 1, 1_000>::from_ticks(1);")]
            /// ```
            #[inline]
            pub const fn from_ticks(ticks: $i) -> Self {
                helpers::greater_than_0::<NOM>();
                helpers::greater_than_0::<DENOM>();

                Rate { ticks }
            }

            /// Extract the ticks from a `Rate`.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let d = Rate::<", stringify!($i), ", 1, 1_000>::from_ticks(234);")]
            ///
            /// assert_eq!(d.ticks(), 234);
            /// ```
            #[inline]
            pub const fn ticks(&self) -> $i {
                self.ticks
            }

            /// Add two durations while checking for overflow.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let d1 = Rate::<", stringify!($i), ", 1, 1_000>::from_ticks(1);")]
            #[doc = concat!("let d2 = Rate::<", stringify!($i), ", 1, 1_000>::from_ticks(2);")]
            #[doc = concat!("let d3 = Rate::<", stringify!($i), ", 1, 1_000>::from_ticks(", stringify!($i), "::MAX);")]
            ///
            /// assert_eq!(d1.checked_add(d2).unwrap().ticks(), 3);
            /// assert_eq!(d1.checked_add(d3), None);
            /// ```
            pub const fn checked_add<const O_NOM: u32, const O_DENOM: u32>(
                self,
                other: Rate<$i, O_NOM, O_DENOM>,
            ) -> Option<Self> {
                if Helpers::<NOM, DENOM, O_NOM, O_DENOM>::SAME_BASE {
                    if let Some(ticks) = self.ticks.checked_add(other.ticks) {
                        Some(Rate::<$i, NOM, DENOM>::from_ticks(ticks))
                    } else {
                        None
                    }
                } else {
                    if let Some(lh) = other
                        .ticks
                        .checked_mul(Helpers::<NOM, DENOM, O_NOM, O_DENOM>::LD_TIMES_RN as $i)
                    {
                        let ticks = lh / Helpers::<NOM, DENOM, O_NOM, O_DENOM>::RD_TIMES_LN as $i;

                        if let Some(ticks) = self.ticks.checked_add(ticks) {
                            Some(Rate::<$i, NOM, DENOM>::from_ticks(ticks))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }
            }

            /// Subtract two durations while checking for overflow.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let d1 = Rate::<", stringify!($i), ", 1, 1_000>::from_ticks(1);")]
            #[doc = concat!("let d2 = Rate::<", stringify!($i), ", 1, 1_000>::from_ticks(2);")]
            #[doc = concat!("let d3 = Rate::<", stringify!($i), ", 1, 1_000>::from_ticks(", stringify!($i), "::MAX);")]
            ///
            /// assert_eq!(d2.checked_sub(d1).unwrap().ticks(), 1);
            /// assert_eq!(d1.checked_sub(d3), None);
            /// ```
            pub const fn checked_sub<const O_NOM: u32, const O_DENOM: u32>(
                self,
                other: Rate<$i, O_NOM, O_DENOM>,
            ) -> Option<Self> {
                if Helpers::<NOM, DENOM, O_NOM, O_DENOM>::SAME_BASE {
                    if let Some(ticks) = self.ticks.checked_sub(other.ticks) {
                        Some(Rate::<$i, NOM, DENOM>::from_ticks(ticks))
                    } else {
                        None
                    }
                } else {
                    if let Some(lh) = other
                        .ticks
                        .checked_mul(Helpers::<NOM, DENOM, O_NOM, O_DENOM>::LD_TIMES_RN as $i)
                    {
                        let ticks = lh / Helpers::<NOM, DENOM, O_NOM, O_DENOM>::RD_TIMES_LN as $i;

                        if let Some(ticks) = self.ticks.checked_sub(ticks) {
                            Some(Rate::<$i, NOM, DENOM>::from_ticks(ticks))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }
            }

            #[doc = concat!("Const `cmp` for ", stringify!($i))]
            #[inline(always)]
            const fn _const_cmp(a: $i, b: $i) -> Ordering {
                if a < b {
                    Ordering::Less
                } else if a > b {
                    Ordering::Greater
                } else {
                    Ordering::Equal
                }
            }

            /// Const partial comparison.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let d1 = Rate::<", stringify!($i), ", 1, 1_00>::from_ticks(1);")]
            #[doc = concat!("let d2 = Rate::<", stringify!($i), ", 1, 1_000>::from_ticks(1);")]
            ///
            /// assert_eq!(d1.const_partial_cmp(d2), Some(core::cmp::Ordering::Greater));
            /// ```
            #[inline]
            pub const fn const_partial_cmp<const R_NOM: u32, const R_DENOM: u32>(
                self,
                other: Rate<$i, R_NOM, R_DENOM>
            ) -> Option<Ordering> {
                //
                // We want to check:
                //
                // n_lh / d_lh * lh_ticks {cmp} n_rh / d_rh * rh_ticks
                //
                // simplify to
                //
                // n_lh * d_rh * lh_ticks {cmp} n_rh * d_lh * rh_ticks
                //
                // find gdc(n_lh * d_rh, n_rh * d_lh) and use that to make the constants minimal (done
                // with the `helpers::Helpers` struct)
                //
                // then perform the comparison in a comparable basis
                //

                if Helpers::<NOM, DENOM, R_NOM, R_DENOM>::SAME_BASE {
                    // If we are in the same base, comparison in trivial
                    Some(Self::_const_cmp(self.ticks, other.ticks))
                } else {
                    let lh = self
                        .ticks
                        .checked_mul(Helpers::<NOM, DENOM, R_NOM, R_DENOM>::RD_TIMES_LN as $i);
                    let rh = other
                        .ticks
                        .checked_mul(Helpers::<NOM, DENOM, R_NOM, R_DENOM>::LD_TIMES_RN as $i);

                    if let (Some(lh), Some(rh)) = (lh, rh) {
                        Some(Self::_const_cmp(lh, rh))
                    } else {
                        None
                    }
                }
            }

            /// Const equality check.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let d1 = Rate::<", stringify!($i), ", 1, 1_00>::from_ticks(1);")]
            #[doc = concat!("let d2 = Rate::<", stringify!($i), ", 1, 1_000>::from_ticks(10);")]
            ///
            /// assert!(d1.const_eq(d2));
            /// ```
            #[inline]
            pub const fn const_eq<const R_NOM: u32, const R_DENOM: u32>(
                self,
                other: Rate<$i, R_NOM, R_DENOM>
            ) -> bool {
                if Helpers::<NOM, DENOM, R_NOM, R_DENOM>::SAME_BASE {
                    // If we are in the same base, comparison in trivial
                    self.ticks == other.ticks
                } else {
                    let lh = self
                        .ticks
                        .checked_mul(Helpers::<NOM, DENOM, R_NOM, R_DENOM>::RD_TIMES_LN as $i);
                    let rh = other
                        .ticks
                        .checked_mul(Helpers::<NOM, DENOM, R_NOM, R_DENOM>::LD_TIMES_RN as $i);

                    if let (Some(lh), Some(rh)) = (lh, rh) {
                        lh == rh
                    } else {
                        false
                    }
                }
            }

            /// Const try into, checking for overflow.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let d1 = Rate::<", stringify!($i), ", 1, 1_00>::from_ticks(1);")]
            #[doc = concat!("let d2: Option<Rate::<", stringify!($i), ", 1, 1_000>> = d1.const_try_into();")]
            ///
            /// assert_eq!(d2.unwrap().ticks(), 10);
            /// ```
            pub const fn const_try_into<const O_NOM: u32, const O_DENOM: u32>(
                self,
            ) -> Option<Rate<$i, O_NOM, O_DENOM>> {
                if Helpers::<NOM, DENOM, O_NOM, O_DENOM>::SAME_BASE {
                    Some(Rate::<$i, O_NOM, O_DENOM>::from_ticks(self.ticks))
                } else {
                    if let Some(lh) = (self.ticks as u64)
                        .checked_mul(Helpers::<NOM, DENOM, O_NOM, O_DENOM>::RD_TIMES_LN as u64)
                    {
                        let ticks = lh / Helpers::<NOM, DENOM, O_NOM, O_DENOM>::LD_TIMES_RN as u64;

                        if ticks <= <$i>::MAX as u64 {
                            Some(Rate::<$i, O_NOM, O_DENOM>::from_ticks(ticks as $i))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }
            }

            /// Const try into duration, checking for divide-by-zero.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let d1 = Rate::<", stringify!($i), ", 1, 1_00>::from_ticks(1);")]
            #[doc = concat!("let d2: Option<Rate::<", stringify!($i), ", 1, 1_000>> = d1.const_try_into();")]
            ///
            /// assert_eq!(d2.unwrap().ticks(), 10);
            /// ```
            pub const fn try_into_duration<const O_NOM: u32, const O_DENOM: u32>(
                self,
            ) -> Option<Duration<$i, O_NOM, O_DENOM>> {
                if self.ticks > 0 {
                    Some(Duration::<$i, O_NOM, O_DENOM>::from_ticks(
                        Helpers::<NOM, DENOM, O_NOM, O_DENOM>::RATE_TO_DURATION_NUMERATOR as $i
                        / self.ticks
                    ))
                } else {
                    None
                }
            }

            /// Convert between bases for a duration.
            ///
            /// Unfortunately not a `From` impl due to collision with the std lib.
            ///
            /// ```
            /// # use fugit::*;
            #[doc = concat!("let d1 = Rate::<", stringify!($i), ", 1, 100>::from_ticks(1);")]
            #[doc = concat!("let d2: Rate::<", stringify!($i), ", 1, 1_000> = d1.convert();")]
            ///
            /// assert_eq!(d2.ticks(), 10);
            /// ```
            /// Can be used in const contexts. Compilation will fail if the conversion causes overflow
            /// ```compile_fail
            /// # use fugit::*;
            #[doc = concat!("const TICKS: ", stringify!($i), "= ", stringify!($i), "::MAX - 10;")]
            #[doc = concat!("const D1: Rate::<", stringify!($i), ", 1, 100> = Rate::<", stringify!($i), ", 1, 100>::from_ticks(TICKS);")]
            /// // Fails conversion due to tick overflow
            #[doc = concat!("const D2: Rate::<", stringify!($i), ", 1, 200> = D1.convert();")]
            pub const fn convert<const O_NOM: u32, const O_DENOM: u32>(
                self,
            ) -> Rate<$i, O_NOM, O_DENOM> {
                if let Some(v) = self.const_try_into() {
                    v
                } else {
                    panic!("Convert failed!");
                }
            }

            /// Convert from rate to duration.
            pub const fn into_duration<const O_NOM: u32, const O_DENOM: u32>(
                self,
            ) -> Duration<$i, O_NOM, O_DENOM> {
                if let Some(v) = self.try_into_duration() {
                    v
                } else {
                    panic!("Into duration failed, divide-by-zero!");
                }
            }

            /// Shorthand for creating a duration which represents hertz.
            #[inline]
            pub const fn hz(val: $i) -> Rate<$i, NOM, DENOM> {
                Rate::<$i, NOM, DENOM>::from_ticks(
                    (Helpers::<1, 1, NOM, DENOM>::RD_TIMES_LN as $i * val)
                        / Helpers::<1, 1, NOM, DENOM>::LD_TIMES_RN as $i,
                )
            }

            /// Shorthand for creating a duration which represents kilohertz.
            #[inline]
            pub const fn khz(val: $i) -> Rate<$i, NOM, DENOM> {
                Rate::<$i, NOM, DENOM>::from_ticks(
                    (Helpers::<1_000, 1, NOM, DENOM>::RD_TIMES_LN as $i * val)
                        / Helpers::<1_000, 1, NOM, DENOM>::LD_TIMES_RN as $i,
                )
            }

            /// Shorthand for creating a duration which represents megahertz.
            #[inline]
            pub const fn mhz(val: $i) -> Rate<$i, NOM, DENOM> {
                Rate::<$i, NOM, DENOM>::from_ticks(
                    (Helpers::<1_000_000, 1, NOM, DENOM>::RD_TIMES_LN as $i * val)
                        / Helpers::<1_000_000, 1, NOM, DENOM>::LD_TIMES_RN as $i,
                )
            }
        }

        impl<const L_NOM: u32, const L_DENOM: u32, const R_NOM: u32, const R_DENOM: u32>
            PartialOrd<Rate<$i, R_NOM, R_DENOM>> for Rate<$i, L_NOM, L_DENOM>
        {
            #[inline]
            fn partial_cmp(&self, other: &Rate<$i, R_NOM, R_DENOM>) -> Option<Ordering> {
                self.const_partial_cmp(*other)
            }
        }

        impl<const NOM: u32, const DENOM: u32> Ord for Rate<$i, NOM, DENOM> {
            #[inline]
            fn cmp(&self, other: &Self) -> Ordering {
                Self::_const_cmp(self.ticks, other.ticks)
            }
        }

        impl<const L_NOM: u32, const L_DENOM: u32, const R_NOM: u32, const R_DENOM: u32>
            PartialEq<Rate<$i, R_NOM, R_DENOM>> for Rate<$i, L_NOM, L_DENOM>
        {
            #[inline]
            fn eq(&self, other: &Rate<$i, R_NOM, R_DENOM>) -> bool {
                self.const_eq(*other)
            }
        }

        impl<const NOM: u32, const DENOM: u32> Eq for Rate<$i, NOM, DENOM> {}

        // Rate - Rate = Rate (only same base until const_generics_defaults is
        // stabilized)
        impl<const NOM: u32, const DENOM: u32> ops::Sub<Rate<$i, NOM, DENOM>>
            for Rate<$i, NOM, DENOM>
        {
            type Output = Rate<$i, NOM, DENOM>;

            #[inline]
            fn sub(self, other: Rate<$i, NOM, DENOM>) -> Self::Output {
                if let Some(v) = self.checked_sub(other) {
                    v
                } else {
                    panic!("Sub failed!");
                }
            }
        }

        // Rate + Rate = Rate (only same base until const_generics_defaults is
        // stabilized)
        impl<const NOM: u32, const DENOM: u32> ops::Add<Rate<$i, NOM, DENOM>>
            for Rate<$i, NOM, DENOM>
        {
            type Output = Rate<$i, NOM, DENOM>;

            #[inline]
            fn add(self, other: Rate<$i, NOM, DENOM>) -> Self::Output {
                if let Some(v) = self.checked_add(other) {
                    v
                } else {
                    panic!("Add failed!");
                }
            }
        }

        // integer * Rate = Rate
        impl<const NOM: u32, const DENOM: u32> ops::Mul<Rate<$i, NOM, DENOM>> for u32 {
            type Output = Rate<$i, NOM, DENOM>;

            #[inline]
            fn mul(self, mut other: Rate<$i, NOM, DENOM>) -> Self::Output {
                other.ticks *= self as $i;
                other
            }
        }

        // Rate * integer = Rate
        impl<const NOM: u32, const DENOM: u32> ops::Mul<u32> for Rate<$i, NOM, DENOM> {
            type Output = Rate<$i, NOM, DENOM>;

            #[inline]
            fn mul(mut self, other: u32) -> Self::Output {
                self.ticks *= other as $i;
                self
            }
        }

        // Rate / integer = Rate
        impl<const NOM: u32, const DENOM: u32> ops::Div<u32> for Rate<$i, NOM, DENOM> {
            type Output = Rate<$i, NOM, DENOM>;

            #[inline]
            fn div(mut self, other: u32) -> Self::Output {
                self.ticks /= other as $i;
                self
            }
        }

        #[cfg(feature = "defmt")]
        impl<const NOM: u32, const DENOM: u32> defmt::Format for Rate<$i, NOM, DENOM>
        {
            fn format(&self, f: defmt::Formatter) {
                if NOM == 1 && DENOM == 1 {
                    defmt::write!(f, "{} Hz", self.ticks)
                } else if NOM == 1_000 && DENOM == 1 {
                    defmt::write!(f, "{} kHz", self.ticks)
                } else if NOM == 1_000_000 && DENOM == 1 {
                    defmt::write!(f, "{} MHz", self.ticks)
                } else if NOM == 1_000_000_000 && DENOM == 1 {
                    defmt::write!(f, "{} GHz", self.ticks)
                } else {
                    defmt::write!(f, "{} ticks @ ({}/{})", self.ticks, NOM, DENOM)
                }
            }
        }

        impl<const NOM: u32, const DENOM: u32> core::fmt::Display for Rate<$i, NOM, DENOM> {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                if NOM == 1 && DENOM == 1 {
                    write!(f, "{} Hz", self.ticks)
                } else if NOM == 1_000 && DENOM == 1 {
                    write!(f, "{} kHz", self.ticks)
                } else if NOM == 1_000_000 && DENOM == 1 {
                    write!(f, "{} MHz", self.ticks)
                } else if NOM == 1_000_000_000 && DENOM == 1 {
                    write!(f, "{} GHz", self.ticks)
                } else {
                    write!(f, "{} ticks @ ({}/{})", self.ticks, NOM, DENOM)
                }
            }
        }
    };
}

impl_duration_for_integer!(u32);
impl_duration_for_integer!(u64);

//
// Operations between u32 and u64 Rate
//

impl<const NOM: u32, const DENOM: u32> From<Rate<u32, NOM, DENOM>> for Rate<u64, NOM, DENOM> {
    #[inline]
    fn from(val: Rate<u32, NOM, DENOM>) -> Rate<u64, NOM, DENOM> {
        Rate::<u64, NOM, DENOM>::from_ticks(val.ticks() as u64)
    }
}

impl<const NOM: u32, const DENOM: u32> convert::TryFrom<Rate<u64, NOM, DENOM>>
    for Rate<u32, NOM, DENOM>
{
    type Error = ();

    #[inline]
    fn try_from(val: Rate<u64, NOM, DENOM>) -> Result<Rate<u32, NOM, DENOM>, ()> {
        Ok(Rate::<u32, NOM, DENOM>::from_ticks(
            val.ticks().try_into().map_err(|_| ())?,
        ))
    }
}

// Rate - Rate = Rate (to make shorthands work, until const_generics_defaults is
// stabilized)
impl<const NOM: u32, const DENOM: u32> ops::Sub<Rate<u32, NOM, DENOM>> for Rate<u64, NOM, DENOM> {
    type Output = Rate<u64, NOM, DENOM>;

    #[inline]
    fn sub(self, other: Rate<u32, NOM, DENOM>) -> Self::Output {
        if let Some(v) = self.checked_sub(Rate::<u64, NOM, DENOM>::from_ticks(other.ticks() as u64))
        {
            v
        } else {
            panic!("Sub failed!");
        }
    }
}

// Rate + Rate = Rate (to make shorthands work, until const_generics_defaults is
// stabilized)
impl<const NOM: u32, const DENOM: u32> ops::Add<Rate<u32, NOM, DENOM>> for Rate<u64, NOM, DENOM> {
    type Output = Rate<u64, NOM, DENOM>;

    #[inline]
    fn add(self, other: Rate<u32, NOM, DENOM>) -> Self::Output {
        if let Some(v) = self.checked_add(Rate::<u64, NOM, DENOM>::from_ticks(other.ticks() as u64))
        {
            v
        } else {
            panic!("Add failed!");
        }
    }
}

impl<const L_NOM: u32, const L_DENOM: u32, const R_NOM: u32, const R_DENOM: u32>
    PartialOrd<Rate<u32, R_NOM, R_DENOM>> for Rate<u64, L_NOM, L_DENOM>
{
    #[inline]
    fn partial_cmp(&self, other: &Rate<u32, R_NOM, R_DENOM>) -> Option<Ordering> {
        self.partial_cmp(&Rate::<u64, R_NOM, R_DENOM>::from_ticks(
            other.ticks() as u64
        ))
    }
}

impl<const L_NOM: u32, const L_DENOM: u32, const R_NOM: u32, const R_DENOM: u32>
    PartialEq<Rate<u32, R_NOM, R_DENOM>> for Rate<u64, L_NOM, L_DENOM>
{
    #[inline]
    fn eq(&self, other: &Rate<u32, R_NOM, R_DENOM>) -> bool {
        self.eq(&Rate::<u64, R_NOM, R_DENOM>::from_ticks(
            other.ticks() as u64
        ))
    }
}

impl<const L_NOM: u32, const L_DENOM: u32, const R_NOM: u32, const R_DENOM: u32>
    PartialOrd<Rate<u64, R_NOM, R_DENOM>> for Rate<u32, L_NOM, L_DENOM>
{
    #[inline]
    fn partial_cmp(&self, other: &Rate<u64, R_NOM, R_DENOM>) -> Option<Ordering> {
        Rate::<u64, L_NOM, L_DENOM>::from_ticks(self.ticks as u64).partial_cmp(other)
    }
}

impl<const L_NOM: u32, const L_DENOM: u32, const R_NOM: u32, const R_DENOM: u32>
    PartialEq<Rate<u64, R_NOM, R_DENOM>> for Rate<u32, L_NOM, L_DENOM>
{
    #[inline]
    fn eq(&self, other: &Rate<u64, R_NOM, R_DENOM>) -> bool {
        Rate::<u64, L_NOM, L_DENOM>::from_ticks(self.ticks as u64).eq(other)
    }
}

/// Extension trait for simple short-hands for u32 Rate
pub trait ExtU32 {
    /// Shorthand for creating a duration which represents hertz.
    fn hz<const NOM: u32, const DENOM: u32>(self) -> Rate<u32, NOM, DENOM>;

    /// Shorthand for creating a duration which represents kilohertz.
    fn khz<const NOM: u32, const DENOM: u32>(self) -> Rate<u32, NOM, DENOM>;

    /// Shorthand for creating a duration which represents megahertz.
    fn mhz<const NOM: u32, const DENOM: u32>(self) -> Rate<u32, NOM, DENOM>;
}

impl ExtU32 for u32 {
    #[inline]
    fn hz<const NOM: u32, const DENOM: u32>(self) -> Rate<u32, NOM, DENOM> {
        Rate::<u32, NOM, DENOM>::hz(self)
    }

    #[inline]
    fn khz<const NOM: u32, const DENOM: u32>(self) -> Rate<u32, NOM, DENOM> {
        Rate::<u32, NOM, DENOM>::khz(self)
    }

    #[inline]
    fn mhz<const NOM: u32, const DENOM: u32>(self) -> Rate<u32, NOM, DENOM> {
        Rate::<u32, NOM, DENOM>::mhz(self)
    }
}

/// Extension trait for simple short-hands for u64 Rate
pub trait ExtU64 {
    /// Shorthand for creating a duration which represents hertz.
    fn hz<const NOM: u32, const DENOM: u32>(self) -> Rate<u64, NOM, DENOM>;

    /// Shorthand for creating a duration which represents kilohertz.
    fn khz<const NOM: u32, const DENOM: u32>(self) -> Rate<u64, NOM, DENOM>;

    /// Shorthand for creating a duration which represents megahertz.
    fn mhz<const NOM: u32, const DENOM: u32>(self) -> Rate<u64, NOM, DENOM>;
}

impl ExtU64 for u64 {
    #[inline]
    fn hz<const NOM: u32, const DENOM: u32>(self) -> Rate<u64, NOM, DENOM> {
        Rate::<u64, NOM, DENOM>::hz(self)
    }

    #[inline]
    fn khz<const NOM: u32, const DENOM: u32>(self) -> Rate<u64, NOM, DENOM> {
        Rate::<u64, NOM, DENOM>::khz(self)
    }

    #[inline]
    fn mhz<const NOM: u32, const DENOM: u32>(self) -> Rate<u64, NOM, DENOM> {
        Rate::<u64, NOM, DENOM>::mhz(self)
    }
}
