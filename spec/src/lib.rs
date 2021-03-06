#![no_std]

pub use norost_ipc_spec_proc::*;

// const generics aren't quite powerful enough yet for our needs, so
// generate a bunch of common types for now instead.
macro_rules! num {
	{ $sty:ident $uty:ident [$n:expr] $fsraw:ident $tsraw:ident $furaw:ident $turaw:ident } => {};
	{
		$sty:ident $uty:ident [$n:expr] $fsraw:ident $tsraw:ident $furaw:ident $turaw:ident
		$s:ident $u:ident $($ns:ident $nu:ident)*
	} => {
		#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
		pub struct $s($sty);
		#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
		pub struct $u($uty);

		impl $s {
			pub const BITS: u32 = $n;
			pub const MASK: $sty = 1u128.wrapping_shl(Self::BITS).wrapping_sub(1) as _;

			#[inline]
			pub fn new(value: $sty) -> Self {
				assert!(value & !Self::MASK == 0, "value is too large");
				Self(value)
			}

			#[inline]
			pub fn get(&self) -> $sty {
				self.0
			}

			#[inline]
			pub fn from_raw(slice: &[u8], offset: usize) -> Self {
				Self($fsraw(slice, offset, Self::BITS))
			}

			#[inline]
			pub fn to_raw(&self, slice: &mut [u8], offset: usize) {
				$tsraw(slice, offset, Self::BITS, self.0)
			}
		}

		impl $u {
			pub const BITS: u32 = $s::BITS;
			pub const MASK: $uty = $s::MASK as _;

			#[inline]
			pub fn new(value: $uty) -> Self {
				assert!(value & !Self::MASK == 0, "value is too large");
				Self(value)
			}

			#[inline]
			pub fn get(&self) -> $uty {
				self.0
			}

			#[inline]
			pub fn from_raw(slice: &[u8], offset: usize) -> Self {
				Self($furaw(slice, offset, Self::BITS))
			}

			#[inline]
			pub fn to_raw(&self, slice: &mut [u8], offset: usize) {
				$turaw(slice, offset, Self::BITS, self.0)
			}
		}
		num! { $sty $uty [$n + 1] $fsraw $tsraw $furaw $turaw $($ns $nu)* }
	};
	(bool $name:ident) => {
		#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
		pub struct $name(bool);

		impl $name {
			pub const BITS: u32 = 1;
			pub const MASK: bool = true;

			#[inline]
			pub fn new(value: bool) -> Self {
				Self(value)
			}

			#[inline]
			pub fn get(&self) -> bool {
				self.0
			}

			#[inline]
			pub fn from_raw(slice: &[u8], offset: usize) -> Self {
				Self(slice[offset / 8] & (1 << offset % 8) != 0)
			}

			#[inline]
			pub fn to_raw(&self, slice: &mut [u8], offset: usize) {
				let mask = 1 << offset % 8;
				slice[offset / 8] &= !mask;
				slice[offset / 8] |= mask * u8::from(self.0);
			}
		}
	};
}

num!(bool S1);
num!(bool U1);

num! { i8 u8 [2] from_raw_i8 to_raw_i8 from_raw_u8 to_raw_u8
	S2 U2 S3 U3 S4 U4 S5 U5 S6 U6 S7 U7 S8 U8 }
num! {
    i16 u16 [9] from_raw_i16 to_raw_i16 from_raw_u16 to_raw_u16
    S9 U9 S10 U10 S11 U11 S12 U12 S13 U13 S14 U14 S15 U15 S16 U16
}
num! {
    i32 u32 [17] from_raw_i32 to_raw_i32 from_raw_u32 to_raw_u32
    S17 U17 S18 U18 S19 U19 S20 U20 S21 U21 S22 U22 S23 U23 S24 U24
    S25 U25 S26 U26 S27 U27 S28 U28 S29 U29 S30 U30 S31 U31 S32 U32
}
// [print(c + str(i), end=' ' if c == 'S' or i % 8 else '\n') for i in range(33,65) for c in 'SU']
num! {
    i64 u64 [33] from_raw_i64 to_raw_i64 from_raw_u64 to_raw_u64
    S33 U33 S34 U34 S35 U35 S36 U36 S37 U37 S38 U38 S39 U39 S40 U40
    S41 U41 S42 U42 S43 U43 S44 U44 S45 U45 S46 U46 S47 U47 S48 U48
    S49 U49 S50 U50 S51 U51 S52 U52 S53 U53 S54 U54 S55 U55 S56 U56
    S57 U57 S58 U58 S59 U59 S60 U60 S61 U61 S62 U62 S63 U63 S64 U64
}
// Ditto
num! {
    i128 u128 [65] from_raw_i128 to_raw_i128 from_raw_u128 to_raw_u128
    S65 U65 S66 U66 S67 U67 S68 U68 S69 U69 S70 U70 S71 U71 S72 U72
    S73 U73 S74 U74 S75 U75 S76 U76 S77 U77 S78 U78 S79 U79 S80 U80
    S81 U81 S82 U82 S83 U83 S84 U84 S85 U85 S86 U86 S87 U87 S88 U88
    S89 U89 S90 U90 S91 U91 S92 U92 S93 U93 S94 U94 S95 U95 S96 U96
    S97 U97 S98 U98 S99 U99 S100 U100 S101 U101 S102 U102 S103 U103 S104 U104
    S105 U105 S106 U106 S107 U107 S108 U108 S109 U109 S110 U110 S111 U111 S112 U112
    S113 U113 S114 U114 S115 U115 S116 U116 S117 U117 S118 U118 S119 U119 S120 U120
    // We don't support these ones yet.
    //S121 U121 S122 U122 S123 U123 S124 U124 S125 U125 S126 U126 S127 U127 S128 U128
}

// Carefully tuned to make LLVM generate optimal code with constants.
// Probably performs horribly in debug mode. Oh well.
#[inline]
fn from_raw_u128(slice: &[u8], offset: usize, bits: u32) -> u128 {
    assert!(
        bits <= 128 - 8,
        "more than 120 bits is not reliably supported"
    );
    let mask = (1 << bits) - 1;
    let bits = usize::try_from(bits).unwrap();
    let shift = offset % 8;

    let from = offset / 8;
    let to = (offset + bits - 1) / 8;

    let mut v = [0; 16];
	let to = to.max(slice.len() - 1).min(from + 15);
	v[..to - from + 1].copy_from_slice(&slice[from..=to]);
    let v = u128::from_le_bytes(v);

    (v >> shift & mask).try_into().unwrap()
}

// TODO this doesn't compile down to optimal assembly, though it probably makes
// more sense to perform optimizations inside the proc macro instead of getting
// LLVM to do what we want (which, from experience, is a very deep and unpleasant
// rabbit hole).
#[inline]
fn to_raw_u128(slice: &mut [u8], offset: usize, bits: u32, value: u128) {
    assert!(
        bits <= 128 - 8,
        "more than 120 bits is not reliably supported"
    );
    let mask = (1 << bits) - 1;
    let bits = usize::try_from(bits).unwrap();
    let shift = offset % 8;
	// debug_assert because the compiler can't reliably assume the value
	// actually fits inside the mask
	debug_assert_eq!(value & !mask, 0, "value doesn't fit inside mask");

    let from = offset / 8;
    let to = (offset + bits - 1) / 8;

	let to = to.max(slice.len() - 1).min(from + 15);
	let mut v = [0; 16];
	v[..to - from + 1].copy_from_slice(&slice[from..=to]);
    let mut v = u128::from_le_bytes(v);

	v &= !(mask << shift);
	// We don't mask here because it _shouldn't_ be necessary, though the
	// compiler cannot always safely assume that. Masking anyways leads
	// to poor assembly.
	v |= value << shift;
	slice[from..=to].copy_from_slice(&v.to_le_bytes()[..to - from + 1]);
}

#[inline]
fn from_raw_i128(slice: &[u8], offset: usize, bits: u32) -> i128 {
    let d = core::mem::size_of::<i128>() as u32 - bits;
    (from_raw_u128(slice, offset, bits) as i128) << d >> d
}

#[inline]
fn to_raw_i128(slice: &mut [u8], offset: usize, bits: u32, value: i128) {
	to_raw_u128(slice, offset, bits, value as u128)
}

macro_rules! raw {
    ($fsfn:ident $tsfn:ident $sty:ident | $fufn:ident $tufn:ident $uty:ident) => {
        #[inline]
        fn $fsfn(slice: &[u8], offset: usize, bits: u32) -> $sty {
            let d = core::mem::size_of::<$sty>() as u32 - bits;
            ($fufn(slice, offset, bits) as $sty) << d >> d
        }

        #[inline]
        fn $fufn(slice: &[u8], offset: usize, bits: u32) -> $uty {
            from_raw_u128(slice, offset, bits).try_into().unwrap()
        }

        #[inline]
        fn $tsfn(slice: &mut [u8], offset: usize, bits: u32, value: $sty) {
            $tufn(slice, offset, bits, value as $uty)
        }

        #[inline]
        fn $tufn(slice: &mut [u8], offset: usize, bits: u32, value: $uty) {
            to_raw_u128(slice, offset, bits, value as u128)
        }
    };
}

raw!(from_raw_i64 to_raw_i64 i64 | from_raw_u64 to_raw_u64 u64);
raw!(from_raw_i32 to_raw_i32 i32 | from_raw_u32 to_raw_u32 u32);
raw!(from_raw_i16 to_raw_i16 i16 | from_raw_u16 to_raw_u16 u16);
raw!(from_raw_i8 to_raw_i8 i8 | from_raw_u8 to_raw_u8 u8);

#[cfg(test)]
mod test {
	use super::*;

	#[test]
	fn convert_u7() {
		let mut a = [0];
		let v = U7::new(0x42);
		v.to_raw(&mut a, 0);
		assert_eq!(U7::from_raw(&a, 0), v);
		v.to_raw(&mut a, 1);
		assert_eq!(U7::from_raw(&a, 1), v);
		v.to_raw(&mut a, 0);
		assert_ne!(U7::from_raw(&a, 1), v);
		v.to_raw(&mut a, 1);
		assert_ne!(U7::from_raw(&a, 0), v);
	}

	#[test]
	#[should_panic]
	fn fail_u7_to_raw() {
		let mut a = [0];
		let v = U7::new(0);
		v.to_raw(&mut a, 2);
	}
}
