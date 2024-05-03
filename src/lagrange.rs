use std::{iter::Sum, ops::Mul};

use bls12_381::Scalar;
use group::ff::Field;

pub trait Groupish<T>
where
    T: Field,
    Self: Sized,
    // Self: Add<Output = Self> + for<'a> Add<&'a Self, Output = Self>,
    // for<'a> &'a Self: Add<&'a Self>,
    // Self: Mul<T, Output = Self> + for<'a> Mul<&'a T, Output = Self>,
    for<'a> &'a Self: Mul<T, Output = Self>,
    Self: Sum<Self>,
{
}

pub type Lagrange = GenericLagrange<Scalar>;

/// implementation of the Lagrange base polynomial
fn ell_j<T>(x: T, xs: &[T], j: usize) -> T
where
    T: Field,
{
    debug_assert!(j < xs.len());

    let xj = xs[j];
    let (num, denom) = xs
        .iter()
        .enumerate()
        .fold((T::ONE, T::ONE), |(num, denom), (m, xm)| {
            if m == j {
                (num, denom)
            } else {
                (num * (x - xm), denom * (xj - xm))
            }
        });
    // SAFETY: denom is always != 0
    num * denom.invert().unwrap()
}

/// implementation of the Lagrange base polynomial for x = 0
fn ell_j_0<T>(xs: &[T], j: usize) -> T
where
    T: Field,
{
    debug_assert!(j < xs.len());

    let xj = xs[j];
    let (num, denom) = xs
        .iter()
        .enumerate()
        .fold((T::ONE, T::ONE), |(num, denom), (m, xm)| {
            if m == j {
                (num, denom)
            } else {
                (-num * xm, denom * (xj - xm))
            }
        });
    // SAFETY: denom is always != 0
    num * denom.invert().unwrap()
}

#[derive(Debug)]
pub struct GenericLagrange<T> {
    xs: Vec<T>,
}

impl<T> GenericLagrange<T>
where
    T: Field + From<u64>,
{
    pub fn new(points: &[T]) -> Self {
        Self { xs: points.into() }
    }

    #[deprecated]
    pub fn new_with_base_points(n: usize) -> Self {
        Self::new(
            (0..n)
                .map(|i| T::from((i + 1) as u64))
                .collect::<Vec<_>>()
                .as_ref(),
        )
    }

    pub fn eval_j(&self, x: T, j: usize) -> T {
        ell_j(x, self.xs.as_ref(), j)
    }

    pub fn eval<G>(&self, x: T, ys: &[G]) -> G
    where
        G: Groupish<T>,
        for<'a> &'a G: Mul<T, Output = G>,
    {
        debug_assert_eq!(ys.len(), self.xs.len());

        ys.iter()
            .enumerate()
            .map(|(j, y)| y * self.eval_j(x, j))
            .sum()
    }

    pub fn eval_0<G>(&self, ys: &[G]) -> G
    where
        G: Groupish<T>,
        for<'a> &'a G: Mul<T, Output = G>,
    {
        debug_assert_eq!(ys.len(), self.xs.len());

        ys.iter()
            .enumerate()
            .map(|(j, y)| y * self.eval_j_0(j))
            .sum()
    }

    pub fn eval_j_0(&self, j: usize) -> T {
        ell_j_0(self.xs.as_ref(), j)
    }
}

#[cfg(test)]
mod test {
    use std::{
        iter::{Product, Sum},
        ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    };

    use num::Integer;
    use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

    use super::*;

    #[test]
    fn lagrange() {
        let xs = [Scalar::zero(), Scalar::one(), Scalar::one().double()];

        let lagrange = Lagrange::new(&xs);
        assert_eq!(lagrange.eval_j(xs[0], 0), Scalar::one());
        assert_eq!(lagrange.eval_j(xs[1], 0), Scalar::zero());
        assert_eq!(lagrange.eval_j(xs[2], 0), Scalar::zero());

        assert_eq!(lagrange.eval_j(xs[0], 1), Scalar::zero());
        assert_eq!(lagrange.eval_j(xs[1], 1), Scalar::one());
        assert_eq!(lagrange.eval_j(xs[2], 1), Scalar::zero());

        assert_eq!(lagrange.eval_j(xs[0], 2), Scalar::zero());
        assert_eq!(lagrange.eval_j(xs[1], 2), Scalar::zero());
        assert_eq!(lagrange.eval_j(xs[2], 2), Scalar::one());
    }

    #[test]
    fn lagrange_fixed() {
        const N: usize = 10;
        let lagrange = Lagrange::new_with_base_points(N);
        for k in 0..N {
            assert!(lagrange.eval_j_0(k) != Scalar::zero());
        }
    }

    #[derive(Copy, Clone, Debug, PartialEq, Eq, Default)]
    struct SmallScalar(u32);

    impl SmallScalar {
        const MOD: u32 = 17;

        fn mul(lhs: u32, rhs: u32) -> u32 {
            (lhs * rhs) % Self::MOD
        }

        fn add(lhs: u32, rhs: u32) -> u32 {
            (lhs + rhs) % Self::MOD
        }

        fn sub(lhs: u32, rhs: u32) -> u32 {
            (Self::MOD + lhs - rhs) % Self::MOD
        }
    }

    impl From<u32> for SmallScalar {
        fn from(value: u32) -> Self {
            Self(value % Self::MOD)
        }
    }

    impl Add for SmallScalar {
        type Output = SmallScalar;

        fn add(self, rhs: Self) -> Self::Output {
            Self(Self::add(self.0, rhs.0))
        }
    }

    impl Add<&SmallScalar> for SmallScalar {
        type Output = SmallScalar;

        fn add(self, rhs: &Self) -> Self::Output {
            Self(Self::add(self.0, rhs.0))
        }
    }

    impl AddAssign for SmallScalar {
        fn add_assign(&mut self, rhs: Self) {
            self.0 = Self::add(self.0, rhs.0)
        }
    }

    impl AddAssign<&SmallScalar> for SmallScalar {
        fn add_assign(&mut self, rhs: &Self) {
            self.0 = Self::add(self.0, rhs.0)
        }
    }

    impl Sub for SmallScalar {
        type Output = SmallScalar;

        fn sub(self, rhs: Self) -> Self::Output {
            Self(Self::sub(self.0, rhs.0))
        }
    }

    impl Sub<&SmallScalar> for SmallScalar {
        type Output = SmallScalar;

        fn sub(self, rhs: &Self) -> Self::Output {
            Self(Self::sub(self.0, rhs.0))
        }
    }

    impl SubAssign for SmallScalar {
        fn sub_assign(&mut self, rhs: Self) {
            self.0 = Self::sub(self.0, rhs.0)
        }
    }

    impl SubAssign<&SmallScalar> for SmallScalar {
        fn sub_assign(&mut self, rhs: &Self) {
            self.0 = Self::sub(self.0, rhs.0)
        }
    }

    impl Mul for SmallScalar {
        type Output = SmallScalar;

        fn mul(self, rhs: Self) -> Self::Output {
            Self(Self::mul(self.0, rhs.0))
        }
    }

    impl Mul<&SmallScalar> for SmallScalar {
        type Output = SmallScalar;

        fn mul(self, rhs: &Self) -> Self::Output {
            Self(Self::mul(self.0, rhs.0))
        }
    }

    impl Mul for &SmallScalar {
        type Output = SmallScalar;

        fn mul(self, rhs: Self) -> Self::Output {
            SmallScalar(SmallScalar::mul(self.0, rhs.0))
        }
    }

    impl Mul<SmallScalar> for &SmallScalar {
        type Output = SmallScalar;

        fn mul(self, rhs: SmallScalar) -> Self::Output {
            SmallScalar(SmallScalar::mul(self.0, rhs.0))
        }
    }

    impl MulAssign for SmallScalar {
        fn mul_assign(&mut self, rhs: Self) {
            self.0 = Self::mul(self.0, rhs.0)
        }
    }

    impl MulAssign<&SmallScalar> for SmallScalar {
        fn mul_assign(&mut self, rhs: &Self) {
            self.0 = Self::mul(self.0, rhs.0)
        }
    }

    impl Neg for SmallScalar {
        type Output = SmallScalar;

        fn neg(self) -> Self::Output {
            Self(Self::MOD - self.0)
        }
    }

    impl Sum<SmallScalar> for SmallScalar {
        fn sum<I: Iterator<Item = SmallScalar>>(iter: I) -> Self {
            iter.fold(Self::ZERO, |acc, v| acc + v)
        }
    }

    impl<'a> Sum<&'a SmallScalar> for SmallScalar {
        fn sum<I: Iterator<Item = &'a SmallScalar>>(iter: I) -> Self {
            iter.fold(Self::ZERO, |acc, v| acc + v)
        }
    }

    impl Product<SmallScalar> for SmallScalar {
        fn product<I: Iterator<Item = SmallScalar>>(iter: I) -> Self {
            iter.fold(Self::ONE, |acc, v| acc * v)
        }
    }

    impl<'a> Product<&'a SmallScalar> for SmallScalar {
        fn product<I: Iterator<Item = &'a SmallScalar>>(iter: I) -> Self {
            iter.fold(Self::ONE, |acc, v| acc * v)
        }
    }

    impl ConstantTimeEq for SmallScalar {
        fn ct_eq(&self, other: &Self) -> Choice {
            self.0.ct_eq(&other.0)
        }
    }

    impl ConditionallySelectable for SmallScalar {
        fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
            Self(u32::conditional_select(&a.0, &b.0, choice))
        }
    }

    impl From<u64> for SmallScalar {
        fn from(value: u64) -> Self {
            Self((value % (Self::MOD as u64)) as u32)
        }
    }

    impl Field for SmallScalar {
        const ZERO: Self = SmallScalar(0);

        const ONE: Self = SmallScalar(1);

        fn random(mut rng: impl rand::RngCore) -> Self {
            Self(rng.next_u32() % Self::MOD)
        }

        fn square(&self) -> Self {
            Self(Self::mul(self.0, self.0))
        }

        fn double(&self) -> Self {
            Self(Self::mul(self.0, 2))
        }

        fn invert(&self) -> CtOption<Self> {
            if self.0 == 0 {
                return CtOption::new(Self::ZERO, 0.into());
            }

            let mut inverse = (Self::MOD as i32).extended_gcd(&(self.0 as i32)).y;
            // FIXME
            while inverse < 0 {
                inverse += Self::MOD as i32;
            }
            CtOption::new(Self::from(inverse as u32), 1.into())
        }

        fn sqrt_ratio(_num: &Self, _div: &Self) -> (Choice, Self) {
            todo!()
        }
    }

    impl Groupish<SmallScalar> for SmallScalar {}

    #[test]
    fn small_lagrange() {
        // check polynomial x^2

        let xs = [SmallScalar(1), SmallScalar(2), SmallScalar(3)];
        let ys = [SmallScalar(1), SmallScalar(4), SmallScalar(9)];

        let lagrange = GenericLagrange::new(&xs);
        assert_eq!(lagrange.eval(SmallScalar(4), &ys), SmallScalar(16));

        let new_xs = [SmallScalar(4), SmallScalar(9), SmallScalar(10)];
        let new_ys = [
            lagrange.eval(new_xs[0], &ys),
            lagrange.eval(new_xs[1], &ys),
            lagrange.eval(new_xs[2], &ys),
        ];
        assert_eq!(new_ys, [SmallScalar(16), SmallScalar(13), SmallScalar(15)]);

        let lagrange = GenericLagrange::new(&new_xs);
        let check_ys = [
            lagrange.eval(xs[0], &new_ys),
            lagrange.eval(xs[1], &new_ys),
            lagrange.eval(xs[2], &new_ys),
        ];
        assert_eq!(ys, check_ys);
    }

    #[test]
    fn small_field() {
        assert_eq!(SmallScalar(1) - SmallScalar(4), SmallScalar(14));
        assert_eq!(SmallScalar(1).invert().unwrap(), SmallScalar(1));
        assert_eq!(
            SmallScalar(8).invert().unwrap() * SmallScalar(8),
            SmallScalar(1)
        );
    }
}
