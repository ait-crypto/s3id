use std::{iter::Sum, ops::Mul};

pub use crate::bls381_helpers::Scalar;
use ark_ff::{Field, One};

pub type Lagrange = GenericLagrange<Scalar>;

/// implementation of the Lagrange base polynomial
fn ell_j(x: Scalar, xs: &[Scalar], j: usize) -> Scalar {
    debug_assert!(j < xs.len());

    let xj = xs[j];
    let (num, denom) =
        xs.iter()
            .enumerate()
            .fold((Scalar::one(), Scalar::one()), |(num, denom), (m, xm)| {
                if m == j {
                    (num, denom)
                } else {
                    (num * (x - xm), denom * (xj - xm))
                }
            });
    // SAFETY: denom is always != 0
    num * denom.inverse().unwrap()
}

/// implementation of the Lagrange base polynomial for x = 0
fn ell_j_0(xs: &[Scalar], j: usize) -> Scalar {
    debug_assert!(j < xs.len());

    let xj = xs[j];
    let (num, denom) =
        xs.iter()
            .enumerate()
            .fold((Scalar::one(), Scalar::one()), |(num, denom), (m, xm)| {
                if m == j {
                    (num, denom)
                } else {
                    (num * xm, denom * (*xm - xj))
                }
            });
    // SAFETY: denom is always != 0
    num * denom.inverse().unwrap()
}

#[derive(Debug)]
pub struct GenericLagrange<T> {
    xs: Vec<T>,
    evaluated_ell_j_0: Vec<T>,
}

impl GenericLagrange<Scalar> {
    pub fn new(points: &[Scalar]) -> Self {
        Self {
            xs: points.into(),
            evaluated_ell_j_0: (0..points.len()).map(|j| ell_j_0(points, j)).collect(),
        }
    }

    pub fn eval_j(&self, x: Scalar, j: usize) -> Scalar {
        ell_j(x, self.xs.as_ref(), j)
    }

    pub fn eval<G>(&self, x: Scalar, ys: &[G]) -> G
    where
        G: Sized,
        // Self: Add<Output = Self> + for<'a> Add<&'a Self, Output = Self>,
        // for<'a> &'a Self: Add<&'a Self>,
        // Self: Mul<T, Output = Self> + for<'a> Mul<&'a T, Output = Self>,
        for<'a> &'a G: Mul<Scalar, Output = G>,
        G: Sum<G>,
    {
        debug_assert_eq!(ys.len(), self.xs.len());

        ys.iter()
            .enumerate()
            .map(|(j, y)| y * self.eval_j(x, j))
            .sum()
    }

    pub fn eval_0<G>(&self, ys: &[G]) -> G
    where
        G: Sized,
        // Self: Add<Output = Self> + for<'a> Add<&'a Self, Output = Self>,
        // for<'a> &'a Self: Add<&'a Self>,
        // Self: Mul<T, Output = Self> + for<'a> Mul<&'a T, Output = Self>,
        for<'a> &'a G: Mul<Scalar, Output = G>,
        G: Sum<G>,
    {
        debug_assert_eq!(ys.len(), self.xs.len());

        ys.iter()
            .enumerate()
            .map(|(j, y)| y * self.eval_j_0(j))
            .sum()
    }

    pub fn eval_j_0(&self, j: usize) -> Scalar {
        self.evaluated_ell_j_0[j]
    }

    pub fn update_point(&mut self, k: usize, new_value: Scalar) {
        if self.xs[k] == new_value {
            return;
        }

        for j in 0..self.xs.len() {
            if k == j {
                continue;
            }

            let num = (self.xs[j] - self.xs[k]) * new_value;
            let denom = self.xs[k] * (self.xs[j] - new_value);

            self.evaluated_ell_j_0[j] *= num * denom.inverse().unwrap();
        }

        self.xs[k] = new_value;
        self.evaluated_ell_j_0[k] = ell_j_0(&self.xs, k);
    }
}

/*
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
}
*/
