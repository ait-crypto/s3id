use bls12_381::Scalar;

pub struct Lagrange {
    xs: Vec<Scalar>,
    denominators: Vec<Scalar>,
}

impl Lagrange {
    pub fn new(points: &[Scalar]) -> Lagrange {
        Lagrange {
            xs: points.into(),
            denominators: points
                .iter()
                .enumerate()
                .map(|(j, xj)| {
                    points
                        .iter()
                        .enumerate()
                        .fold(Scalar::one(), |product, (idx, point)| {
                            if idx == j {
                                product
                            } else {
                                product * (xj - point)
                            }
                        })
                        .invert()
                        .unwrap()
                })
                .collect(),
        }
    }

    pub fn new_with_base_points(n: usize) -> Lagrange {
        let mut base = Scalar::zero();
        Self::new(
            &(0..n)
                .map(|_| {
                    base += Scalar::one();
                    base
                })
                .collect::<Vec<_>>(),
        )
    }

    pub fn eval(&self, x: Scalar, j: usize) -> Scalar {
        debug_assert!(j < self.denominators.len());

        self.xs
            .iter()
            .enumerate()
            .fold(self.denominators[j], |product, (idx, point)| {
                if idx == j {
                    product
                } else {
                    product * (x - point)
                }
            })
    }

    pub fn eval_0(&self, j: usize) -> Scalar {
        debug_assert!(j < self.denominators.len());

        self.xs
            .iter()
            .enumerate()
            .fold(self.denominators[j], |product, (idx, point)| {
                if idx == j {
                    product
                } else {
                    -product * point
                }
            })
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn lagrange() {
        let xs = [Scalar::zero(), Scalar::one(), Scalar::one().double()];

        let lagrange = Lagrange::new(&xs);
        assert_eq!(lagrange.eval(xs[0], 0), Scalar::one());
        assert_eq!(lagrange.eval(xs[1], 0), Scalar::zero());
        assert_eq!(lagrange.eval(xs[2], 0), Scalar::zero());

        assert_eq!(lagrange.eval(xs[0], 1), Scalar::zero());
        assert_eq!(lagrange.eval(xs[1], 1), Scalar::one());
        assert_eq!(lagrange.eval(xs[2], 1), Scalar::zero());

        assert_eq!(lagrange.eval(xs[0], 2), Scalar::zero());
        assert_eq!(lagrange.eval(xs[1], 2), Scalar::zero());
        assert_eq!(lagrange.eval(xs[2], 2), Scalar::one());
    }

    #[test]
    fn lagrange_fixed() {
        const N: usize = 10;
        let lagrange = Lagrange::new_with_base_points(N);
        for k in 0..N {
            assert!(lagrange.eval_0(k) != Scalar::zero());
        }
    }
}
