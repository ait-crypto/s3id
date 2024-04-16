use bls12_381::{Bls12, G1Affine, G1Projective, G2Affine, G2Projective, Scalar};
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use group::{ff::Field, Group};
use pairing::Engine;

struct Nums {
    e: usize,
    g1_e: usize,
    g1_m: usize,
    g2_e: usize,
    g2_m: usize,
    r_m: usize,
    r_a: usize,
}

impl Nums {
    fn new(
        e: usize,
        g1_e: usize,
        g1_m: usize,
        g2_e: usize,
        g2_m: usize,
        r_m: usize,
        r_a: usize,
    ) -> Self {
        Nums {
            e,
            g1_e,
            g1_m,
            g2_e,
            g2_m,
            r_m,
            r_a,
        }
    }
}

fn internal_bench(c: &mut Criterion, name: &str, nums: Nums) {
    let (e, g1_e, g1_m, g2_e, g2_m, r_m, r_a) = (
        nums.e, nums.g1_e, nums.g1_m, nums.g2_e, nums.g2_m, nums.r_m, nums.r_a,
    );

    let mut rng = rand::thread_rng();

    let pairing_elements: Vec<(G1Affine, G2Affine)> = (0..e)
        .map(|_| {
            (
                G1Projective::random(&mut rng).into(),
                G2Projective::random(&mut rng).into(),
            )
        })
        .collect();

    let g1_elements_exp: Vec<_> = (0..g1_e)
        .map(|_| (G1Projective::random(&mut rng), Scalar::random(&mut rng)))
        .collect();

    let g1_elements_mul: Vec<_> = (0..g1_m).map(|_| G1Projective::random(&mut rng)).collect();

    let g2_elements_exp: Vec<_> = (0..g2_e)
        .map(|_| (G2Projective::random(&mut rng), Scalar::random(&mut rng)))
        .collect();

    let g2_elements_mul: Vec<_> = (0..g2_m).map(|_| G2Projective::random(&mut rng)).collect();

    let f_elements: Vec<_> = (0..r_m.max(r_a))
        .map(|_| Scalar::random(&mut rng))
        .collect();

    c.bench_function(
        &format!(
            "{} e={} G1={} | {} G2={} | {} R={} | {}",
            name, e, g1_e, g1_m, g2_e, g2_m, r_m, r_a
        ),
        |b| {
            b.iter(|| {
                for (p, q) in &pairing_elements {
                    black_box(Bls12::pairing(p, q));
                }
                for (p, e) in &g1_elements_exp {
                    black_box(p * e);
                }
                black_box(
                    g1_elements_mul
                        .iter()
                        .fold(G1Projective::identity(), |acc, x| acc + x),
                );
                for (p, e) in &g2_elements_exp {
                    black_box(p * e);
                }
                black_box(
                    g2_elements_mul
                        .iter()
                        .fold(G2Projective::identity(), |acc, x| acc + x),
                );
                black_box(
                    f_elements
                        .iter()
                        .take(r_m)
                        .fold(Scalar::one(), |acc, x| acc * x),
                );
                black_box(
                    f_elements
                        .iter()
                        .take(r_m)
                        .fold(Scalar::zero(), |acc, x| acc + x),
                );
            })
        },
    );
}

//  dedup issuer runtime: 4*tp - 4 P | E=(n - tp + 1)*t + 2*n + 2 M=(n - tp + 1)*t + 3*n + 2*tp - 2 G1 | E=n M=2*n + 2*tp - 2 G2 | M=0 A=0 r | E=0 M=0 G | M=0 A=0 q

fn compute_dedup_issuer_params(
    big_n: usize,
    tprime: usize,
    n: usize,
    t: usize,
    _ell: usize,
) -> Nums {
    assert!(t <= big_n);
    assert!(tprime <= n);
    Nums::new(
        4 * tprime - 4,
        (n - tprime + 1) * t + 2 * n + 2,
        (n - tprime + 1) * t + 3 * n + 2 * tprime - 2,
        n,
        2 * n + 2 * tprime - 2,
        0,
        0,
    )
}

//  dedup user runtime: 0 P | E=(2*tp + 1)*(tp - 1) + 2*t + 2*tp + 2 M=2*t*(tp - 1) + (t + 1)*tp + t + tp G1 | E=0 M=(t + 1)*tp G2 | M=1 A=1 r | E=0 M=0 G | M=0 A=0 q

fn compute_dedup_user_params(
    _big_n: usize,
    tprime: usize,
    n: usize,
    t: usize,
    _ell: usize,
) -> Nums {
    assert!(tprime <= n);
    Nums::new(
        0,
        (2 * tprime + 1) * (tprime - 1) + 2 * t + 2 * tprime + 2,
        2 * t * (tprime - 1) + (t + 1) * tprime + t + tprime,
        0,
        (t + 1) * tprime,
        1,
        1,
    )
}

//  microcred issuer runtime: 0 P | E=10 M=2 G1 | E=1 M=2 G2 | M=0 A=0 r | E=0 M=0 G | M=0 A=0 q

fn compute_microcred_issuer_params(
    _big_n: usize,
    _tprime: usize,
    _n: usize,
    _t: usize,
    ell: usize,
) -> Nums {
    Nums::new(0, 10, 2, 1, 2, 6 * ell, 6 * ell)
}

//  microcred user runtime: 0 P | E=11*L M=7*L + t + 1 G1 | E=0 M=t + 1 G2 | M=6*L A=6*L r | E=0 M=0 G | M=0 A=0 q

fn compute_microcred_user_params(
    _big_n: usize,
    _tprime: usize,
    _n: usize,
    t: usize,
    ell: usize,
) -> Nums {
    Nums::new(0, 11 * ell, 7 * ell + t + 1, 0, t + 1, 6 * ell, 6 * ell)
}

//  appcred runtime: 0 P | E=2*L + 5 M=2*L + 1 G1 | E=0 M=0 G2 | M=2*L + 5 A=2*L + 4 r | E=0 M=0 G | M=0 A=0 q

fn compute_appcred_params(_big_n: usize, _tprime: usize, _n: usize, _t: usize, ell: usize) -> Nums {
    Nums::new(0, 2 * ell + 5, 2 * ell + 1, 0, 0, 2 * ell + 5, 2 * ell + 4)
}

//  verify runtime: 2 P | E=L + 8 M=L + 3 G1 | E=0 M=0 G2 | M=0 A=0 r | E=0 M=0 G | M=0 A=0 q

fn compute_verifycred_params(
    _big_n: usize,
    _tprime: usize,
    _n: usize,
    _t: usize,
    ell: usize,
) -> Nums {
    Nums::new(2, ell + 8, ell + 3, 0, 0, 0, 0)
}

const BIG_N: usize = 50;
const N: usize = 128; // 128; // 40
const TPRIME: usize = N / 2 + 1;
const T: usize = BIG_N / 2 + 1;
const ELL: usize = 10;

fn dedup_issuer(c: &mut Criterion) {
    let params = compute_dedup_issuer_params(BIG_N, TPRIME, N, T, ELL);
    internal_bench(c, "Dedup I", params);
}

fn dedup_user(c: &mut Criterion) {
    let params = compute_dedup_user_params(BIG_N, TPRIME, N, T, ELL);
    internal_bench(c, "Dedup U", params);
}

fn microcred_issuer(c: &mut Criterion) {
    let params = compute_microcred_issuer_params(BIG_N, TPRIME, N, T, ELL);
    internal_bench(c, "MicroCred I", params);
}

fn microcred_user(c: &mut Criterion) {
    let params = compute_microcred_user_params(BIG_N, TPRIME, N, T, ELL);
    internal_bench(c, "MicroCred U", params);
}

fn app_cred(c: &mut Criterion) {
    let params = compute_appcred_params(BIG_N, TPRIME, N, T, ELL);
    internal_bench(c, "AppCred", params);
}

fn verify_cred(c: &mut Criterion) {
    let params = compute_verifycred_params(BIG_N, TPRIME, N, T, ELL);
    internal_bench(c, "VerifyCred", params);
}

criterion_group!(
    benches,
    dedup_issuer,
    dedup_user,
    microcred_issuer,
    microcred_user,
    app_cred,
    verify_cred
);
criterion_main!(benches);
