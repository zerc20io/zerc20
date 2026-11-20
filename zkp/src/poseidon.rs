//! circomlib-compatible Poseidon over BN254, natively and in-circuit.

use std::sync::LazyLock;

use ark_bn254::Fr;
use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar,
    poseidon::{PoseidonConfig, constraints::PoseidonSpongeVar, find_poseidon_ark_and_mds},
};
use ark_ff::{AdditiveGroup, Field, PrimeField};
use ark_r1cs_std::{GR1CSVar, fields::fp::FpVar};
use ark_relations::gr1cs::SynthesisError;

/// circomlib's `Poseidon(T - 1)`, of width `T`: the standard parameters, which the circuits take, and the same
/// permutation rearranged for native hashing, which `hash` runs.
///
/// The rearrangement is linear algebra over the standard permutation, so its output is circomlib's. A partial round's
/// S-box takes only the first element, so the rest of the state passes through it linearly:
/// - A partial round's constants `c` move back through the matrix before them, as `M⁻¹·c`: the first element is
///   added after the previous round's S-box, the rest join the previous round's constants. From the last partial
///   round back, the first partial round's land after the S-boxes of the last full round before them.
/// - A partial round's matrix factors as `[[a, vᵀ], [w, N]] = [[a, vᵀN⁻¹], [w, I]]·diag(1, N)`. `diag(1, N)` leaves
///   the first element alone, so it moves back past the S-box into the previous round's matrix, which factors the
///   same way. From the last partial round back, every partial round keeps a sparse matrix (`2T - 1`
///   multiplications rather than `T²`), and the dense rest joins the last full round before them.
pub struct Poseidon<const T: usize> {
    pub config: PoseidonConfig<Fr>,
    mds: [[Fr; T]; T],
    /// The round constants of the first half's full rounds before its last.
    first_ark: Vec<[Fr; T]>,
    /// The round constants of the first half's last round.
    first_last_ark: [Fr; T],
    /// The constants added after the S-boxes of the first half's last round.
    into_partial_ark: [Fr; T],
    /// The first half's last matrix, with the dense part of every partial round's.
    into_partial_mds: [[Fr; T]; T],
    partial: Vec<PartialRound<T>>,
    /// The round constants of the second half's full rounds.
    second_ark: Vec<[Fr; T]>,
}

/// `s[0] = s[0]⁵ + ark`, then the sparse matrix `[[row], [col, I]]` (`col[0]` unused).
struct PartialRound<const T: usize> {
    ark: Fr,
    row: [Fr; T],
    col: [Fr; T],
}

type Matrix = Vec<Vec<Fr>>;

fn mul(a: &Matrix, b: &Matrix) -> Matrix {
    let n = a.len();
    let entry = |i: usize, j: usize| (0..n).map(|k| a[i][k] * b[k][j]).sum();
    (0..n)
        .map(|i| (0..n).map(|j| entry(i, j)).collect())
        .collect()
}

/// Gauss-Jordan elimination; None for a singular matrix.
fn invert(m: &Matrix) -> Option<Matrix> {
    let n = m.len();
    let mut a: Matrix = (0..n)
        .map(|i| {
            let identity = (0..n).map(|j| if i == j { Fr::ONE } else { Fr::ZERO });
            m[i].iter().copied().chain(identity).collect()
        })
        .collect();
    for c in 0..n {
        let (pivot, inv) = (c..n).find_map(|r| Some((r, a[r][c].inverse()?)))?;
        a.swap(c, pivot);
        a[c].iter_mut().for_each(|x| *x *= inv);
        for r in (0..n).filter(|&r| r != c) {
            let f = a[r][c];
            let pivot_row = a[c].clone();
            a[r].iter_mut()
                .zip(pivot_row)
                .for_each(|(x, p)| *x -= f * p);
        }
    }
    Some(a.into_iter().map(|row| row[n..].to_vec()).collect())
}

fn array<const T: usize>(v: &[Fr]) -> Option<[Fr; T]> {
    v.try_into().ok()
}

fn square<const T: usize>(m: &Matrix) -> Option<[[Fr; T]; T]> {
    m.iter()
        .map(|row| array(row))
        .collect::<Option<Vec<_>>>()?
        .try_into()
        .ok()
}

impl<const T: usize> Poseidon<T> {
    /// circomlib's parameters: 8 full rounds and its partial round count for width `T`. The grain-LFSR generation with
    /// `skip_matrices = 0` reproduces circomlib's round constants and MDS matrix.
    #[expect(
        clippy::expect_used,
        reason = "circomlib's parameters are fixed: their matrices are T wide, and an MDS matrix and its lower-right \
                  blocks are invertible, so they always rearrange"
    )]
    fn circom(partial_rounds: usize) -> Self {
        let (ark, mds) = find_poseidon_ark_and_mds::<Fr>(
            Fr::MODULUS_BIT_SIZE as u64,
            T - 1,
            8,
            partial_rounds as u64,
            0,
        );
        let config = PoseidonConfig::new(8, partial_rounds, 5, mds, ark, T - 1, 1);
        Self::rearranged(config).expect("circomlib's parameters rearrange")
    }

    /// `config` with its permutation rearranged for native hashing; None unless its matrices are `T` wide and those
    /// it inverts are invertible.
    fn rearranged(config: PoseidonConfig<Fr>) -> Option<Self> {
        let (rf, rp) = (config.full_rounds / 2, config.partial_rounds);
        let mds = &config.mds;
        let mds_inv = invert(mds)?;
        let mut ark = config.ark.clone();
        let mut partial_ark = vec![Fr::ZERO; rp];
        let mut into_partial_ark = [Fr::ZERO; T];
        for r in (rf..rf + rp).rev() {
            let moved: Vec<Fr> = mds_inv
                .iter()
                .map(|row| row.iter().zip(&ark[r]).map(|(m, c)| *m * c).sum())
                .collect();
            if r == rf {
                into_partial_ark = array(&moved)?;
            } else {
                partial_ark[r - 1 - rf] = moved[0];
                (1..T).for_each(|k| ark[r - 1][k] += moved[k]);
            }
        }

        let mut m = mds.clone();
        let mut partial = (0..rp)
            .rev()
            .map(|p| {
                let n: Matrix = m[1..].iter().map(|row| row[1..].to_vec()).collect();
                let n_inv = invert(&n)?;
                let mut row = [m[0][0]; T];
                for j in 1..T {
                    row[j] = (1..T).map(|i| m[0][i] * n_inv[i - 1][j - 1]).sum();
                }
                let col = std::array::from_fn(|k| m[k][0]);
                let mut diag_n = vec![vec![Fr::ZERO; T]; T];
                diag_n[0][0] = Fr::ONE;
                (1..T).for_each(|i| diag_n[i][1..].copy_from_slice(&n[i - 1]));
                m = mul(&diag_n, mds);
                Some(PartialRound {
                    ark: partial_ark[p],
                    row,
                    col,
                })
            })
            .collect::<Option<Vec<_>>>()?;
        partial.reverse();

        let arks = |rounds: &[Vec<Fr>]| rounds.iter().map(|c| array(c)).collect::<Option<Vec<_>>>();
        let (first_last_ark, first_ark) = ark[..rf].split_last()?;
        Some(Poseidon {
            mds: square(mds)?,
            first_ark: arks(first_ark)?,
            first_last_ark: array(first_last_ark)?,
            into_partial_ark,
            into_partial_mds: square(&m)?,
            partial,
            second_ark: arks(&ark[rf + rp..])?,
            config,
        })
    }
}

/// circomlib `Poseidon(2)`: commitment tree nodes, `DomainHash1`.
pub static POSEIDON2: LazyLock<Poseidon<3>> = LazyLock::new(|| Poseidon::circom(57));
/// circomlib `Poseidon(3)`: `DomainHash2`.
pub static POSEIDON3: LazyLock<Poseidon<4>> = LazyLock::new(|| Poseidon::circom(56));
/// circomlib `Poseidon(4)`: commitment leaves.
pub static POSEIDON4: LazyLock<Poseidon<5>> = LazyLock::new(|| Poseidon::circom(60));
/// circomlib `Poseidon(5)`: `DomainHash4`.
pub static POSEIDON5: LazyLock<Poseidon<6>> = LazyLock::new(|| Poseidon::circom(60));
/// circomlib `Poseidon(6)`: `DomainHash5`.
pub static POSEIDON6: LazyLock<Poseidon<7>> = LazyLock::new(|| Poseidon::circom(63));

fn pow5(x: Fr) -> Fr {
    x.square().square() * x
}

fn full_sbox<const T: usize>(s: &mut [Fr; T], ark: &[Fr; T]) {
    for (x, c) in s.iter_mut().zip(ark) {
        *x = pow5(*x + c);
    }
}

fn apply<const T: usize>(m: &[[Fr; T]; T], s: &[Fr; T]) -> [Fr; T] {
    std::array::from_fn(|i| m[i].iter().zip(s).map(|(a, b)| *a * b).sum())
}

/// circomlib's output is the first state element after the permutation.
pub fn hash<const T: usize>(p: &Poseidon<T>, inputs: &[Fr]) -> Fr {
    assert_eq!(inputs.len(), T - 1, "inputs must fill the rate");
    let mut s = [Fr::ZERO; T];
    s[1..].copy_from_slice(inputs);
    for ark in &p.first_ark {
        full_sbox(&mut s, ark);
        s = apply(&p.mds, &s);
    }
    full_sbox(&mut s, &p.first_last_ark);
    s.iter_mut()
        .zip(&p.into_partial_ark)
        .for_each(|(x, c)| *x += c);
    s = apply(&p.into_partial_mds, &s);
    for PartialRound { ark, row, col } in &p.partial {
        s[0] = pow5(s[0]) + ark;
        let first = row.iter().zip(&s).map(|(a, b)| *a * b).sum();
        for k in 1..T {
            s[k] += col[k] * s[0];
        }
        s[0] = first;
    }
    for ark in &p.second_ark {
        full_sbox(&mut s, ark);
        s = apply(&p.mds, &s);
    }
    s[0]
}

/// In-circuit counterpart of [`hash`], over the standard parameters.
pub fn hash_var<const T: usize>(
    p: &Poseidon<T>,
    inputs: &[FpVar<Fr>],
) -> Result<FpVar<Fr>, SynthesisError> {
    assert_eq!(inputs.len(), T - 1, "inputs must fill the rate");
    let mut sponge = PoseidonSpongeVar::new(inputs.cs(), &p.config);
    for input in inputs {
        sponge.absorb(input)?;
    }
    sponge.squeeze_field_elements(1)?;
    Ok(sponge.state[0].clone())
}

#[cfg(test)]
mod tests {
    use ark_crypto_primitives::sponge::{
        CryptographicSponge, FieldBasedCryptographicSponge, poseidon::PoseidonSponge,
    };
    use ark_r1cs_std::alloc::AllocVar;
    use ark_relations::gr1cs::ConstraintSystem;
    use ark_std::UniformRand;

    use super::*;

    fn fr(hex: &str) -> Fr {
        let bytes: Vec<u8> = (0..hex.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).unwrap())
            .collect();
        Fr::from_be_bytes_mod_order(&bytes)
    }

    fn check_vector<const T: usize>(p: &Poseidon<T>, inputs: Vec<Fr>, expected: &str) {
        assert_eq!(hash(p, &inputs), fr(expected));

        let cs = ConstraintSystem::new_ref();
        let vars = Vec::new_witness(cs.clone(), || Ok(inputs)).unwrap();
        assert_eq!(hash_var(p, &vars).unwrap().value().unwrap(), fr(expected));
        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn matches_circomlibjs_vectors() {
        check_vector(
            &POSEIDON2,
            vec![0u64.into(), 0u64.into()],
            "2098f5fb9e239eab3ceac3f27b81e481dc3124d55ffed523a839ee8446b64864",
        );
        check_vector(
            &POSEIDON2,
            vec![1u64.into(), 2u64.into()],
            "115cc0f5e7d690413df64c6b9662e9cf2a3617f2743245519e19607a4417189a",
        );
        check_vector(
            &POSEIDON4,
            vec![1u64.into(), 2u64.into(), 3u64.into(), 4u64.into()],
            "299c867db6c1fdd79dcefa40e4510b9837e60ebb1ce0663dbaa525df65250465",
        );
        check_vector(
            &POSEIDON4,
            vec![
                (15_992_936_129_728_872_448u128 + 42).into(),
                0x11u64.into(),
                0x22u64.into(),
                333u64.into(),
            ],
            "2b939ab2f4d3773bf07eeef9e41d12f793d9a1a6c633cfddfe756ac500641892",
        );
    }

    /// The rearranged permutation agrees with the standard one, arkworks' sponge over the same parameters, on
    /// random inputs at every width.
    #[test]
    fn matches_the_standard_permutation() {
        fn check<const T: usize>(p: &Poseidon<T>) {
            let rng = &mut ark_std::test_rng();
            for _ in 0..32 {
                let inputs: Vec<Fr> = (1..T).map(|_| Fr::rand(rng)).collect();
                let mut sponge = PoseidonSponge::new(&p.config);
                inputs.iter().for_each(|x| sponge.absorb(x));
                sponge.squeeze_native_field_elements(1);
                assert_eq!(hash(p, &inputs), sponge.state[0]);
            }
        }
        check(&POSEIDON2);
        check(&POSEIDON3);
        check(&POSEIDON4);
        check(&POSEIDON5);
        check(&POSEIDON6);
    }

    /// The configs carry circomlib's standard round constants and MDS matrix, the parameters
    /// the Lean proofs fix as the Poseidon spec.
    #[test]
    fn configs_match_circomlib_standard_constants() {
        use std::str::FromStr;

        let json: serde_json::Value =
            serde_json::from_str(include_str!("../../lean/scripts/poseidon_constants.json"))
                .unwrap();
        let matrix = |v: &serde_json::Value| -> Vec<Vec<Fr>> {
            v.as_array()
                .unwrap()
                .iter()
                .map(|row| {
                    row.as_array()
                        .unwrap()
                        .iter()
                        .map(|x| Fr::from_str(x.as_str().unwrap()).unwrap())
                        .collect()
                })
                .collect()
        };
        let configs: [&PoseidonConfig<Fr>; 5] = [
            &POSEIDON2.config,
            &POSEIDON3.config,
            &POSEIDON4.config,
            &POSEIDON5.config,
            &POSEIDON6.config,
        ];
        for (rate, config) in (2..).zip(configs) {
            let expected = &json[(rate + 1).to_string()];
            assert_eq!(config.rate, rate);
            assert_eq!(config.capacity, 1);
            assert_eq!(config.full_rounds, 8);
            assert_eq!(config.alpha, 5);
            assert_eq!(
                config.partial_rounds as u64,
                expected["partialRounds"].as_u64().unwrap()
            );
            assert_eq!(config.ark, matrix(&expected["ark"]));
            assert_eq!(config.mds, matrix(&expected["mds"]));
        }
    }
}
