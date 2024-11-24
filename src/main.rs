use std::borrow::Cow;
use std::fmt::{Display, Formatter};
use num_bigint::BigUint;
use num_prime::nt_funcs::{factorize128, is_prime64};
use num_prime::{BitTest, ExactRoots, Primality, PrimalityTestConfig, PrimeBuffer};
use std::ops::{Add, Shl, Sub};
use std::sync::OnceLock;
use std::time;
use num_integer::Integer;
use num_prime::buffer::{NaiveBuffer, PrimeBufferExt};
use Primality::{No, Yes};
use tokio::task::JoinHandle;

pub const MERSENNE_EXPONENTS: [u32; 52] = [2, 3, 5, 7, 13, 17, 19, 31, 61, 89, 107, 127, 521, 607,
        1279, 2203, 2281, 3217, 4253,4423,9689,9941,11213,19937,
    21701,23209,44497,86243,110503,132049,216091,
    756839,859433,1257787,1398269,2976221,3021377,
    6972593,13466917,20996011,24036583,25964951,
    30402457,32582657,37156667,42643801,43112609,
    57885161, 74207281, 77232917, 82589933, 136279841];
pub const NUM_TRIAL_DIVISIONS: usize = 16384;
pub const NUM_TRIAL_ROOTS: usize = 256;

static CONFIG: OnceLock<Option<PrimalityTestConfig>> = OnceLock::new();
static BUFFER: OnceLock<NaiveBuffer> = OnceLock::new();
static PRIMES_AS_BIGUINT: OnceLock<Box<[BigUint]>> = OnceLock::new();
static MIN_ROOT_BITS: OnceLock<u64> = OnceLock::new();

fn is_prime_with_trials(num: &BigUint, known_non_factors: &[BigUint]) -> PrimalityResult {
    let buffer = BUFFER.get_or_init(|| {
        let mut buffer = NaiveBuffer::new();
        buffer.reserve(NUM_TRIAL_DIVISIONS.max(NUM_TRIAL_ROOTS) as u64);
        buffer
    });
    let config = CONFIG.get_or_init(|| {
        let mut config = PrimalityTestConfig::default();
        config.sprp_trials = 16;
        config.sprp_random_trials = 4;
        config.slprp_test = true;
        config.eslprp_test = true;
        Some(config)
    });
    let primes_as_biguint = PRIMES_AS_BIGUINT.get_or_init(|| {
        // Skip 2: definition as (2^p - 1)(2^q - 1) +/- 2 ensures product is odd
        buffer.iter().copied().skip(1).take(NUM_TRIAL_DIVISIONS).map(BigUint::from).collect()
    });
    let min_root_bits = MIN_ROOT_BITS.get_or_init(|| {
        primes_as_biguint.last().unwrap().bits()
    });
    for prime in primes_as_biguint.iter() {
        if !known_non_factors.contains(prime) && num.is_multiple_of(prime) {
            return PrimalityResult {
                result: No,
                source: format!("Trial division by {}", prime).into()
            };
        }
    }
    let num_bits = num.bits();
    for prime in buffer.iter().copied().take(NUM_TRIAL_ROOTS) {
        if prime.bits() as u64 * min_root_bits > num_bits {
            // Higher roots would've been found by trial divisions already
            break;
        }
        if num.is_nth_power(prime as u32) {
            return PrimalityResult {
                result: No,
                source: format!("Trial nth root: {}", prime).into()
            };
        }
    }
    eprintln!("Calling is_prime for a {}-bit number", num_bits);
    let instant = time::Instant::now();
    let result = buffer.is_prime(num, *config);
    let elapsed = instant.elapsed();
    eprintln!("is_prime for a {}-bit number took {}ns and returned {:?}", num_bits, elapsed.as_nanos(), result);
    PrimalityResult {
        result,
        source: "is_prime".into()
    }
}

struct PrimalityResult {
    result: Primality,
    source: Cow<'static, str>
}

impl Display for PrimalityResult {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(format!("{:?}, {}", self.result, self.source).as_str())
    }
}

struct OutputLine {
    p: u32,
    q: u32,
    result_product_plus_2: JoinHandle<PrimalityResult>,
    result_product_minus_2: JoinHandle<PrimalityResult>
}

#[tokio::main(flavor = "multi_thread", )]
async fn main() {
    println!("p,q,prime(M(p)*M(q)-2),Source,prime(M(p)*M(q)+2),Source");
    let mut output_lines = Vec::new();
    for p_i in (0..MERSENNE_EXPONENTS.len()).rev() {
        let p = MERSENNE_EXPONENTS[p_i];
        for q_i in (p_i..MERSENNE_EXPONENTS.len()).rev() {
            let q = MERSENNE_EXPONENTS[q_i];
            if p + q <= 64 {
                let m_p = (1u64 << p) - 1;
                let m_q = (1u64 << q) - 1;
                let product = m_p * m_q;
                output_lines.push(OutputLine {
                    p,
                    q,
                    result_product_plus_2: tokio::spawn(async move {
                        PrimalityResult {
                            result: if is_prime64(product + 2) { Yes } else { No },
                            source: "is_prime64".into()
                        }
                    }),
                    result_product_minus_2: tokio::spawn(async move {
                        PrimalityResult {
                            result: if is_prime64(product - 2) { Yes } else { No },
                            source: "is_prime64".into()
                        }
                    }),
                });
            } else if p + q <= 128 {
                let m_p = (1u64 << p) - 1;
                let m_q = (1u128 << q) - 1;
                let product = m_p as u128 * m_q;
                output_lines.push(OutputLine {
                    p,
                    q,
                    result_product_plus_2: tokio::spawn(async move {
                        PrimalityResult {
                            result: if factorize128(product + 2).into_values().sum::<usize>() == 1 { Yes } else { No },
                            source: "factorize128".into()
                        }
                    }),
                    result_product_minus_2: tokio::spawn(async move {
                        PrimalityResult {
                            result: if factorize128(product - 2).into_values().sum::<usize>() == 1 { Yes } else { No },
                            source: "factorize128".into()
                        }
                    }),
                });
            } else {
                let mut known_non_factors = Vec::with_capacity(2);
                if p <= 63 {
                    known_non_factors.push(BigUint::from(1u64 << p - 1));
                }
                if q <= 63 {
                    known_non_factors.push(BigUint::from(1u64 << q - 1));
                }
                let known_non_factors_copy = known_non_factors.clone();
                let product_m1: BigUint = one().shl(p+q)
                    .sub(one().shl(p))
                    .sub(one().shl(q));
                let product_m2 = product_m1.clone().sub(one());
                let product_p2 = product_m1.add(three());
                output_lines.push(OutputLine {
                    p,
                    q,
                    result_product_plus_2: tokio::spawn(async move {
                        is_prime_with_trials(&product_p2, &known_non_factors_copy)
                    }).into(),
                    result_product_minus_2: tokio::spawn(async move {
                        is_prime_with_trials(&product_m2, &known_non_factors)
                    }).into(),
                });
            }
        }
    }
    eprintln!("All computation tasks launched");
    for line in output_lines.into_iter() {
        let p = line.p;
        let q = line.q;
        let result_product_minus_2 = line.result_product_minus_2.await.unwrap();
        let result_product_plus_2 = line.result_product_plus_2.await.unwrap();
        println!("{}, {}, {}, {}", p, q, result_product_minus_2, result_product_plus_2);
    }
}

fn three() -> BigUint {
    BigUint::from(3u8)
}

fn one() -> BigUint {
    BigUint::from(1u8)
}
