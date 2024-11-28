use num_bigint::BigUint;
use num_integer::Integer;
use num_prime::buffer::{NaiveBuffer, PrimeBufferExt};
use num_prime::nt_funcs::{factorize128, is_prime64};
use num_prime::{BitTest, ExactRoots, Primality, PrimalityTestConfig, PrimeBuffer};
use std::borrow::Cow;
use std::fmt::{Display, Formatter};
use std::ops::{Shl, Sub};
use std::sync::OnceLock;
use std::time;
use tokio::task::JoinHandle;
use Primality::{No, Yes};

pub const MERSENNE_EXPONENTS: [u32; 52] = [
    2, 3, 5, 7, 13, 17, 19, 31, 61, 89, 107, 127, 521, 607, 1279, 2203, 2281, 3217, 4253, 4423,
    9689, 9941, 11213, 19937, 21701, 23209, 44497, 86243, 110503, 132049, 216091, 756839, 859433,
    1257787, 1398269, 2976221, 3021377, 6972593, 13466917, 20996011, 24036583, 25964951, 30402457,
    32582657, 37156667, 42643801, 43112609, 57885161, 74207281, 77232917, 82589933, 136279841,
];
pub const NUM_TRIAL_DIVISIONS: usize = 1 << 24;
pub const REPORT_TRIAL_DIVISIONS_EVERY: usize = 1 << 10;
pub const NUM_TRIAL_ROOTS: usize = 1 << 6;

static CONFIG: OnceLock<Option<PrimalityTestConfig>> = OnceLock::new();
static BUFFER: OnceLock<NaiveBuffer> = OnceLock::new();
static PRIMES_AS_BIGUINT: OnceLock<Box<[BigUint]>> = OnceLock::new();
static MIN_ROOT_BITS: OnceLock<u64> = OnceLock::new();

fn is_prime_with_trials(num: BigUint, known_non_factors: &[BigUint]) -> PrimalityResult {
    let buffer = BUFFER.get_or_init(|| {
        let mut buffer = NaiveBuffer::new();
        let desired_len = NUM_TRIAL_DIVISIONS.max(NUM_TRIAL_ROOTS) as u64;
        buffer.reserve(desired_len);
        while buffer.iter().len() < desired_len as usize {
            buffer.reserve(buffer.iter().last().unwrap() * 2);
        }
        buffer
    });
    let config = CONFIG.get_or_init(|| {
        let mut config = PrimalityTestConfig::default();
        config.sprp_trials = 8;
        config.sprp_random_trials = 4;
        config.slprp_test = true;
        config.eslprp_test = true;
        Some(config)
    });
    let primes_as_biguint = PRIMES_AS_BIGUINT.get_or_init(|| {
        // Skip 2: definition as (2^p - 1)(2^q - 1) +/- 2 ensures product is odd
        buffer
            .iter()
            .copied()
            .skip(1)
            .take(NUM_TRIAL_DIVISIONS)
            .map(BigUint::from)
            .collect()
    });
    let min_root_bits = MIN_ROOT_BITS.get_or_init(|| primes_as_biguint.last().unwrap().bits());
    let num_bits = num.bits();
    let start_trials = time::Instant::now();
    let mut divisions_done = 0;
    for chunk in primes_as_biguint.chunks(REPORT_TRIAL_DIVISIONS_EVERY) {
        for prime in chunk {
            if !known_non_factors.contains(prime) && num.is_multiple_of(prime) {
                eprintln!("Trial division found {} as a factor of a {}-bit number in {}ns",
                          prime, num_bits, start_trials.elapsed().as_nanos());
                return PrimalityResult {
                    result: No,
                    source: format!("Trial division by {}", prime).into(),
                };
            }
        }
        divisions_done += chunk.len();
        eprintln!("{} trial divisions failed for a {}-bit number in {}ns",
                  divisions_done, num_bits, start_trials.elapsed().as_nanos());
    }
    let mut num_trial_roots: usize = 0;
    let start_roots = time::Instant::now();
    for prime in buffer.iter().copied().take(NUM_TRIAL_ROOTS) {
        if prime == 2 && num_bits < 100_000_000 {
            // Previous runs have ruled out numbers in this range being perfect squares
            continue;
        }
        if (prime.bits() as u64 - 1) * (min_root_bits - 1) > num_bits {
            // Higher roots would've been found by trial divisions already
            eprintln!("Ruling out {} and higher roots for a {}-bit number",
                      prime, num_bits);
            break;
        }
        if num.is_nth_power(prime as u32) {
            eprintln!("Trial root found {} root of a {}-bit number in {}ns",
                      prime, num_bits, start_trials.elapsed().as_nanos());
            return PrimalityResult {
                result: No,
                source: format!("Trial nth root: {}", prime).into(),
            };
        } else {
            num_trial_roots += 1;
            eprintln!("{}-bit number has no {} root (trying roots for {}ns)",
                      num_bits, prime, start_roots.elapsed().as_nanos());
        }
    }
    eprintln!("Trial roots failed for a {}-bit number in {} ns; calling is_prime",
              num_bits, start_roots.elapsed().as_nanos());
    let start_is_prime = time::Instant::now();
    let result = buffer.is_prime(&num, *config);
    let elapsed = start_is_prime.elapsed();
    drop(num);
    eprintln!(
        "is_prime for a {}-bit number took {}ns and returned {:?}",
        num_bits,
        elapsed.as_nanos(),
        result
    );
    PrimalityResult {
        result,
        source: "is_prime".into(),
    }
}

struct PrimalityResult {
    result: Primality,
    source: Cow<'static, str>,
}

impl Display for PrimalityResult {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(format!("{:?}, {}", self.result, self.source).as_str())
    }
}

struct OutputLine {
    p: u32,
    q: u32,
    result_product_minus_2: JoinHandle<PrimalityResult>,
}

#[tokio::main(flavor = "multi_thread")]
async fn main() {
    println!("p,q,prime(M(p)*M(q)-2),Source");
    let mut output_lines = Vec::new();
    let mut is_prime_calls = 0;
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
                    result_product_minus_2: tokio::spawn(async move {
                        PrimalityResult {
                            result: if is_prime64(product - 2) { Yes } else { No },
                            source: "is_prime64".into(),
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
                    result_product_minus_2: tokio::spawn(async move {
                        PrimalityResult {
                            result: if factorize128(product - 2).into_values().sum::<usize>() == 1 {
                                Yes
                            } else {
                                No
                            },
                            source: "factorize128".into(),
                        }
                    }),
                });
            } else {
                is_prime_calls += 1;
                let mut known_non_factors = Vec::with_capacity(2);
                if p <= 63 {
                    known_non_factors.push(BigUint::from(1u64 << p - 1));
                }
                if q <= 63 {
                    known_non_factors.push(BigUint::from(1u64 << q - 1));
                }
                output_lines.push(OutputLine {
                    p,
                    q,
                    result_product_minus_2: tokio::spawn(async move {
                        let mut product_limbs = vec![u32::MAX; (p + q) as usize / 32];
                        if (p + q) % 32 != 0 {
                            product_limbs.push((1 << ((p + q) % 32)) - 1);
                        }
                        let mut product_m2: BigUint = BigUint::new(product_limbs);
                        debug_assert!(product_m2 == one().shl(p + q).sub(one()));
                        if p == q {
                            product_m2.set_bit(p as u64 + 1, false);
                        } else {
                            product_m2.set_bit(p as u64, false);
                            product_m2.set_bit(q as u64, false);
                        }
                        debug_assert!(product_m2 == one().shl(p + q).sub(one().shl(p)).sub(one().shl(q)).sub(one()));
                        is_prime_with_trials(product_m2, &known_non_factors)
                    })
                    .into(),
                });
            }
        }
    }
    eprintln!("All computation tasks launched; {} will use is_prime or trial divisions", is_prime_calls);
    for line in output_lines.into_iter() {
        let p = line.p;
        let q = line.q;
        let result_product_plus_2 = line.result_product_minus_2.await.unwrap();
        println!(
            "{}, {}, {}",
            p, q, result_product_plus_2
        );
    }
}

fn one() -> BigUint {
    BigUint::from(1u8)
}
