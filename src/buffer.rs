use std::time::Instant;
use bitvec::bitvec;
use bitvec::order::Msb0;
use num_bigint::BigUint;
use num_integer::Roots;
use num_prime::detail::SMALL_PRIMES;
use num_prime::{Primality, PrimalityUtils};
use parking_lot::RwLock;
use rand::rngs::ThreadRng;
use rand::RngCore;
use crate::ReadableDuration;

const SPRP_TRIALS: u64 = 8;
const RANDOM_SPRP_TRIALS: u64 = 4;

pub struct ConcurrentPrimeBuffer(RwLock<Vec<u64>>);

pub struct ConcurrentPrimeBufferIter<'a> {
    buffer: &'a ConcurrentPrimeBuffer,
    index: u64,
}

impl <'a> Iterator for ConcurrentPrimeBufferIter<'a> {
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        let result = self.buffer.get_nth(self.index);
        self.index += 1;
        Some(result)
    }
}

impl ConcurrentPrimeBuffer {
    pub async fn new() -> Self {
        ConcurrentPrimeBuffer(RwLock::new(Vec::from(SMALL_PRIMES.map(u64::from))))
    }

    pub fn copying_iter(&self) -> ConcurrentPrimeBufferIter {
        ConcurrentPrimeBufferIter {
            buffer: self,
            index: 0,
        }
    }

    pub fn get_nth(&self, n: u64) -> u64 {
        let mut out = self.0.read().get(n as usize).copied();
        while out.is_none() {
            let list = self.0.read();
            let len = list.len() as u64;
            let bound = *list.last().unwrap();
            drop(list);
            if len < n {
                self.reserve_concurrent(bound + n);
            }
            out = self.0.read().get(n as usize).copied();
        }
        out.unwrap()
    }

    pub fn primes(&self, limit: u64) -> std::iter::Take<ConcurrentPrimeBufferIter> {
        let position = match self.0.read().binary_search(&limit) {
            Ok(p) => p + 1,
            Err(p) => p,
        }; // into_ok_or_err()
        self.copying_iter().take(position)
    }

    pub fn bound(&self) -> u64 {
        *self.0.read().last().unwrap()
    }

    fn reserve_concurrent(&self, limit: u64) {
        let sieve_limit = (limit | 1) + 2; // make sure sieving limit is odd and larger than limit
        let current = self.bound();
        if sieve_limit < current {
            return;
        }
        let mut list = self.0.write();
        let current = list.last().copied().unwrap();
        if sieve_limit < current {
            return;
        }
        eprintln!("Expanding prime limit from {} to {}", current, sieve_limit);
        let sieve_start = Instant::now();
        // create sieve and filter with existing primes
        let mut sieve = bitvec![usize, Msb0; 0; ((sieve_limit - current) / 2) as usize];
        for p in list.iter().skip(1).copied() {
            // skip pre-filtered 2
            let start = if p * p < current {
                p * ((current / p) | 1) // start from an odd factor
            } else {
                p * p
            };
            for multi in (start..sieve_limit).step_by(2 * (p as usize)) {
                if multi >= current {
                    sieve.set(((multi - current) / 2) as usize, true);
                }
            }
        }

        // sieve with new primes
        for p in (current..Roots::sqrt(&sieve_limit) + 1).step_by(2) {
            for multi in (p * p..sieve_limit).step_by(2 * (p as usize)) {
                if multi >= current {
                    sieve.set(((multi - current) / 2) as usize, true);
                }
            }
        }

        // collect the sieve
        list.extend(sieve.iter_zeros().map(|x| (x as u64) * 2 + current));
        eprintln!("Expanding prime limit from {} to {} took {}", current, sieve_limit, ReadableDuration(sieve_start.elapsed()));
    }

    #[inline]
    pub fn is_prime(
        &self,
        target: &BigUint,
    ) -> Primality
    {
        let mut probability = 1.;

        // miller-rabin test
        let mr_start = Instant::now();
        let mut witness_list: Vec<u64> = Vec::with_capacity((SPRP_TRIALS + RANDOM_SPRP_TRIALS) as usize);
        witness_list.extend(self.primes(SPRP_TRIALS));
        probability *= 1. - 0.25f32.powi(SPRP_TRIALS as i32);
        for _ in 0..RANDOM_SPRP_TRIALS {
            // we have ensured target is larger than 2^64
            let mut w: u64 = ThreadRng::default().next_u64();
            while witness_list.iter().find(|&x| x == &w).is_some() {
                w = ThreadRng::default().next_u64();
            }
            witness_list.push(w);
        }
        probability *= 1. - 0.25f32.powi(RANDOM_SPRP_TRIALS as i32);
        if !witness_list
            .into_iter()
            .all(|x| {
                let mr_start = Instant::now();
                let result = target.is_sprp(BigUint::from(x));
                eprintln!("Miller-Rabin test for a {}-bit number with witness {} took {} and returned {}",
                          target.bits(), x, ReadableDuration(mr_start.elapsed()), result);
                result
            })
        {
            eprintln!("Miller-Rabin test found a {}-bit number composite after {}", target.bits(),
                      ReadableDuration(mr_start.elapsed()));
            return Primality::No;
        }
        eprintln!("Miller-Rabin test failed to prove a {}-bit number composite after {}", target.bits(),
                  ReadableDuration(mr_start.elapsed()));
        // lucas probable prime test
        probability *= 1. - 4f32 / 15f32;
        let lucas_start = Instant::now();
        if !target.is_slprp(None, None) {
            eprintln!("Strong Lucas test found a {}-bit number composite after {}", target.bits(),
                      ReadableDuration(lucas_start.elapsed()));
            return Primality::No;
        }
        eprintln!("Strong Lucas test failed to prove a {}-bit number composite after {}", target.bits(),
                  ReadableDuration(lucas_start.elapsed()));
        probability *= 1. - 4f32 / 15f32;
        let lucas_start = Instant::now();
        if !target.is_eslprp(None) {
            eprintln!("Extra-strong Lucas test found a {}-bit number composite after {}", target.bits(),
                      ReadableDuration(lucas_start.elapsed()));
            return Primality::No;
        }
        eprintln!("Extra-strong Lucas test failed to prove a {}-bit number composite after {}", target.bits(),
                  ReadableDuration(lucas_start.elapsed()));
        Primality::Probable(probability)
    }
}
