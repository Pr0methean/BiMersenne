use std::time::Instant;
use bitvec::bitvec;
use bitvec::order::Msb0;
use num_bigint::BigUint;
use num_integer::Roots;
use num_prime::detail::SMALL_PRIMES;
use num_prime::{Primality, PrimalityTestConfig, PrimalityUtils};
use parking_lot::RwLock;
use rand::rngs::ThreadRng;
use rand::RngCore;
use crate::ReadableDuration;

pub struct ConcurrentPrimeBuffer(RwLock<Vec<u64>>);

pub struct ConcurrentPrimeBufferIter<'a> {
    buffer: &'a ConcurrentPrimeBuffer,
    index: usize,
}

impl <'a> Iterator for ConcurrentPrimeBufferIter<'a> {
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        let result = self.buffer.0.read().get(self.index).copied();
        self.index += 1;
        result
    }
}

impl ConcurrentPrimeBuffer {
    pub fn new() -> Self {
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
            if len * 2 < n {
                self.reserve_concurrent(bound * 2);
            } else {
                self.reserve_concurrent(bound + n);
            }
            out = self.0.read().get(n as usize).copied();
        }
        out.unwrap()
    }

    pub fn primes(&self, limit: u64) -> std::iter::Take<ConcurrentPrimeBufferIter> {
        self.reserve_concurrent(limit);
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

    pub fn is_prime(
        &self,
        target: &BigUint,
        config: Option<PrimalityTestConfig>,
    ) -> Primality
    {
        let config = config.unwrap_or(PrimalityTestConfig::default());
        let mut probability = 1.;

        // miller-rabin test
        let mut witness_list: Vec<u64> = Vec::new();
        if config.sprp_trials > 0 {
            witness_list.extend(self.primes(config.sprp_trials as u64));
            probability *= 1. - 0.25f32.powi(config.sprp_trials as i32);
        }
        if config.sprp_random_trials > 0 {
            for _ in 0..config.sprp_random_trials {
                // we have ensured target is larger than 2^64
                let mut w: u64 = ThreadRng::default().next_u64();
                while witness_list.iter().find(|&x| x == &w).is_some() {
                    w = ThreadRng::default().next_u64();
                }
                witness_list.push(w);
            }
            probability *= 1. - 0.25f32.powi(config.sprp_random_trials as i32);
        }
        if !witness_list
            .into_iter()
            .all(|x| target.is_sprp(BigUint::from(x)))
        {
            return Primality::No;
        }

        // lucas probable prime test
        if config.slprp_test {
            probability *= 1. - 4f32 / 15f32;
            if !target.is_slprp(None, None) {
                return Primality::No;
            }
        }
        if config.eslprp_test {
            probability *= 1. - 4f32 / 15f32;
            if !target.is_eslprp(None) {
                return Primality::No;
            }
        }

        Primality::Probable(probability)
    }
}
