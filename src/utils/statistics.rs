use std::cmp::Eq;
use std::collections::HashMap;
use std::fmt;
use std::hash::Hash;

#[derive(Debug)]
pub struct CountingStats<E>
where
    E: Eq + Hash,
{
    values: HashMap<E, usize>,
}

impl<E: Hash + Eq> CountingStats<E> {
    pub fn new() -> CountingStats<E> {
        CountingStats {
            values: HashMap::new(),
        }
    }

    pub fn get(&self, value: E) -> usize {
        *self.values.get(&value).unwrap_or(&0)
    }

    pub fn inc(&mut self, value: E) {
        let val = self.values.entry(value).or_insert(0);
        *val += 1;
    }
}

impl<E: fmt::Display + Hash + Eq> fmt::Display for CountingStats<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (event, count) in &self.values {
            write!(f, "{}\t{}\n", event, count)?;
        }
        Ok(())
    }
}

use std::cell::RefCell;
use std::rc::Rc;
use std::time::{Duration, Instant};

type TimingStatsValues<E> = HashMap<E, Vec<Duration>>;

pub struct Timer<E>
where
    E: Eq + Hash + Copy,
{
    pointer: Rc<RefCell<TimingStatsValues<E>>>,
    phase: E,
    begin: Instant,
    stopped: bool,
}

impl<E: Eq + Hash + Copy> Timer<E> {
    pub fn stop(&mut self) {
        let duration = self.begin.elapsed();
        let mut values = self.pointer.borrow_mut();
        let e = values.entry(self.phase).or_insert(Vec::new());
        e.push(duration);
        self.stopped = true;
    }
}

impl<E: Eq + Hash + Copy> Drop for Timer<E> {
    fn drop(&mut self) {
        if !self.stopped {
            self.stop();
        }
    }
}

pub struct TimingStats<E>
where
    E: Eq + Hash + Copy,
{
    pointer: Rc<RefCell<TimingStatsValues<E>>>,
}

impl<E: Eq + Hash + Copy> TimingStats<E> {
    pub fn new() -> TimingStats<E> {
        TimingStats {
            pointer: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    pub fn start(&self, phase: E) -> Timer<E> {
        Timer {
            pointer: self.pointer.clone(),
            phase: phase,
            begin: Instant::now(),
            stopped: false,
        }
    }

    pub fn count(&self, phase: E) -> usize {
        let values = self.pointer.borrow();
        values.get(&phase).map(|v| v.len()).unwrap_or(0)
    }

    pub fn sum(&self, phase: E) -> Duration {
        let values = self.pointer.borrow();
        values
            .get(&phase)
            .map(|v| v.iter().sum())
            .unwrap_or(Duration::new(0, 0))
    }

    pub fn avg(&self, phase: E) -> Duration {
        self.sum(phase) / self.count(phase) as u32
    }

    pub fn min(&self, phase: E) -> Duration {
        let values = self.pointer.borrow();
        values
            .get(&phase)
            .map(|v| {
                v.iter()
                    .fold(Duration::new(u64::max_value(), 0), |acc, &val| {
                        if acc < val {
                            acc
                        } else {
                            val
                        }
                    })
            })
            .unwrap_or(Duration::new(0, 0))
    }

    pub fn max(&self, phase: E) -> Duration {
        let values = self.pointer.borrow();
        values
            .get(&phase)
            .map(|v| {
                v.iter().fold(
                    Duration::new(0, 0),
                    |acc, &val| {
                        if acc > val {
                            acc
                        } else {
                            val
                        }
                    },
                )
            })
            .unwrap_or(Duration::new(0, 0))
    }
}

impl<E: Eq + Hash + Copy + fmt::Display> TimingStats<E> {
    pub fn print(&self) {
        let values = self.pointer.borrow();
        for &stat in values.keys() {
            let sum = self.sum(stat);
            let avg = self.avg(stat);
            let min = self.min(stat);
            let max = self.max(stat);
            println!(
                "  {} count {}  sum {}.{}  avg: {}.{}  min {}.{}  max {}.{}",
                stat,
                self.count(stat),
                sum.as_secs(),
                sum.subsec_nanos() / 1_000_000,
                avg.as_secs(),
                avg.subsec_nanos() / 1_000_000,
                min.as_secs(),
                min.subsec_nanos() / 1_000_000,
                max.as_secs(),
                max.subsec_nanos() / 1_000_000
            );
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[derive(PartialEq, Eq, Hash, Clone, Copy)]
    enum TestEnum {
        Case1,
        Case2,
    }

    #[test]
    fn counter() {
        let mut counter = CountingStats::new();
        counter.inc(TestEnum::Case1);
        assert_eq!(counter.get(TestEnum::Case1), 1);
        assert_eq!(counter.get(TestEnum::Case2), 0);
        counter.inc(TestEnum::Case2);
        counter.inc(TestEnum::Case2);
        assert_eq!(counter.get(TestEnum::Case1), 1);
        assert_eq!(counter.get(TestEnum::Case2), 2);
    }

    #[test]
    fn timer() {
        let timing = TimingStats::new();
        let mut timer1 = timing.start(TestEnum::Case1);
        let mut timer2 = timing.start(TestEnum::Case2);
        timer1.stop();
        {
            let timer1 = timing.start(TestEnum::Case1);
            // atomatically stopped when dropped
        }
        timer2.stop();
        assert_eq!(timing.count(TestEnum::Case1), 2);
        assert_eq!(timing.count(TestEnum::Case2), 1);
    }

}
