use std::cmp::{Eq, Ord};
use std::collections::HashMap;
use std::fmt;
use std::hash::Hash;

#[derive(Debug)]
pub struct CountingStats<E>
where
    E: Eq + Hash + Ord,
{
    values: HashMap<E, usize>,
}

impl<E: Hash + Eq + Ord> CountingStats<E> {
    pub fn new() -> Self {
        Self {
            values: HashMap::new(),
        }
    }

    pub fn get(&self, value: &E) -> usize {
        *self.values.get(value).unwrap_or(&0)
    }

    pub fn inc(&mut self, value: E) {
        let val = self.values.entry(value).or_insert(0);
        *val += 1;
    }

    pub fn inc_by(&mut self, value: E, val: usize) {
        let val_entry = self.values.entry(value).or_insert(0);
        *val_entry += val;
    }
}

impl<E: fmt::Display + Hash + Eq + Ord + Copy> fmt::Display for CountingStats<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut vals: Vec<_> = self.values.keys().collect();
        vals.sort();
        for event in &vals {
            writeln!(f, "{}\t{}", event, self.get(*event))?;
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
        let e = values.entry(self.phase).or_insert_with(Vec::new);
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
    pub fn new() -> Self {
        Self {
            pointer: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    pub fn start(&self, phase: E) -> Timer<E> {
        Timer {
            pointer: self.pointer.clone(),
            phase,
            begin: Instant::now(),
            stopped: false,
        }
    }

    pub fn count(&self, phase: E) -> usize {
        let values = self.pointer.borrow();
        values.get(&phase).map_or(0, Vec::len)
    }

    pub fn sum(&self, phase: E) -> Duration {
        let values = self.pointer.borrow();
        values
            .get(&phase)
            .map_or_else(|| Duration::new(0, 0), |v| v.iter().sum())
    }

    pub fn avg(&self, phase: E) -> Duration {
        #[allow(clippy::cast_possible_truncation)]
        let count = self.count(phase) as u32;

        self.sum(phase) / count
    }

    pub fn min(&self, phase: E) -> Duration {
        let values = self.pointer.borrow();
        values.get(&phase).map_or_else(
            || Duration::new(0, 0),
            |v| {
                v.iter()
                    .fold(Duration::new(u64::max_value(), 0), |acc, &val| {
                        if acc < val {
                            acc
                        } else {
                            val
                        }
                    })
            },
        )
    }

    pub fn max(&self, phase: E) -> Duration {
        let values = self.pointer.borrow();
        values.get(&phase).map_or_else(
            || Duration::new(0, 0),
            |v| {
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
            },
        )
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
                sum.subsec_millis(),
                avg.as_secs(),
                avg.subsec_millis(),
                min.as_secs(),
                min.subsec_millis(),
                max.as_secs(),
                max.subsec_millis()
            );
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Clone, Copy)]
    enum TestEnum {
        Case1,
        Case2,
    }

    #[test]
    fn counter() {
        let mut counter = CountingStats::new();
        counter.inc(TestEnum::Case1);
        assert_eq!(counter.get(&TestEnum::Case1), 1);
        assert_eq!(counter.get(&TestEnum::Case2), 0);
        counter.inc(TestEnum::Case2);
        counter.inc(TestEnum::Case2);
        assert_eq!(counter.get(&TestEnum::Case1), 1);
        assert_eq!(counter.get(&TestEnum::Case2), 2);
    }

    #[test]
    fn timer() {
        let timing = TimingStats::new();
        let mut timer1 = timing.start(TestEnum::Case1);
        let mut timer2 = timing.start(TestEnum::Case2);
        timer1.stop();
        {
            let _timer = timing.start(TestEnum::Case1);
            // atomatically stopped when dropped
        }
        timer2.stop();
        assert_eq!(timing.count(TestEnum::Case1), 2);
        assert_eq!(timing.count(TestEnum::Case2), 1);
    }
}
