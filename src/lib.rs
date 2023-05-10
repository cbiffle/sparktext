//! Generates compact graphs for showing trends inline with text (sparklines)
//! using Unicode text.
//!
//! [Sparklines] are "data visualization words" -- word-sized graphics that
//! describe the trend in a signal and can be used inline with text. For
//! instance:
//!
//! My love of sparklines has ⣀⡠⠔⠊⠉ increased consistently over time.
//!
//! This crate provides a function for formatting time-series data as a text
//! using Unicode Braille characters, which are pretty well supported across
//! platforms and in both proportional and monospaced fonts. For instance, you
//! could chart a simple sine wave like this:
//!
//! ```
//! # use sparktext::sparktext;
//! let mut data = vec![];
//! for i in 0..20 {
//!     data.push((((i as f32) * std::f32::consts::PI / 3.).sin() * 5. + 10.) as usize);
//! }
//! assert_eq!(
//!     sparktext(data, 10),
//!     "⠊⠑⣀⠊⠑⣀⠊⠑⣀⠊",
//! );
//! ```
//!
//! # Using sparklines effectively
//!
//! The modern "sparkline" concept was invented by data visualization expert
//! Edward Tufte, who has a a lot of information about their application on [his
//! website][tufte-sparklines]. In brief, my poor summary of his suggestions is
//!
//! - Keep the sparkline about the same size as the surrounding text -- in this
//!   case, that's handled for you by using text.
//!
//! - Printing a latest value just right of the sparkline is convenient.
//!   Sometimes printing a starting value to the left is also convenient.
//!
//! - It can be useful to indicate min and max values for the time series
//!   presented in a sparkline, but generally, a chart that needs a detailed Y
//!   axis should probably not be a sparkline. Sparklines are really best for
//!   commenting on trends in data rather than displaying absolute magnitude or
//!   comparing two series.
//!
//! - A conventional Tufte sparkline should have significantly higher resolution
//!   than what's possible with this crate. Such are the limitations of ASCII
//!   art (or in this case, Unicode art).
//!
//! [Sparklines]: https://en.wikipedia.org/wiki/Sparkline
//! [tufte-sparklines]: https://www.edwardtufte.com/bboard/q-and-a-fetch-msg?msg_id=0001OR&topic_id=1

use std::{iter::Sum, ops::{Div, Sub, Mul}};

use num_traits::FromPrimitive;

/// Generates a text sparkline from `data`.
///
/// `data` is assumed to be a series of points equally spaced in time. The type
/// of the point, `P`, must implement the slightly gross set of traits below,
/// but you can think of it as "a number" -- most numeric types you're likely to
/// use will just work, with one caveat about floating point, below.
///
/// `max_width` gives the maximum number of character cells to use to render the
/// result. If `data` contains fewer than `2*max_width` data points, the result
/// may be shorter.
///
/// # How to use floating point
///
/// Rust floating point types don't implement `Ord`, because there are several
/// ways they could do it that are appropriate in different circumstances. For
/// this function, you want the strategy provided by the `ordered_float` crate.
/// To feed in floating point data encoded as (say) `f64`, use:
///
/// ```
/// # use sparktext::sparktext;
/// use ordered_float::OrderedFloat;
///
/// let my_data: [f64; 4] = [0., 1., 2., 3.];
///
/// sparktext(my_data.into_iter().map(OrderedFloat), 2);
/// ```
pub fn sparktext<P>(
    data: impl IntoIterator<Item = P>,
    char_width: usize,
) -> String
    where P: Clone + Sum + Div<Output = P> + Sub<Output = P> + Mul<Output = P> + FromPrimitive + Ord,
{
    let data = data.into_iter().collect::<Vec<_>>();

    // We're going to have two buckets per char of output width, unless the
    // input is shorter than that.
    let n_buckets = usize::min(char_width * 2, data.len());
    // Do a naive bucketing of the data by separating it into groups of
    // samples_per_bucket. The final group may have fewer samples in it than the
    // others.
    let samples_per_bucket = (data.len() + (n_buckets - 1)) / n_buckets;
    let buckets = data.chunks(samples_per_bucket)
        .map(|vals| vals.iter().cloned().sum::<P>() / P::from_usize(vals.len()).unwrap())
        .collect::<Vec<_>>();

    // Determine the range of the bucketed values.
    let min = buckets.iter().min().unwrap().clone();
    let max = buckets.iter().max().unwrap().clone();

    if min == max {
        // As a special case, if the line is perfectly flat, we'll just generate
        // a line to avoid corner cases in the math below.
        let mut out = String::new();
        for _ in 0..char_width {
            out.push('⠒');
        }
        return out;
    }

    // Generate characters for pairs of buckets.
    buckets.chunks(2)
        .map(|pair| {
            let mut c = 0x2800;
            c |= match map_4(pair[0].clone(), min.clone(), max.clone()) {
                0 => 1 << 6,
                1 => 1 << 2,
                2 => 1 << 1,
                _ => 1 << 0,
            };
            if let Some(p1) = pair.get(1) {
                c |= match map_4(p1.clone(), min.clone(), max.clone()) {
                    0 => 1 << 7,
                    1 => 1 << 5,
                    2 => 1 << 4,
                    _ => 1 << 3,
                };
            }
            char::from_u32(c).unwrap()
        })
        .collect()
}

fn map_4<P>(value: P, min: P, max: P) -> usize
    where P: Clone + Sub<Output = P> + Mul<Output = P> + FromPrimitive + Ord,
{
    let x = (value - min.clone()) * P::from_u8(4).unwrap();
    let step = max - min;
    if x < step.clone() {
        0
    } else if x < step.clone() * P::from_u8(2).unwrap() {
        1
    } else if x < step * P::from_u8(3).unwrap() {
        2
    } else {
        3
    }
}

#[cfg(test)]
mod tests {
    use ordered_float::OrderedFloat;

    use super::*;

    #[test]
    fn it_works() {
        let data = [0., 1., 2., 3.].map(OrderedFloat);
        assert_eq!(
            sparktext(data, 2),
            "⡠⠊",
        );
    }

    #[test]
    fn flatline() {
        let data = [0.; 4].map(OrderedFloat);
        assert_eq!(
            sparktext(data, 2),
            "⠒⠒",
        );
    }

    #[test]
    fn discontinuous() {
        let data = [0., 10., 5., 15.].map(OrderedFloat);
        assert_eq!(
            sparktext(data, 2),
            "⡐⠌",
        );
    }

    #[test]
    fn decimal() {
        use rust_decimal_macros::dec;

        let data = [dec!(0), dec!(10), dec!(5), dec!(15)];
        assert_eq!(
            sparktext(data, 2),
            "⡐⠌",
        );
    }

    #[test]
    fn shorty() {
        let data = [0., 1.].map(OrderedFloat);
        assert_eq!(
            sparktext(data, 5),
            "⡈",
        );
    }

    #[test]
    fn sin() {
        let mut data = [0; 20];
        for (i, d) in data.iter_mut().enumerate() {
            *d = (((i as f32) * std::f32::consts::PI / 3.).sin() * 5. + 10.) as usize;
        }
        assert_eq!(
            sparktext(data, 10),
            "⠊⠑⣀⠊⠑⣀⠊⠑⣀⠊",
        );
    }
}
