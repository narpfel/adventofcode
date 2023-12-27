#![allow(mixed_script_confusables)]

use std::collections::HashSet;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Point {
    x: i64,
    y: i64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Beam {
    position: Point,
    direction: Point,
}

fn part_1(contraption: &[&[u8]], start: Beam) -> usize {
    let mut beams = vec![start];
    let mut seen: HashSet<Beam> = HashSet::default();

    while let Some(beam) = beams.pop() {
        let Beam {
            position: position @ Point { x, y },
            direction: Point { x: δx, y: δy },
        } = beam;
        if !seen.contains(&beam)
            && (0..contraption.len()).contains(&(y as usize))
            && (0..contraption[0].len()).contains(&(x as usize))
        {
            seen.insert(beam);
            match contraption[y as usize][x as usize] {
                b'|' if δy == 0 => {
                    beams.push(Beam {
                        position,
                        direction: Point { x: 0, y: -1 },
                    });
                    beams.push(Beam {
                        position,
                        direction: Point { x: 0, y: 1 },
                    });
                }
                b'-' if δx == 0 => {
                    beams.push(Beam {
                        position,
                        direction: Point { x: -1, y: 0 },
                    });
                    beams.push(Beam {
                        position,
                        direction: Point { x: 1, y: 0 },
                    });
                }
                c => {
                    let (δx, δy) = match c {
                        b'/' => (-δy, -δx),
                        b'\\' => (δy, δx),
                        _ => (δx, δy),
                    };
                    beams.push(Beam {
                        position: Point { x: x + δx, y: y + δy },
                        direction: Point { x: δx, y: δy },
                    });
                }
            }
        }
    }

    seen.iter()
        .map(|beam| beam.position)
        .collect::<HashSet<_>>()
        .len()
}

fn part_2(contraption: &[&[u8]]) -> usize {
    [
        (0..contraption.len())
            .map(|y| {
                part_1(
                    contraption,
                    Beam {
                        position: Point { x: 0, y: y as _ },
                        direction: Point { x: 1, y: 0 },
                    },
                )
            })
            .max()
            .unwrap(),
        (0..contraption.len())
            .map(|y| {
                part_1(
                    contraption,
                    Beam {
                        position: Point {
                            x: contraption[0].len() as i64 - 1,
                            y: y as _,
                        },
                        direction: Point { x: -1, y: 0 },
                    },
                )
            })
            .max()
            .unwrap(),
        (0..contraption[0].len())
            .map(|x| {
                part_1(
                    contraption,
                    Beam {
                        position: Point { x: x as _, y: 0 },
                        direction: Point { x: 0, y: 1 },
                    },
                )
            })
            .max()
            .unwrap(),
        (0..contraption[0].len())
            .map(|x| {
                part_1(
                    contraption,
                    Beam {
                        position: Point {
                            x: x as _,
                            y: contraption.len() as i64 - 1,
                        },
                        direction: Point { x: 0, y: -1 },
                    },
                )
            })
            .max()
            .unwrap(),
    ]
    .into_iter()
    .max()
    .unwrap()
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = std::fs::read_to_string("input")?;
    let contraption = input
        .lines()
        .map(|line| line.as_bytes())
        .collect::<Vec<_>>();
    println!(
        "{}",
        part_1(
            &contraption,
            Beam {
                position: Point { x: 0, y: 0 },
                direction: Point { x: 1, y: 0 }
            }
        )
    );
    println!("{}", part_2(&contraption));
    Ok(())
}
