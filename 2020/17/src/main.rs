use std::fs::File;
use std::io;
use std::io::BufRead;
use std::io::BufReader;
use std::path::Path;

use itertools::iproduct;

fn next_generation_part1(cells: &[Vec<Vec<bool>>]) -> Vec<Vec<Vec<bool>>> {
    let x = cells[0][0].len() as isize;
    let y = cells[0].len() as isize;
    let z = cells.len() as isize;
    (-1..=z)
        .map(|i| {
            (-1..=y)
                .map(|j| {
                    (-1..=x)
                        .map(|k| {
                            let cell = (|| {
                                Some(*cells.get(i as usize)?.get(j as usize)?.get(k as usize)?)
                            })()
                            .unwrap_or(false);
                            let neighbours =
                                iproduct!((i - 1)..=(i + 1), (j - 1)..=(j + 1), (k - 1)..=(k + 1))
                                    .filter_map(|(i, j, k)| {
                                        Some(
                                            *cells
                                                .get(i as usize)?
                                                .get(j as usize)?
                                                .get(k as usize)?
                                                as u8,
                                        )
                                    })
                                    .sum::<u8>()
                                    - cell as u8;
                            if cell {
                                neighbours == 2 || neighbours == 3
                            }
                            else {
                                neighbours == 3
                            }
                        })
                        .collect()
                })
                .collect()
        })
        .collect()
}

fn next_generation_part2(cells: &[Vec<Vec<Vec<bool>>>]) -> Vec<Vec<Vec<Vec<bool>>>> {
    let x = cells[0][0][0].len() as isize;
    let y = cells[0][0].len() as isize;
    let z = cells[0].len() as isize;
    let w = cells.len() as isize;
    (-1..=w)
        .map(|i| {
            (-1..=z)
                .map(|j| {
                    (-1..=y)
                        .map(|k| {
                            (-1..=x)
                                .map(|l| {
                                    let cell = (|| {
                                        Some(
                                            *cells
                                                .get(i as usize)?
                                                .get(j as usize)?
                                                .get(k as usize)?
                                                .get(l as usize)?,
                                        )
                                    })()
                                    .unwrap_or(false);
                                    let neighbours = iproduct!(
                                        (i - 1)..=(i + 1),
                                        (j - 1)..=(j + 1),
                                        (k - 1)..=(k + 1),
                                        (l - 1)..=(l + 1)
                                    )
                                    .filter_map(|(i, j, k, l)| {
                                        Some(
                                            *cells
                                                .get(i as usize)?
                                                .get(j as usize)?
                                                .get(k as usize)?
                                                .get(l as usize)?
                                                as u8,
                                        )
                                    })
                                    .sum::<u8>()
                                        - cell as u8;
                                    if cell {
                                        neighbours == 2 || neighbours == 3
                                    }
                                    else {
                                        neighbours == 3
                                    }
                                })
                                .collect()
                        })
                        .collect()
                })
                .collect()
        })
        .collect()
}

fn read_input(filename: impl AsRef<Path>) -> io::Result<Vec<Vec<Vec<bool>>>> {
    let file = File::open(filename)?;
    Ok(vec![BufReader::new(file)
        .lines()
        .map(|line| {
            let line = line?;
            Ok(line
                .strip_suffix(char::is_whitespace)
                .unwrap_or(&line)
                .chars()
                .map(|c| c == '#')
                .collect())
        })
        .collect::<io::Result<_>>()?])
}

fn main() -> io::Result<()> {
    let mut cells = read_input("input")?;
    for _ in 0..6 {
        cells = next_generation_part1(&cells);
    }
    println!(
        "{}",
        cells
            .into_iter()
            .map(|plane| plane
                .into_iter()
                .map(|row| row.into_iter().map(|cell| cell as u64).sum::<u64>())
                .sum::<u64>())
            .sum::<u64>()
    );

    let mut cells = vec![read_input("input")?];
    for _ in 0..6 {
        cells = next_generation_part2(&cells);
    }
    println!(
        "{}",
        cells
            .into_iter()
            .map(|cube| cube
                .into_iter()
                .map(|plane| plane
                    .into_iter()
                    .map(|row| row.into_iter().map(|cell| cell as u64).sum::<u64>())
                    .sum::<u64>())
                .sum::<u64>())
            .sum::<u64>()
    );

    Ok(())
}
