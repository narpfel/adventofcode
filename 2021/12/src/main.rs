use std::{
    collections::HashMap,
    fs::File,
    io::{
        self,
        BufRead,
        BufReader,
    },
    path::Path,
};

use itertools::Itertools;

fn dfs(
    cave_count: usize,
    adjecency: &[bool],
    is_small: &[bool],
    start: usize,
    end: usize,
    path: &mut Vec<usize>,
    allow_small_cave: &mut impl FnMut(&[usize], usize) -> bool,
) -> u64 {
    adjecency[path.last().unwrap() * cave_count..]
        .iter()
        .take(cave_count)
        .enumerate()
        .filter_map(|(cave, connected)| connected.then(|| cave))
        .filter_map(|cave| {
            if cave == end {
                Some(1)
            }
            else if cave == start || (is_small[cave] && !allow_small_cave(path, cave)) {
                None
            }
            else {
                path.push(cave.to_owned());
                let result = Some(dfs(
                    cave_count,
                    adjecency,
                    is_small,
                    start,
                    end,
                    path,
                    allow_small_cave,
                ));
                path.pop();
                result
            }
        })
        .sum()
}

#[allow(clippy::type_complexity)]
fn read_input(path: impl AsRef<Path>) -> io::Result<(usize, Vec<bool>, Vec<bool>, usize, usize)> {
    let mut caves = HashMap::new();
    let mut cave_count = 0usize;

    let file = File::open(path)?;
    let connections = BufReader::new(file)
        .lines()
        .map(|line| {
            line?
                .trim()
                .split('-')
                .map(|cave| {
                    *caves.entry(cave.to_owned()).or_insert_with(|| {
                        let idx = cave_count;
                        cave_count += 1;
                        idx
                    })
                })
                .collect_tuple()
                .ok_or_else(|| io::Error::new(io::ErrorKind::Other, "no parse"))
        })
        .collect::<io::Result<Vec<(_, _)>>>()?;

    let is_small = (0..cave_count)
        .map(|idx| {
            caves
                .iter()
                .find(|(_, i)| **i == idx)
                .unwrap()
                .0
                .chars()
                .next()
                .unwrap()
                .is_lowercase()
        })
        .collect();

    let mut adjecency = vec![false; cave_count * cave_count];
    for (start, end) in &connections {
        adjecency[start + end * cave_count] = true;
        adjecency[end + start * cave_count] = true;
    }

    Ok((
        cave_count,
        adjecency,
        is_small,
        caves["start"],
        caves["end"],
    ))
}

fn part_1(
    cave_count: usize,
    adjecency: &[bool],
    is_small: &[bool],
    start: usize,
    end: usize,
) -> u64 {
    dfs(
        cave_count,
        adjecency,
        is_small,
        start,
        end,
        &mut vec![start],
        &mut |path, cave| !path.contains(&cave),
    )
}

fn part_2(
    cave_count: usize,
    adjecency: &[bool],
    is_small: &[bool],
    start: usize,
    end: usize,
) -> u64 {
    let mut small_cave_counts = vec![0; cave_count];
    dfs(
        cave_count,
        adjecency,
        is_small,
        start,
        end,
        &mut vec![start],
        &mut |path, cave| {
            small_cave_counts.iter_mut().for_each(|count| *count = 0);
            for &c in path.iter().filter(|&&c| is_small[c]) {
                small_cave_counts[c] += 1;
            }
            small_cave_counts[cave] += 1;
            let mut twos = 0;

            for &count in &small_cave_counts {
                if count == 2 {
                    twos += 1;
                }
                if count > 2 {
                    return false;
                }
            }

            twos <= 1
        },
    )
}

#[cfg(test)]
mod tests {
    use super::{
        part_1,
        part_2,
        read_input,
    };

    #[test]
    fn test_part_1_1() {
        let (cave_count, adjecency, is_small, start, end) = read_input("input_test_1").unwrap();
        assert_eq!(part_1(cave_count, &adjecency, &is_small, start, end), 10);
    }

    #[test]
    fn test_part_1_2() {
        let (cave_count, adjecency, is_small, start, end) = read_input("input_test_2").unwrap();
        assert_eq!(part_1(cave_count, &adjecency, &is_small, start, end), 19);
    }

    #[test]
    fn test_part_1_3() {
        let (cave_count, adjecency, is_small, start, end) = read_input("input_test_3").unwrap();
        assert_eq!(part_1(cave_count, &adjecency, &is_small, start, end), 226);
    }

    #[test]
    fn test_part_2_1() {
        let (cave_count, adjecency, is_small, start, end) = read_input("input_test_1").unwrap();
        assert_eq!(part_2(cave_count, &adjecency, &is_small, start, end), 36);
    }

    #[test]
    fn test_part_2_2() {
        let (cave_count, adjecency, is_small, start, end) = read_input("input_test_2").unwrap();
        assert_eq!(part_2(cave_count, &adjecency, &is_small, start, end), 103);
    }

    #[test]
    fn test_part_2_3() {
        let (cave_count, adjecency, is_small, start, end) = read_input("input_test_3").unwrap();
        assert_eq!(part_2(cave_count, &adjecency, &is_small, start, end), 3509);
    }
}

fn main() -> io::Result<()> {
    let (cave_count, adjecency, is_small, start, end) = read_input("input")?;
    println!("{}", part_1(cave_count, &adjecency, &is_small, start, end));
    println!("{}", part_2(cave_count, &adjecency, &is_small, start, end));
    Ok(())
}
