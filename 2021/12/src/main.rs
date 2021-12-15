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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Cave {
    name: String,
}

impl Cave {
    fn is_small(&self) -> bool {
        self.name.chars().next().map_or(false, char::is_lowercase)
    }
}

impl<S> From<S> for Cave
where
    S: Into<String>,
{
    fn from(name: S) -> Self {
        Self { name: name.into() }
    }
}

fn dfs(
    adjecency: &HashMap<Cave, Vec<Cave>>,
    path: Vec<Cave>,
    allow_small_cave: &impl Fn(&[Cave], &Cave) -> bool,
) -> u64 {
    adjecency[path.last().unwrap()]
        .iter()
        .filter_map(|cave| {
            if cave == &"end".into() {
                Some(1)
            }
            else if cave == &"start".into() || (cave.is_small() && !allow_small_cave(&path, cave))
            {
                None
            }
            else {
                let mut path = path.clone();
                path.push(cave.to_owned());
                Some(dfs(adjecency, path, allow_small_cave))
            }
        })
        .sum()
}

fn read_input(path: impl AsRef<Path>) -> io::Result<HashMap<Cave, Vec<Cave>>> {
    let file = File::open(path)?;
    let connections = BufReader::new(file)
        .lines()
        .map(|line| {
            line?
                .trim()
                .split('-')
                .map(str::to_owned)
                .collect_tuple()
                .ok_or_else(|| io::Error::new(io::ErrorKind::Other, "no parse"))
        })
        .collect::<io::Result<Vec<(_, _)>>>()?;

    let mut adjecency = HashMap::<Cave, Vec<Cave>>::default();
    for (start, end) in &connections {
        adjecency.entry(start.into()).or_default().push(end.into());
        adjecency.entry(end.into()).or_default().push(start.into());
    }

    Ok(adjecency)
}

fn part_1(adjecency: &HashMap<Cave, Vec<Cave>>) -> u64 {
    dfs(adjecency, vec!["start".into()], &|path, cave| {
        !path.contains(cave)
    })
}

fn part_2(adjecency: &HashMap<Cave, Vec<Cave>>) -> u64 {
    dfs(adjecency, vec!["start".into()], &|path, cave| {
        let mut small_cave_counts = path.iter().filter(|cave| cave.is_small()).counts();
        *small_cave_counts.entry(cave).or_default() += 1;
        let counts = small_cave_counts.into_values().counts();
        counts.get(&2).map_or(true, |&count| count <= 1) && counts.keys().max().unwrap_or(&0) <= &2
    })
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
        assert_eq!(part_1(&read_input("input_test_1").unwrap()), 10);
    }

    #[test]
    fn test_part_1_2() {
        assert_eq!(part_1(&read_input("input_test_2").unwrap()), 19);
    }

    #[test]
    fn test_part_1_3() {
        assert_eq!(part_1(&read_input("input_test_3").unwrap()), 226);
    }

    #[test]
    fn test_part_2_1() {
        assert_eq!(part_2(&read_input("input_test_1").unwrap()), 36);
    }

    #[test]
    fn test_part_2_2() {
        assert_eq!(part_2(&read_input("input_test_2").unwrap()), 103);
    }

    #[test]
    fn test_part_2_3() {
        assert_eq!(part_2(&read_input("input_test_3").unwrap()), 3509);
    }
}

fn main() -> io::Result<()> {
    let adjecency = read_input("input")?;
    println!("{}", part_1(&adjecency));
    println!("{}", part_2(&adjecency));
    Ok(())
}
