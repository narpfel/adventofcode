use graph::{
    Point as _,
    ReadExt as _,
    Tile as _,
    World as _,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Tile {
    Start,
    Rock,
    Soil,
}

impl TryFrom<char> for Tile {
    type Error = char;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        match value {
            'S' => Ok(Tile::Start),
            '.' => Ok(Tile::Soil),
            '#' => Ok(Tile::Rock),
            _ => Err(value),
        }
    }
}

impl graph::Tile for Tile {
    fn is_walkable(&self) -> bool {
        matches!(self, Tile::Start | Tile::Soil)
    }
}

type Garden = graph::RectangularWorld<graph::CartesianPoint, Tile>;

fn part_1(garden: &Garden, n: u64) -> u64 {
    let start = garden.find(&Tile::Start).unwrap();
    let mut reachable_neighbours = vec![false; garden.len()];
    garden
        .walk_cells_breadth_first(&start)
        .filter_map(|path| {
            let len = (path.len() as u64).saturating_sub(1);
            if len < n && len % 2 == 0 {
                path.last().cloned()
            }
            else {
                None
            }
        })
        .flat_map(|p| p.neighbours())
        .filter(|p| garden.get(p).map_or(false, |t| t.is_walkable()))
        .for_each(|p| reachable_neighbours[garden.index(&p)] = true);
    reachable_neighbours.iter().map(|&b| b as u64).sum()
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let garden = Garden::from_file("input")?;
    println!("{}", part_1(&garden, 64));
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_part_1() -> Result<(), Box<dyn std::error::Error>> {
        let garden = Garden::from_file("input_test")?;
        assert_eq!(part_1(&garden, 6), 16);
        Ok(())
    }
}
