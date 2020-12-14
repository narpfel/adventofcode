use std::{
    cmp::min,
    fs::File,
    io::{
        self,
        BufRead,
        BufReader,
    },
    iter::repeat,
    path::Path,
};

use itertools::iproduct;

fn generation_part1(cells: &[Vec<bool>], chairs: &[Vec<bool>]) -> Vec<Vec<bool>> {
    let x = cells[0].len();
    let y = cells.len();
    cells
        .iter()
        .enumerate()
        .map(|(i, row)| {
            row.iter()
                .enumerate()
                .map(|(j, cell)| {
                    let neighbours = iproduct!(
                        i.saturating_sub(1)..min(i + 2, y),
                        j.saturating_sub(1)..min(j + 2, x)
                    )
                    .map(|(i, j)| cells[i][j] as u8)
                    .sum::<u8>()
                        - cells[i][j] as u8;
                    (cell | (!cell & (neighbours == 0)))
                        & !(cell & (neighbours >= 4))
                        & chairs[i][j]
                })
                .collect()
        })
        .collect()
}

fn diagonal_for<'a>(
    cells: &'a [Vec<bool>],
    chairs: &'a [Vec<bool>],
    is: impl Iterator<Item = usize> + 'a,
    js: impl Iterator<Item = usize> + 'a,
) -> impl Iterator<Item = i8> + 'a {
    is.zip(js)
        .map(move |(i, j)| cells[i][j] as i8 - (chairs[i][j] != cells[i][j]) as i8)
}

fn next_visible_is_alive(mut xs: impl Iterator<Item = i8>) -> u8 {
    xs.find(|&x| x != 0).map_or(false, |x| x == 1) as u8
}

fn generation_part2(cells: &[Vec<bool>], chairs: &[Vec<bool>]) -> Vec<Vec<bool>> {
    let x = cells[0].len();
    let y = cells.len();
    macro_rules! is_neighbour_visible_in_direction {
        ($is:expr, $js:expr) => {
            next_visible_is_alive(diagonal_for(&cells, &chairs, $is, $js))
        };
    }

    cells
        .iter()
        .enumerate()
        .map(|(i, row)| {
            row.iter()
                .enumerate()
                .map(|(j, cell)| {
                    let neighbours = is_neighbour_visible_in_direction!(repeat(i), (0..j).rev())
                        + is_neighbour_visible_in_direction!((0..i).rev(), (0..j).rev())
                        + is_neighbour_visible_in_direction!((0..i).rev(), repeat(j))
                        + is_neighbour_visible_in_direction!((0..i).rev(), j + 1..x)
                        + is_neighbour_visible_in_direction!(repeat(i), j + 1..x)
                        + is_neighbour_visible_in_direction!(i + 1..y, j + 1..x)
                        + is_neighbour_visible_in_direction!(i + 1..y, repeat(j))
                        + is_neighbour_visible_in_direction!(i + 1..y, (0..j).rev());
                    (cell | (!cell & (neighbours == 0)))
                        & !(cell & (neighbours >= 5))
                        & chairs[i][j]
                })
                .collect()
        })
        .collect()
}

fn find_steady_state(
    chairs: &[Vec<bool>],
    generation: impl Fn(&[Vec<bool>], &[Vec<bool>]) -> Vec<Vec<bool>>,
) -> Vec<Vec<bool>> {
    let mut cells = vec![vec![false; chairs[0].len()]; chairs.len()];
    loop {
        let new_cells = generation(&cells, &chairs);
        if new_cells == cells {
            break cells;
        }
        cells = new_cells;
    }
}

fn read_input(filename: impl AsRef<Path>) -> io::Result<Vec<Vec<bool>>> {
    let file = File::open(filename)?;
    BufReader::new(file)
        .lines()
        .map(|line| {
            let line = line?;
            Ok(line
                .strip_suffix(char::is_whitespace)
                .unwrap_or(&line)
                .chars()
                .map(|c| c == 'L')
                .collect())
        })
        .collect()
}

fn main() -> io::Result<()> {
    let chairs = read_input("input")?;
    println!(
        "{}",
        find_steady_state(&chairs, generation_part1)
            .into_iter()
            .map(|row| row.into_iter().map(|cell| cell as u64).sum::<u64>())
            .sum::<u64>()
    );
    println!(
        "{}",
        find_steady_state(&chairs, generation_part2)
            .into_iter()
            .map(|row| row.into_iter().map(|cell| cell as u64).sum::<u64>())
            .sum::<u64>()
    );
    Ok(())
}
