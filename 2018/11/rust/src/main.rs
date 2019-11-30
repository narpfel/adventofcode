#![feature(box_syntax)]

const GRID_SIZE: usize = 300;

const INPUT: i64 = 7672;

type Grid = Box<[[i64; GRID_SIZE + 1]; GRID_SIZE + 1]>;

struct Window {
    x: usize,
    y: usize,
    window_size: usize,
    total_power: i64,
}

fn power_level(x: usize, y: usize, serial_number: i64) -> i64 {
    let rack_id = x as i64 + 10;
    ((((rack_id * y as i64 + serial_number) * rack_id) / 100) % 10) - 5
}

fn calculate_grid(serial_number: i64) -> Grid {
    let mut grid = box [[0; GRID_SIZE + 1]; GRID_SIZE + 1];
    for (y, line) in grid.iter_mut().enumerate() {
        for (x, fuel_cell) in line.iter_mut().enumerate() {
            *fuel_cell = power_level(x, y, serial_number);
        }
    }
    grid
}

fn precompute_sums(grid: &mut Grid) {
    for line in grid.iter_mut() {
        for x in 1..line.len() {
            line[x] += line[x - 1];
        }
    }
    for y in 1..grid.len() {
        for x in 0..grid[y].len() {
            grid[y][x] += grid[y - 1][x];
        }
    }
}

fn windowed<'a>(grid: &'a Grid, window_size: usize) -> impl Iterator<Item=Window> + 'a {
    let y = grid.len();
    let x = grid[0].len();
    (1..x - window_size)
        .flat_map(move |i|
            (1..y - window_size)
            .map(move |j| {
                let a = grid[j][i];
                let b = grid[j][i + window_size];
                let c = grid[j + window_size][i + window_size];
                let d = grid[j + window_size][i];
                let power_level = c + a - d - b;
                Window { x: i + 1, y: j + 1, window_size, total_power: power_level }
            })
        )
}

fn solve(power_levels: &Grid, window_sizes: impl Iterator<Item=usize>) -> Window {
    window_sizes
        .flat_map(|window_size| windowed(power_levels, window_size))
        .max_by_key(|window| window.total_power)
        .unwrap()
}

fn main() {
    let power_levels = {
        let mut ps = calculate_grid(INPUT);
        precompute_sums(&mut ps);
        ps
    };
    let part1 = solve(&power_levels, std::iter::once(3));
    println!("{},{}", part1.x, part1.y);
    let part2 = solve(&power_levels, 1..GRID_SIZE + 1);
    println!("{},{},{}", part2.x, part2.y, part2.window_size);
}
