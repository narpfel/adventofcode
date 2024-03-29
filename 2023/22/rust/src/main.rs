use std::ops::Range;

ct_python::ct_python! {
    import sys
    sys.path.append("../python")
    import solution

    puzzle_input = [
        (tuple(start), tuple(end))
        for start, end in solution.read_input("input")
    ]
    print(f "const INPUT: &[(Point, Point)] = &{puzzle_input};")
}

type Coordinate = usize;
type Point = (Coordinate, Coordinate, Coordinate);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Brick {
    name: usize,
    moved: bool,
    start: Point,
    end: Point,
}

impl Brick {
    fn new(name: usize, start: Point, end: Point) -> Self {
        Self { name, moved: false, start, end }
    }

    fn drop(self) -> Self {
        Self {
            name: self.name,
            moved: true,
            start: (self.start.0, self.start.1, self.start.2 - 1),
            end: (self.end.0, self.end.1, self.end.2 - 1),
        }
    }

    fn blocks(&self) -> impl Iterator<Item = Point> {
        let start = self.start;
        let end = self.end;
        (start.0..end.0 + 1).flat_map(move |x| {
            (start.1..end.1 + 1).flat_map(move |y| (start.2..end.2 + 1).map(move |z| (x, y, z)))
        })
    }
}

fn settle(
    mut bricks: Vec<Brick>,
    x_range: Range<Coordinate>,
    y_range: Range<Coordinate>,
    z_range: Range<Coordinate>,
) -> Vec<Brick> {
    let xy_size = x_range.len() * y_range.len();
    let index = |(x, y, z)| z * xy_size + y * x_range.len() + x;

    let mut all_blocks = vec![false; x_range.len() * y_range.len() * z_range.len()];
    for y in y_range.clone() {
        for x in x_range.clone() {
            all_blocks[index((x, y, 0))] = true;
        }
    }

    bricks.iter_mut().for_each(|brick| loop {
        let moved = brick.drop();
        if moved.blocks().any(|block| all_blocks[index(block)]) {
            for block in brick.blocks() {
                all_blocks[index(block)] = true;
            }
            break;
        }
        else {
            *brick = moved;
        }
    });
    bricks
}

fn main() {
    let &min_x = INPUT.iter().map(|((x, _, _), _)| x).min().unwrap();
    let &max_x = INPUT.iter().map(|(_, (x, _, _))| x).max().unwrap();
    let &min_y = INPUT.iter().map(|((_, y, _), _)| y).min().unwrap();
    let &max_y = INPUT.iter().map(|(_, (_, y, _))| y).max().unwrap();
    let &min_z = INPUT.iter().map(|((_, _, z), _)| z).min().unwrap();
    let &max_z = INPUT.iter().map(|(_, (_, _, z))| z).max().unwrap();

    let x_range = min_x..max_x + 1;
    let y_range = min_y..max_y + 1;
    let z_range = min_z..max_z + 1;

    let bricks = {
        let mut bricks = INPUT
            .iter()
            .enumerate()
            .map(|(i, &(start, end))| Brick::new(i, start, end))
            .collect::<Vec<_>>();
        bricks.sort_by_key(|brick| brick.blocks().map(|(_, _, z)| z).min());
        bricks = settle(bricks, x_range.clone(), y_range.clone(), z_range.clone());
        for brick in &mut bricks {
            brick.moved = false;
        }
        bricks
    };

    let mut result_part_1 = 0_u64;
    let mut result_part_2 = 0_u64;

    for (i, _) in bricks.iter().enumerate() {
        let mut ith_brick_removed = bricks.clone();
        ith_brick_removed.remove(i);
        let settled = settle(
            ith_brick_removed,
            x_range.clone(),
            y_range.clone(),
            z_range.clone(),
        );
        let fallen_bricks = settled.iter().filter(|brick| brick.moved).count() as u64;

        result_part_1 += (fallen_bricks == 0) as u64;
        result_part_2 += fallen_bricks;
    }

    println!("{result_part_1}");
    println!("{result_part_2}");
}
