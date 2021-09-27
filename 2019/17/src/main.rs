use std::{
    collections::HashMap,
    error::Error,
    iter::once,
};

#[cfg(feature = "visualise")]
use std::{
    io::Write,
    time::Duration,
};

use itertools::Itertools;

use intcode::{
    Cell,
    Computer,
    IO,
};

type Scaffolding = HashMap<Point, Tile>;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct Point {
    x: i64,
    y: i64,
}

#[derive(Debug, PartialEq, Copy, Clone)]
enum Tile {
    Scaffold,
    Empty,
    Up,
    Down,
    Left,
    Right,
}
use Tile::*;

#[derive(Debug)]
struct InvalidTile;

impl TryFrom<Cell> for Tile {
    type Error = InvalidTile;

    fn try_from(cell: Cell) -> Result<Self, Self::Error> {
        Ok(match u8::try_from(cell).map_err(|_| InvalidTile)? as char {
            '#' => Scaffold,
            '.' => Empty,
            '^' => Up,
            'v' => Down,
            '<' => Left,
            '>' => Right,
            _ => return Err(InvalidTile),
        })
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
enum Step {
    Go(usize),
    TurnLeft,
    TurnRight,
}

impl Step {
    fn len(self) -> usize {
        match self {
            Step::Go(n) =>
                if n >= 10 {
                    2
                }
                else {
                    1
                },
            _ => 1,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Function {
    A,
    B,
    C,
}

impl Function {
    fn as_index(self) -> usize {
        use Function::*;
        match self {
            A => 0,
            B => 1,
            C => 2,
        }
    }
}

trait ToAscii {
    fn to_ascii(&self) -> String;
}

impl ToAscii for Step {
    fn to_ascii(&self) -> String {
        use Step::*;
        match self {
            TurnLeft => "L".into(),
            TurnRight => "R".into(),
            Go(n) => n.to_string(),
        }
    }
}

impl ToAscii for Function {
    fn to_ascii(&self) -> String {
        use Function::*;
        match self {
            A => "A".into(),
            B => "B".into(),
            C => "C".into(),
        }
    }
}

struct State<Iter: Iterator<Item = Cell>> {
    position: Point,
    scaffolding: Scaffolding,
    dust_collected: Option<Cell>,
    input: Iter,
}

/// FIXME: Apparently, this cannot be expressed as an associated function as
/// there is no way to name the type `State` is generic over.
fn new_state<IntoIter>(input: IntoIter) -> State<impl Iterator<Item = Cell>>
where
    IntoIter: IntoIterator<Item = u8>,
{
    State {
        position: Point { x: 0, y: 0 },
        scaffolding: Scaffolding::default(),
        dust_collected: None,
        input: input.into_iter().map(|x| x as Cell),
    }
}

impl<Iter: Iterator<Item = Cell>> State<Iter> {
    fn intersections(&self) -> impl Iterator<Item = Point> + '_ {
        self.scaffolding
            .keys()
            .filter(move |&&p| {
                neighbours(p).chain(once(p)).all(|n| {
                    self.scaffolding
                        .get(&n)
                        .map_or(false, |tile| tile == &Scaffold)
                })
            })
            .copied()
    }

    fn part1(&self) -> Cell {
        self.intersections().map(|Point { x, y }| x * y).sum()
    }

    fn part2(&self) -> String {
        #[derive(Copy, Clone, Debug)]
        enum Possibility {
            Main(Function),
            Function(Function),
        }

        impl Possibility {
            fn iter() -> impl Iterator<Item = Self> {
                use crate::Function::*;
                use Possibility::*;
                [
                    Function(A),
                    Function(B),
                    Function(C),
                    Main(A),
                    Main(B),
                    Main(C),
                ]
                .iter()
                .copied()
            }
        }

        fn expand<'a>(
            main: &'a [Function],
            functions: &'a [Vec<Step>; 3],
        ) -> impl Iterator<Item = Step> + 'a {
            main.iter()
                .flat_map(move |f| &functions[f.as_index()])
                .copied()
        }

        fn render(f: &[impl ToAscii]) -> String {
            f.iter().map(ToAscii::to_ascii).join(",")
        }

        fn go(
            i: usize,
            steps: &[Step],
            main: &mut Vec<Function>,
            functions: &mut [Vec<Step>; 3],
        ) -> Option<(Vec<Function>, [Vec<Step>; 3])> {
            // FIXME: Is this a false positive? Regardless, a `match` wouldn’t make the
            // code more readable here.
            #[allow(clippy::comparison_chain)]
            if i == steps.len() {
                return Some((main.clone(), functions.clone()));
            }
            else if i > steps.len() {
                return None;
            }

            for possibility in Possibility::iter() {
                use Possibility::*;
                let i_offset = match possibility {
                    Main(step) => {
                        if steps[i..].starts_with(&functions[step.as_index()]) && main.len() < 10 {
                            main.push(step);
                        }
                        else {
                            continue;
                        }
                        functions[step.as_index()].len()
                    }
                    Function(step) => {
                        functions[step.as_index()].push(steps[i]);
                        if functions[step.as_index()]
                            .iter()
                            .map(|step| step.len())
                            .sum::<usize>()
                            > 10
                            || expand(main, functions)
                                .zip(steps.iter())
                                .any(|(x, &y)| x != y)
                        {
                            functions[step.as_index()].pop();
                            continue;
                        }
                        main.iter().filter(|&&it| it == step).count()
                    }
                };
                let solution = go(i + i_offset, steps, main, functions);
                if let Some((main, functions)) = solution.as_ref() {
                    if expand(main, functions)
                        .zip(steps.iter())
                        .all(|(x, &y)| x == y)
                    {
                        return solution;
                    }
                }
                else {
                    match possibility {
                        Main(_) => {
                            main.pop();
                        }
                        Function(step) => {
                            functions[step.as_index()].pop();
                        }
                    };
                }
            }
            None
        }

        let mut robot = Robot::new(self.scaffolding.clone());
        let steps = robot.steps();

        let mut main = vec![Function::A];
        let mut functions = <[_; 3]>::default();
        let result = go(0, &steps, &mut main, &mut functions);

        let (main, [a, b, c]) = result.unwrap();

        #[cfg(feature = "visualise")]
        let visualise = "y".into();
        #[cfg(not(feature = "visualise"))]
        let visualise = "n".into();

        [
            render(&main),
            render(&a),
            render(&b),
            render(&c),
            visualise,
            "".into(),
        ]
        .join("\n")
    }
}

impl<Iter: Iterator<Item = Cell>> IO for State<Iter> {
    fn next_input(&mut self) -> Option<Cell> {
        self.input.next()
    }

    fn output(&mut self, cell: Cell) {
        #[cfg(feature = "visualise")]
        print!("{}", cell as u8 as char);
        #[cfg(feature = "visualise")]
        if is_newline(cell) && self.position.x == 0 {
            std::thread::sleep(Duration::from_millis(50));
            print!("\x1B[;H");
            std::io::stdout().flush().unwrap();
        }
        if is_newline(cell) {
            self.position = Point { x: 0, y: self.position.y + 1 };
        }
        else if let Ok(tile) = cell.try_into() {
            self.scaffolding.insert(self.position, tile);
            self.position = Point { x: self.position.x + 1, ..self.position };
        }
        else if !u8::try_from(cell).map(|x| x.is_ascii()).unwrap_or(false) {
            self.dust_collected = Some(cell);
        }
    }
}

/// FIXME: This is just a function (`steps`)
struct Robot {
    scaffolding: Scaffolding,
}

impl Robot {
    fn new(scaffolding: Scaffolding) -> Self {
        Robot { scaffolding }
    }

    fn position(&self) -> Point {
        *self
            .scaffolding
            .iter()
            .find(|(_, tile)| [Up, Down, Left, Right].contains(tile))
            .map(|(position, _)| position)
            .unwrap()
    }

    fn direction(&self) -> Tile {
        *self.scaffolding.get(&self.position()).unwrap()
    }

    fn steps(&mut self) -> Vec<Step> {
        let mut steps = Vec::new();
        loop {
            let mut n = 0;
            while self.can_move() {
                n += 1;
                self.move_forward();
            }
            if n != 0 {
                steps.push(Step::Go(n));
            }
            self.turn_left();
            if self.can_move() {
                steps.push(Step::TurnLeft);
            }
            else {
                self.turn_right();
                self.turn_right();
                if self.can_move() {
                    steps.push(Step::TurnRight);
                }
                else {
                    break steps;
                }
            }
        }
    }

    fn can_move(&self) -> bool {
        self.scaffolding
            .get(&self.next_position())
            .map(|&tile| tile == Scaffold)
            .unwrap_or(false)
    }

    fn next_position(&self) -> Point {
        let Point { x, y } = self.position();
        match self.direction() {
            Up => Point { x, y: y - 1 },
            Down => Point { x, y: y + 1 },
            Left => Point { x: x - 1, y },
            Right => Point { x: x + 1, y },
            _ => unreachable!(),
        }
    }

    fn move_forward(&mut self) {
        let next_position = self.next_position();
        let direction = self.direction();
        self.scaffolding.insert(self.position(), Scaffold);
        self.scaffolding.insert(next_position, direction);
    }

    fn turn_left(&mut self) {
        self.scaffolding.insert(
            self.position(),
            match self.direction() {
                Up => Left,
                Down => Right,
                Left => Down,
                Right => Up,
                _ => unreachable!(),
            },
        );
    }

    fn turn_right(&mut self) {
        self.scaffolding.insert(
            self.position(),
            match self.direction() {
                Up => Right,
                Down => Left,
                Left => Up,
                Right => Down,
                _ => unreachable!(),
            },
        );
    }
}

fn is_newline(cell: Cell) -> bool {
    cell == 10
}

fn neighbours(Point { x, y }: Point) -> impl Iterator<Item = Point> {
    [
        Point { x: x - 1, y },
        Point { x: x + 1, y },
        Point { x, y: y - 1 },
        Point { x, y: y + 1 },
    ]
    .into_iter()
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut state = new_state("".bytes());
    let mut computer = Computer::from_file("input", &mut state)?;

    #[cfg(feature = "visualise")]
    print!("\x1B[?25l\x1B[?1049h");

    computer.run();
    let solution_part_1 = state.part1();
    let part2_input = state.part2();

    #[cfg(feature = "visualise")]
    print!("\x1B[2J");

    let mut state = new_state(part2_input.bytes());
    let mut computer = Computer::from_file("input", &mut state)?;
    computer.memory[0] = 2;
    computer.run();
    let solution_part_2 = state.dust_collected.unwrap();

    #[cfg(feature = "visualise")]
    print!("\x1B[?25h\x1B[?1049l");

    println!("{}", solution_part_1);
    println!("{}", solution_part_2);

    Ok(())
}
