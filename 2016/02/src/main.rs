use std::cmp::max;
use std::cmp::min;
use std::fs::File;
use std::io;
use std::io::BufRead;
use std::io::BufReader;

fn read_instructions() -> io::Result<Vec<String>> {
    BufReader::new(File::open("input")?).lines().collect()
}

fn follow_instructions<F>(position: &mut [i8; 2], instructions: &str, validate: F)
where
    F: Fn(&mut [i8; 2], char),
{
    for c in instructions.chars() {
        match c {
            'U' => position[1] -= 1,
            'D' => position[1] += 1,
            'L' => position[0] -= 1,
            'R' => position[0] += 1,
            _ => unreachable!(),
        }
        validate(position, c);
    }
}

fn solve<F>(keypad: &[Vec<&str>], validate: F) -> io::Result<String>
where
    F: Fn(&mut [i8; 2], char),
{
    let mut position: [i8; 2] = [1, 1];
    Ok(read_instructions()?
        .iter()
        .map(|instructions| {
            follow_instructions(&mut position, instructions, &validate);
            let [x, y] = position;
            keypad[y as usize][x as usize]
        })
        .collect())
}

fn main() -> io::Result<()> {
    let keypad = vec![
        vec!["1", "2", "3"],
        vec!["4", "5", "6"],
        vec!["7", "8", "9"],
    ];
    println!(
        "{}",
        solve(&keypad, |position, _| {
            for p in position {
                *p = max(min(*p, 2), 0);
            }
        })?
    );

    let keypad = vec![
        vec![" ", " ", "1", " ", " "],
        vec![" ", "2", "3", "4", " "],
        vec!["5", "6", "7", "8", "9"],
        vec![" ", "A", "B", "C", " "],
        vec![" ", " ", "D", " ", " "],
    ];
    println!(
        "{}",
        solve(&keypad, |position, direction| {
            let mut validate_coordinate = |coordinate, other| {
                let other_position = position[other];
                let mut clamp = |min_value, max_value| {
                    position[coordinate] = max(min(position[coordinate], max_value), min_value);
                };
                match other_position {
                    0 | 4 => clamp(2, 2),
                    1 | 3 => clamp(1, 3),
                    2 => clamp(0, 4),
                    _ => unreachable!(),
                }
            };
            match direction {
                'U' | 'D' => validate_coordinate(1, 0),
                'L' | 'R' => validate_coordinate(0, 1),
                _ => unreachable!(),
            }
        })?
    );
    Ok(())
}
