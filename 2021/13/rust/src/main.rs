use std::collections::HashSet;
use std::error::Error;
use std::fs;

#[derive(Debug)]
enum Fold {
    X(u64),
    Y(u64),
}

impl Fold {
    fn apply(&self, dots: &mut [(u64, u64)]) {
        for (x, y) in dots {
            match self {
                Fold::X(axis) if *x > *axis => *x = 2 * axis - *x,
                Fold::Y(axis) if *y > *axis => *y = 2 * axis - *y,
                _ => (),
            }
        }
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let input = fs::read_to_string("input")?;
    let [dots, folds] = &input.split("\n\n").collect::<Vec<_>>()[..]
    else {
        return Err("invalid input".into());
    };
    let mut dots = dots
        .lines()
        .map(|line| {
            let mut numbers = line.trim().split(',').map(str::parse::<u64>);
            if let (Some(x), Some(y), None) = (numbers.next(), numbers.next(), numbers.next()) {
                Ok((x?, y?))
            }
            else {
                Err("invalid input".into())
            }
        })
        .collect::<Result<Vec<_>, Box<dyn Error>>>()?;

    let folds = folds
        .lines()
        .map(|line| {
            let mut fold = line.split_whitespace().last()?.split('=');
            match (
                fold.next(),
                fold.next()
                    .map(str::parse::<u64>)
                    .transpose()
                    .ok()
                    .flatten(),
                fold.next(),
            ) {
                (Some("x"), Some(axis), None) => Some(Fold::X(axis)),
                (Some("y"), Some(axis), None) => Some(Fold::Y(axis)),
                _ => None,
            }
        })
        .collect::<Option<Vec<_>>>()
        .ok_or("invalid input")?;

    folds[0].apply(&mut dots);
    println!("{}", dots.iter().collect::<HashSet<_>>().len());

    folds[1..].iter().for_each(|fold| fold.apply(&mut dots));

    let size_x = dots.iter().map(|(x, _)| x).max().ok_or("empty dots")? + 1;
    let size_y = dots.iter().map(|(_, y)| y).max().ok_or("empty dots")? + 1;

    let mut paper = vec![vec![false; size_x as _]; size_y as _];
    for (x, y) in dots {
        paper[y as usize][x as usize] = true;
    }

    for line in paper {
        for cell in line {
            print!("{}", if cell { '\u{2588}' } else { ' ' });
        }
        println!();
    }

    Ok(())
}
