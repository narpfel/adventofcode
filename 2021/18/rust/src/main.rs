type Number = Vec<(u8, u8)>;

fn parse(number: &str) -> Number {
    let mut flat_number = Number::new();
    let mut level = 0_u8;
    for c in number.chars() {
        match c {
            '[' => level += 1,
            c if c.is_ascii_digit() => flat_number.push((c.to_digit(10).unwrap() as u8, level - 1)),
            ']' => level -= 1,
            ',' => (),
            _ => unreachable!(),
        }
    }
    flat_number
}

fn reduce_step_explode(mut number: Number) -> (bool, Number) {
    let mut changed = false;
    let mut i = 0;
    while i < number.len() {
        let (x, level) = number[i];
        if level >= 4 {
            debug_assert_eq!(level, 4);
            changed = true;

            let (y, other_level) = number[i + 1];
            debug_assert_eq!(other_level, 4);

            if i > 0 {
                number[i - 1].0 += x;
            }
            if i < number.len() - 2 {
                number[i + 2].0 += y;
            }

            number[i] = (0, 3);
            number.remove(i + 1);
        }
        else {
            i += 1;
        }
    }
    (changed, number)
}

fn reduce_step_split(mut number: Number) -> (bool, Number) {
    for i in 0..number.len() {
        let (x, level) = number[i];
        if x >= 10 {
            number[i] = (x / 2, level + 1);
            number.insert(i + 1, (x.div_ceil(2), level + 1));
            return (true, number);
        }
    }
    (false, number)
}

fn reduce_step(number: Number) -> (bool, Number) {
    let (changed, number) = reduce_step_explode(number);
    if !changed {
        reduce_step_split(number)
    }
    else {
        (changed, number)
    }
}

fn reduce(mut number: Number) -> Number {
    loop {
        let (changed, new_number) = reduce_step(number);
        if !changed {
            return new_number;
        }
        number = new_number;
    }
}

fn add(a: &Number, b: &Number) -> Number {
    reduce(
        a.iter()
            .chain(b)
            .map(|(x, level)| (*x, level + 1))
            .collect(),
    )
}

fn magnitude(number: Number) -> u64 {
    let mut magnitude_stack = vec![];
    let mut lengths = vec![0];

    for (x, level) in number {
        let level = level + 1;
        while lengths.len() > level as _ || *lengths.last().unwrap() == 2 {
            let r = magnitude_stack.pop().unwrap();
            let l = magnitude_stack.pop().unwrap();
            magnitude_stack.push(3 * l + 2 * r);
            lengths.pop();
        }
        while lengths.len() < level as _ {
            *lengths.last_mut().unwrap() += 1;
            lengths.push(0);
        }
        magnitude_stack.push(x as u64);
        *lengths.last_mut().unwrap() += 1;
    }

    for _ in lengths {
        let r = magnitude_stack.pop().unwrap();
        let l = magnitude_stack.pop().unwrap();
        magnitude_stack.push(3 * l + 2 * r);
    }

    debug_assert!(magnitude_stack.len() == 1);
    magnitude_stack[0]
}

fn main() -> std::io::Result<()> {
    let input = std::fs::read_to_string("input")?;
    let numbers = input.lines().map(str::trim).map(parse).collect::<Vec<_>>();

    let result = numbers
        .iter()
        .skip(1)
        .fold(numbers[0].clone(), |a, b| add(&a, b));
    println!("{}", magnitude(result));

    let max = numbers
        .iter()
        .enumerate()
        .flat_map(|(i, a)| numbers[i + 1..].iter().map(move |b| (a, b)))
        .flat_map(|(a, b)| [add(a, b), add(b, a)])
        .map(magnitude)
        .max()
        .unwrap();
    println!("{}", max);

    Ok(())
}
