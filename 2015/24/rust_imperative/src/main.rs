use std::fs::read_to_string;

use std::num::Wrapping;

type Value = u8;

fn weight(xs: &[Value]) -> u64 {
    xs.into_iter().map(|&v| v as u64).sum()
}

fn calculate_weight_and_quantum_entanglement(indices: &[usize], weights: &[Value]) -> (u64, u64) {
    let mut total_weight = 0;
    let mut quantum_entanglement = Wrapping(1);
    for &index in indices {
        let weight = weights[index] as u64;
        total_weight += weight;
        quantum_entanglement *= Wrapping(weight);
    }
    (total_weight, quantum_entanglement.0)
}

fn find_best_solution_of_length(target_weight: u64, weights: &[Value], r: usize) -> u64 {
    let n = weights.len();
    let mut indices: Vec<_> = (0..r).collect();
    let mut min_quantum_entanglement = std::u64::MAX;

    // Moving this to the top of the loop increases run time by ~1.7 s (17 %).
    let (w, q) = calculate_weight_and_quantum_entanglement(&indices, weights);
    if w == target_weight && min_quantum_entanglement > q {
        min_quantum_entanglement = q;
    }

    loop {
        let mut i = r - 1;

        while indices[i] == i + n - r {
            if i > 0 {
                i -= 1;
            }
            else {
                return min_quantum_entanglement;
            }
        }
        indices[i] += 1;
        // writing this a a `for` loop increases run time by ~ 0.5 s (5 %).
        let mut j = i + 1;
        while j < r {
            indices[j] = indices[j - 1] + 1;
            j += 1;
        }

        let (w, q) = calculate_weight_and_quantum_entanglement(&indices, weights);
        if w == target_weight && min_quantum_entanglement > q {
            min_quantum_entanglement = q;
        }
    }
}

fn solve(target_weight: u64, weights: &[Value]) -> u64 {
    let mut min_quantum_entanglement = std::u64::MAX;
    for r in 1..weights.len() + 1 {
        let q = find_best_solution_of_length(target_weight, weights, r);
        if q < min_quantum_entanglement {
            min_quantum_entanglement = q;
        }
    }
    min_quantum_entanglement
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input: Vec<Value> = read_to_string("input")?
        .lines()
        .map(str::parse)
        .collect::<Result<_, _>>()?;

    let part1 = weight(&input) / 3;
    let part2 = weight(&input) / 4;
    println!("{}", solve(part1, &input));
    println!("{}", solve(part2, &input));
    Ok(())
}
