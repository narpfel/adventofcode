use std::collections::VecDeque;

use fnv::FnvHashMap;

enum Module {
    FlipFlop {
        name: &'static str,
        state: bool,
        targets: &'static [&'static str],
    },
    Conjunction {
        name: &'static str,
        inputs: FnvHashMap<&'static str, bool>,
        targets: &'static [&'static str],
        first_true_activation: Option<u64>,
        activation_difference: Option<u64>,
    },
    Broadcaster {
        name: &'static str,
        targets: &'static [&'static str],
    },
}

impl Module {
    fn flipflop(name: &'static str, targets: &'static [&'static str]) -> Module {
        Module::FlipFlop { name, state: false, targets }
    }

    fn conjunction(
        name: &'static str,
        targets: &'static [&'static str],
        inputs: &'static [&'static str],
    ) -> Module {
        Module::Conjunction {
            name,
            inputs: inputs.iter().map(|&s| (s, false)).collect(),
            targets,
            first_true_activation: None,
            activation_difference: None,
        }
    }

    fn broadcaster(name: &'static str, targets: &'static [&'static str]) -> Module {
        Module::Broadcaster { name, targets }
    }

    fn recv(
        &mut self,
        time: u64,
        sender: &'static str,
        pulse: bool,
        signals: &mut impl Extend<(&'static str, &'static str, bool)>,
    ) {
        match self {
            Module::FlipFlop { name, state, targets } =>
                if !pulse {
                    *state = !*state;
                    signals.extend(targets.iter().map(|&tgt| (*name, tgt, *state)))
                },
            Module::Conjunction {
                name,
                inputs,
                targets,
                first_true_activation,
                activation_difference,
            } => {
                *inputs.get_mut(sender).unwrap() = pulse;
                let output = !inputs.values().all(|&b| b);
                if output {
                    if first_true_activation.is_none() {
                        *first_true_activation = Some(time);
                    }
                    else if activation_difference.is_none() {
                        *activation_difference = Some(time - first_true_activation.unwrap());
                    }
                }
                signals.extend(targets.iter().map(|&tgt| (*name, tgt, output)))
            }
            Module::Broadcaster { name, targets } =>
                signals.extend(targets.iter().map(|&tgt| (*name, tgt, pulse))),
        }
    }
}

fn main() {
    ct_python::ct_python! {
        import sys
        sys.path.append("../python")
        import solution
        modules = solution.read_input("input")

        def string(s):
            return f "\"{s}\""

        print("let modules = [")

        for module in modules:
            args = [f "&[{', '.join(string(target) for target in module.targets)}]"]

            if module.type == "conjunction":
                inputs = [m.name for m in modules if module.name in m.targets]
                args.append(f "&[{', '.join(string(input) for input in inputs)}]")

            print(
                f "({string(module.name)}, Module::{module.type}"
                f "({string(module.name)}, {', '.join(args)})),",
            )

        print("];")
        rx_dep, = (module.name for module in modules if "rx" in module.targets)
        rx_dep_deps = [module.name for module in modules if rx_dep in module.targets]
        print(f "let rx_dep_deps = [{', '.join(string(dep) for dep in rx_dep_deps)}];")
    }

    let mut modules = FnvHashMap::from(modules.into_iter().collect());

    let mut sent = [0_u64; 2];
    let mut signals = VecDeque::new();
    for i in 1_u64.. {
        signals.push_back(("button", "broadcaster", false));

        while let Some((sender, target, signal)) = signals.pop_front() {
            sent[signal as usize] += 1;
            if let Some(module) = modules.get_mut(target) {
                module.recv(i, sender, signal, &mut signals);
            }
        }

        if i == 1_000 {
            println!("{}", sent.iter().product::<u64>());
        }

        if rx_dep_deps.iter().all(|dep| {
            matches!(
                modules.get(dep),
                Some(Module::Conjunction { activation_difference: Some(_), .. }),
            )
        }) {
            let result = rx_dep_deps
                .iter()
                .filter_map(|dep| match modules.get(dep) {
                    Some(Module::Conjunction { activation_difference: Some(diff), .. }) =>
                        Some(diff),
                    _ => unreachable!(),
                })
                // FIXME: this should be LCM, but all numbers are prime
                .product::<u64>();
            println!("{result}");
            break;
        }
    }
}
