use std::cell::Cell;
use std::error::Error;
use std::rc::Rc;

use intcode::Computer;
use intcode::IO;

struct State {
    input_queue: std::sync::mpsc::Receiver<intcode::Cell>,
    output_queues: Vec<std::sync::mpsc::Sender<intcode::Cell>>,
    output_buffer: Vec<intcode::Cell>,
    address_255: Rc<Cell<Option<intcode::Cell>>>,
}

impl IO for State {
    fn next_input(&mut self) -> Option<intcode::Cell> {
        Some(self.input_queue.try_recv().unwrap_or(-1))
    }

    fn output(&mut self, value: intcode::Cell) {
        self.output_buffer.push(value);
        if self.output_buffer.len() == 3 {
            let target_address = usize::try_from(self.output_buffer[0]).unwrap();
            if target_address == 255 {
                self.address_255.set(Some(self.output_buffer[2]));
                return;
            }
            let target = &mut self.output_queues[target_address];
            target.send(self.output_buffer[1]).unwrap();
            target.send(self.output_buffer[2]).unwrap();
            self.output_buffer.clear();
        }
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let (senders, receivers): (Vec<_>, Vec<_>) =
        (0..50).map(|_| std::sync::mpsc::channel()).unzip();
    let address_255 = Rc::new(Cell::new(None));

    let mut states: Vec<_> = receivers
        .into_iter()
        .enumerate()
        .map(|(i, receiver)| {
            senders[i].send(i as intcode::Cell).unwrap();
            State {
                input_queue: receiver,
                output_queues: senders.clone(),
                output_buffer: Vec::new(),
                address_255: Rc::clone(&address_255),
            }
        })
        .collect();

    let mut computers = states
        .iter_mut()
        .map(|state| Computer::from_file("input", state))
        .collect::<Result<Vec<_>, _>>()?;

    loop {
        for computer in &mut computers {
            if let Some(result) = address_255.get() {
                println!("{result}");
                return Ok(());
            }
            computer.step().unwrap();
        }
    }
}
