//! Reports the features usable by the library, including OS register-state support.

#[allow(dead_code)]
#[path = "../src/cpu.rs"]
mod cpu;

fn main() {
    let features = cpu::detected();
    println!(
        "{}",
        cpu::NAMES
            .iter()
            .enumerate()
            .filter(|(i, _)| features.0 & (1 << i) != 0)
            .map(|(_, name)| *name)
            .collect::<Vec<_>>()
            .join(",")
    );
}
