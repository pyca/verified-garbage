use super::Searcher;
use crate::arch::dispatch::dsa::vg_dsa_parameter_search_init_auto;
use alloc::vec;

const WIDTHS: [(usize, usize); 3] = [(128, 20), (256, 32), (384, 32)];

#[test]
fn init_words() {
    let dit = crate::dit::public(crate::dit::Why::Test);
    for (p_len, _) in WIDTHS {
        let mut state = [7u64; 4];
        // SAFETY: four writable words.
        assert_eq!(
            unsafe { vg_dsa_parameter_search_init_auto(dit, &mut state, p_len) },
            1
        );
        let p = p_len as u64;
        assert_eq!(state, [4096, p, 32769 * p, 512 * p]);
    }
    for p_len in [0, 20, 127, 192, 512] {
        let mut state = [7u64; 4];
        // SAFETY: four writable words.
        assert_eq!(
            unsafe { vg_dsa_parameter_search_init_auto(dit, &mut state, p_len) },
            0
        );
        assert_eq!(state, [0; 4]);
    }
}

/// The search on an empty tape asks for the first tape, and (at 1024 bits)
/// on a tape of 0x02 octets, whose seeds' q are divisible by 3, rejects every
/// seed: with one seed allowed it is exhausted after consuming one seed.
#[test]
fn steps() {
    let dit = crate::dit::public(crate::dit::Why::Test);
    for (p_len, q_len) in WIDTHS {
        let mut s = Searcher::new(dit, p_len, q_len);
        s.packed.fill(0xa5);
        assert_eq!(s.run(dit, &[]), (0, 0));
        assert_eq!(s.state[3], 512 * p_len as u64);
        assert!(s.packed.iter().all(|&b| b == 0));
        if p_len != 128 {
            continue;
        }
        s.state[0] = 1;
        let tape = vec![2u8; 2 * q_len];
        assert_eq!(s.run(dit, &tape), (3, q_len));
        assert_eq!(s.state, [0, p_len as u64, 32769 * p_len as u64, 0]);
    }
}
