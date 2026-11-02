module

public import VerifiedGarbage.Impl.MillerRabin.RISCV64.Search
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32

/-!
# Trial division by the shared table of small primes on RISC-V

RSA's trial division (`Spec.RsaKeyGen.obviouslyComposite`) of the candidate
in array 0 of the Montgomery working space (`w` words at `a7`, `w` in `t0`),
by the first `n` entries of the table `VG_RSA_KEYGEN_TRIAL32`
(`Impl/RsaKeyGen/TrialTable32.lean`: each entry a prime `s` in its low half
and `−s⁻¹ mod 2³²` in its high half), as on PPC64LE
(`Impl/RsaKeyGen/PPC64LE/Trial.lean`):

* `digits`: the candidate's `2 w` digits of 32 bits, least significant
  first (`lwu`), each reduced into the accumulator `acc` by Montgomery's
  reduction by `2³²`: `X = acc + x`, `acc := (X + (X (−s⁻¹) mod 2³²) s) /
  2³²`, which keeps `acc < 2 s` and `acc 2^(32 j) ≡` the first `j` digits
  `(mod s)` (`Proof/RsaKeyGen/Trial32.lean`); the 64-bit products and sums
  never carry out, since `X < 2³³` and `q s < 2⁴⁶`.
* `entry`: one prime, its flag of `acc ∈ {0, s}` (`s` divides the candidate)
  in `a4`.
* `trial`: the entries from `s9`, `s10` of them, until one divides: `s10` is
  cleared on a hit, so the loop stops at the first divisor. The table's
  address is `lla`'s.

The candidate is public: the loop branches on it. It writes `a4`, `s0`–`s2`,
`s9`, `s10` and `t2`–`t6`.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.RISCV64.Trial

open VG VG.RISCV64
open VG.Impl.Bignum.RISCV64 (countLoop)

/-- One digit at `t3` into `acc` (`s0`), with `s` in `s1` and `−s⁻¹ mod 2³²`
in `s2`; `t3` advanced. It writes `s0`, `t2`, `t3` and `t4`. -/
def digit : List Instr :=
  [.load .w .t2 .t3 0, .add .t2 .t2 .s0, .mul .t4 .t2 .s2, .shift .sll .d .t4 .t4 32, .shift .srl .d .t4 .t4 32,
    .mul .t4 .t4 .s1, .add .t4 .t4 .t2, .shift .srl .d .s0 .t4 32, .addi .t3 .t3 4]

/-- The entry at `s9` into `s` (`s1`) and `−s⁻¹ mod 2³²` (`s2`), `acc := 0`,
and the digits' address and count (`2 w`). -/
def load : List Instr :=
  [.load .d .s1 .s9 0, .shift .srl .d .s2 .s1 32, .shift .sll .d .s1 .s1 32, .shift .srl .d .s1 .s1 32, .li .s0 0,
    .addi .t3 .a7 0, .shift .sll .d .t5 .t0 1]

/-- `a4 :=` 1 if `acc` is 0 or `s`, else 0; on to the next entry, `s10`
counted down, and cleared on a hit. -/
def finish : List Instr :=
  [.li .t2 1, .sltu .t4 .s0 .t2, .logic .xor .t6 .s0 .s1, .sltu .t6 .t6 .t2, .logic .or .a4 .t4 .t6,
    .addi .s9 .s9 8, .addi .s10 .s10 (-1), .addi .t2 .a4 (-1), .logic .and .s10 .s10 .t2]

/-- One entry: `a4 :=` its flag of dividing array 0. -/
def entry : Prog isa := .seq (.block load) (.seq (countLoop .t5 digit) (.block finish))

/-- The first `s10` entries (at least 1) from `s9`, until one divides
array 0: `a4 :=` 1 if one does, else 0. -/
def loop : Prog isa := .loop entry (.nonzero .s10)

/-- The table's address into `s9`, `s10 := ` header word `cnt`, and the
loop. -/
def trial (cnt : Nat) : Prog isa :=
  .seq (.block [.lla .s9 TrialTable32.symbol, MillerRabin.RISCV64.Search.ldh .s10 cnt]) loop

end VG.Impl.RsaKeyGen.RISCV64.Trial
