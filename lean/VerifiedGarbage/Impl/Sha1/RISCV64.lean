module

public import VerifiedGarbage.Spec.Sha1
public import VerifiedGarbage.Impl.Words.RISCV64

/-!
# SHA-1 compression function: RISC-V implementation

`vg_sha1_compress(state = a0, blocks = a1, n = a2, scratch = a3)`.

The structure of the PPC64LE implementation (`Impl/Sha1/PPC64LE.lean`), for
RV64I, which has neither rotates nor byte-reversed loads, and faults on
misaligned accesses, with the idioms of SHA-256's RISC-V implementation
(`Impl/Sha256/RISCV64.lean`):
* The working variables `a … e` live in the low words of `t0`–`t4`; the
  fully unrolled rounds rename them: in round `t`, variable `k` is in
  `var t k`. The additions act on all 64 bits, so the high words hold
  carries and the sign extensions of the `*w` shifts, which the word shifts
  and the stores ignore.
* A rotation left by `n` is `slliw` by `n` and `srliw` by `32 - n`,
  combined by `or`, but in the rounds: each new `a` is kept doubled, as
  `x * (2³² + 1)` (`x` in both halves of its register), from which one
  `srli` leaves `ROTL⁵(x)` (as `a`, the next round) or `ROTL³⁰(x)` (as `b`,
  the round after) in the low word.
* `Kₜ` is in `KR`, loaded where it changes, and the rounds add `Wₜ` and `Kₜ`
  before `f(b, c, d)`, so that the additions depending on the previous round
  come last.
* The hash value (`state`, an array of `u32`) and the blocks are argument
  buffers, whose alignment the contract does not state, so they are read
  and written a byte at a time (`Impl/Words/RISCV64.lean`); the words of a
  block are big-endian.
* `scratch` is rounded up to a multiple of 8 (it has room to spare), so the
  16-word message schedule window in its first 64 bytes takes naturally
  aligned word accesses.
* Only temporaries are used, so nothing is saved.
* `a0`–`a3` (the pointers and the block count) are public; no address and
  no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Sha1.RISCV64

open VG.RISCV64
open VG.Impl.Words.RISCV64
open VG.Spec.Sha1 (K)

/-- The registers holding the working variables. -/
def work : List Reg := [.t0, .t1, .t2, .t3, .t4]

/-- The register holding working variable `k` (`a = 0, …, e = 4`) at the start of round `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 5 - t % 5) % 5) .t0

/-- Temporaries; `T0` holds `Wₜ` at the start of each round. -/
def T0 : Reg := .t5
def T1 : Reg := .t6
def T2 : Reg := .a4

/-- `Kₜ`. -/
def KR : Reg := .a5

/-- Round `scratch` up to a multiple of 8. -/
def align : List Instr := [.addi .a3 .a3 7, .logicImm .and .a3 .a3 (-8)]

/-- The offset of `W[i mod 16]` in the scratch buffer. -/
def slot (i : Nat) : Nat := 4 * (i % 16)

/-- `d := ROTLⁿ(x)` for a word `x`, with `tmp` clobbered (`0 < n < 32`; `d` may be `x`). -/
def rotl (d tmp x : Reg) (n : Nat) : List Instr :=
  [.shift .sll .w tmp x n, .shift .srl .w d x (32 - n), .logic .or d d tmp]

/-- Leave `Wₜ` in the low word of `T0` and in its slot. The operations are
in the order of the specification. -/
def schedule (t : Nat) : List Instr :=
  if t < 16 then loadBE32 T0 T1 .a1 (4 * t) ++ [.store .w T0 .a3 (slot t)]
  else
    -- Wₜ₋₃ ⊕ Wₜ₋₈ ⊕ Wₜ₋₁₄ ⊕ Wₜ₋₁₆
    [.load .w T0 .a3 (slot (t + 13)), .load .w T1 .a3 (slot (t + 8)), .logic .xor T0 T0 T1,
      .load .w T1 .a3 (slot (t + 2)), .logic .xor T0 T0 T1,
      .load .w T1 .a3 (slot t), .logic .xor T0 T0 T1] ++
    rotl T0 T1 T0 1 ++ [.store .w T0 .a3 (slot t)]

/-- The logical functions of §4.1.1. -/
inductive Fn | ch | parity | maj
  deriving DecidableEq

/-- The function `fₜ` of round `t`. -/
def fn (t : Nat) : Fn :=
  if t < 20 then .ch else if t < 40 then .parity else if t < 60 then .maj else .parity

/-- `T1 := f(b, c, d)` (using `T2` as well for `Maj`). -/
def fcode (f : Fn) (b c d : Reg) : List Instr :=
  match f with
  | .ch => -- `Ch(b, c, d)`, as `((c ⊕ d) ∧ b) ⊕ d`
    [.logic .xor T1 c d, .logic .and T1 T1 b, .logic .xor T1 T1 d]
  | .parity => [.logic .xor T1 b c, .logic .xor T1 T1 d]
  | .maj => -- `Maj(b, c, d)`, as `((b ∨ c) ∧ d) ∨ (b ∧ c)`
    [.logic .or T1 b c, .logic .and T1 T1 d, .logic .and T2 b c, .logic .or T1 T1 T2]

/-- The rest of round `t`, with `a` and `b` doubled: `e += ROTL⁵(a)`,
`b := ROTL³⁰(b)` (in its low word), and the new `a`, in `e`'s register,
doubled. -/
def tail (a b e : Reg) : List Instr :=
  [.shift .srl .d T1 a 27, .add e e T1, .shift .srl .d b b 2,
    .shift .sll .d e e 32, .shift .srl .d T1 e 32, .logic .or e e T1]

/-- Round `t`, with `Wₜ` in `T0` and `Kₜ` in `KR`: `T = ROTL⁵(a) + f + e + Kₜ + Wₜ`
is added up in `e`'s register (the new `a`), as `e + Wₜ + Kₜ + f + ROTL⁵(a)`,
and `b` becomes `ROTL³⁰(b)`. -/
def round (t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let c := var t 2; let d := var t 3; let e := var t 4
  ([.add e e T0, .add e e KR] : List Instr) ++ fcode (fn t) b c d ++ ([.add e e T1] : List Instr) ++
  tail a b e

/-- `KR := Kₜ` where it changes. -/
def kload (t : Nat) : List Instr := if t % 20 = 0 then li32 KR (K t) else []

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ kload n ++ round n))

/-- Load the hash value (`80 % 5 = 0`, so the variables are in the same
registers after the 80 rounds), `a` and `b` doubled. -/
def load : List Instr :=
  (List.range 5).flatMap (fun k => loadLE32 (var 0 k) T0 .a0 (4 * k)) ++
  [.shift .sll .d T1 (var 0 0) 32, .logic .or (var 0 0) (var 0 0) T1,
    .shift .sll .d T1 (var 0 1) 32, .logic .or (var 0 1) (var 0 1) T1]

/-- Add word `k` of the hash value into its working variable, and store the
result. -/
def updateW (k : Nat) : List Instr :=
  loadLE32 T0 T1 .a0 (4 * k) ++ [.add (var 0 k) (var 0 k) T0] ++ storeLE32 (var 0 k) T0 .a0 (4 * k)

/-- Advance to the next block and decrement the count. -/
def advance : List Instr := [.addi .a1 .a1 64, .addi .a2 .a2 (-1)]

/-- One block. -/
def body : Prog isa :=
  .seq (.block load) (.seq (rounds 80) (.block ((List.range 5).flatMap updateW ++ advance)))

/-- The blocks. -/
def blocks : Prog isa := .ite (.zero .a2) (.block []) (.loop body (.nonzero .a2))

def compress : Prog isa := .seq (.block align) blocks

end VG.Impl.Sha1.RISCV64
