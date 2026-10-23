module

public import VerifiedGarbage.Spec.Md5
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# MD5 compression function: PPC64LE implementation

`vg_md5_compress(state = r3, blocks = r4, n = r5, scratch = r6)`.

The same structure as the AArch64 implementation (`Impl/Md5/AArch64.lean`):
* The MD buffer `A, B, C, D` lives in `r6`–`r9` (`scratch` is not used); the
  fully unrolled operations rename them: in operation `t`, word `k` of the
  specification's `(a, b, c, d)` is in `var t k`.
* Each word `X[k]` is loaded from the block (`lwz`, a little-endian 32-bit
  load) when it is added, so there is no message schedule to keep.
* Each operation is scheduled for latency: `b` is the word the previous
  operation computed, so everything that does not depend on it is computed
  first. `a + X[k] + T[t+1]` is added before the auxiliary function, and so
  are the terms of the auxiliary functions that do not depend on `b`: `G`
  is added as `(¬d ∧ c) + (d ∧ b)` (the two terms have no bit in common),
  and `F` and `H` start with `c ⊕ d`.
* The model has no `andc`/`orc`/`nor`, so `¬d` is `d ⊕ 0xffffffff`, with the
  constant in `r12`, set at the start of each block.
* The arithmetic is on whole registers: only their low 32 bits are the
  words, as the rotations (`rotrwi`, which reads the low word) and the
  stores (`stw`) use only those, and the low word of a sum, or of `and`,
  `or` and `xor`, depends only on the low words of the operands.
* Only volatile registers are used (`r0`, `r3`–`r12`), so nothing is saved.
* `r3`–`r5` (the pointers and the block count) are public; no address and
  no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Md5.PPC64LE

open VG.PPC64LE
open VG.Spec.Md5 (ks ss Ts)

/-- The registers holding the MD buffer. -/
def work : List Reg := [.r6, .r7, .r8, .r9]

/-- The register holding word `k` (`a = 0, …, d = 3`) at the start of operation `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 4 - t % 4) % 4) .r6

/-- Temporaries: `T0` holds the auxiliary function's terms, `T1` the word
`X[k]` and then the constant `T[t+1]`. -/
def T0 : Reg := .r10
def T1 : Reg := .r11

/-- The register holding `0xffffffff` (in its low word). -/
def Ones : Reg := .r12

/-- `a := a + fn(b, c, d)`, the auxiliary function of round `r`, using `T0`:
`F = ((c ⊕ d) ∧ b) ⊕ d`, `G = ((d ⊕ 0xffffffff) ∧ c) + (d ∧ b)`,
`H = (c ⊕ d) ⊕ b` and `I = ((d ⊕ 0xffffffff) ∨ b) ⊕ c`, each with the
instructions not depending on `b` first. -/
def fn (r : Nat) (a b c d : Reg) : List Instr :=
  match r with
  | 0 => [.logic .xor T0 c d, .logic .and T0 T0 b, .logic .xor T0 T0 d, .add a a T0]
  | 1 => [.logic .xor T0 d Ones, .logic .and T0 T0 c, .add a a T0, .logic .and T0 d b, .add a a T0]
  | 2 => [.logic .xor T0 c d, .logic .xor T0 T0 b, .add a a T0]
  | _ => [.logic .xor T0 d Ones, .logic .or T0 T0 b, .logic .xor T0 T0 c, .add a a T0]

/-- The rotation amount `s` of operation `t`. -/
def rot (t : Nat) : Nat := (ss.getD (t / 16) []).getD (t % 4) 0

/-- Operation `t`: `a := b + ((a + X[k] + T[t+1] + fn(b,c,d)) <<< s)`, the
rotation as a right rotation of the low word by `32 - s`. The constant is
built by `lis` of its high half and `ori` of its low half. -/
def step (t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let c := var t 2; let d := var t 3
  ([.load .w T1 .r4 (4 * ks.getD t 0),
    .add a a T1,
    .lis T1 ((Ts.getD t 0).extractLsb' 16 16),
    .ori T1 T1 ((Ts.getD t 0).extractLsb' 0 16),
    .add a a T1] : List Instr) ++
  fn (t / 16) a b c d ++
  ([.rotr .w a a (32 - rot t),
    .add a a b] : List Instr)

/-- Operations `0 … n-1`. -/
def steps : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (steps n) (.block (step n))

/-- `0xffffffff`. -/
def ones : BitVec 32 := 0xffffffff

/-- Load the MD buffer (`64 % 4 = 0`, so the words are in the same registers
after the 64 operations), and set `Ones`. -/
def load : List Instr :=
  (List.range 4).map (fun k => .load .w (var 0 k) .r3 (4 * k)) ++
  ([.lis Ones (ones.extractLsb' 16 16), .ori Ones Ones (ones.extractLsb' 0 16)] : List Instr)

/-- The registers the old MD buffer is loaded into before the addition. -/
def olds : List Reg := [T0, T1, Ones, .r0]

/-- Add the words into the MD buffer (loading all of it before storing any
of it), and store the result. -/
def update : List Instr :=
  (List.range 4).map (fun k => .load .w (olds.getD k T0) .r3 (4 * k)) ++
  (List.range 4).map (fun k => .add (var 0 k) (var 0 k) (olds.getD k T0)) ++
  (List.range 4).map (fun k => .store .w (var 0 k) .r3 (4 * k))

/-- Advance to the next block and decrement the count. -/
def advance : List Instr := [.addi .r4 .r4 64, .subi .r5 .r5 1]

/-- One block. -/
def body : Prog isa := .seq (.block load) (.seq (steps 64) (.block (update ++ advance)))

def compress : Prog isa :=
  .ite (.zero .d .r5) (.block []) (.loop body (.nonzero .d .r5))

end VG.Impl.Md5.PPC64LE
