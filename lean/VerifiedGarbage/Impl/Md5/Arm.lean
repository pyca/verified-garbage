module

public import VerifiedGarbage.Spec.Md5
public import VerifiedGarbage.TCB.Arm.Isa

/-!
# MD5 compression function: ARMv7 implementation

`vg_md5_compress(state = r0, blocks = r1, n = r2, scratch = r3)`.

The same structure as the AArch64 implementation:
* The MD buffer `A, B, C, D` lives in `r4`–`r7`, from one block to the next;
  the fully unrolled operations rename them: in operation `t`, word `k` of
  the specification's `(a, b, c, d)` is in `var t k`.
* Each word `X[k]` is loaded from the block (a little-endian 32-bit load)
  when it is added, so there is no message schedule to keep.
* `b`, the result of the operation before, is the last thing an operation
  waits for: `X[k]` and the constant `T[t+1]` are added to `a` first, and then
  the auxiliary function's value, in as few operations of `b` as it has.
  `G(b, c, d)` is added as its two terms, which have no bit in common,
  `c ∧ ¬d` and then `b ∧ d`; and `I(b, c, d) = ¬(c ⊕ (d ∧ ¬b))`, so
  `a + I(b, c, d) = a - (c ⊕ (d ∧ ¬b)) - 1`, the `1` taken off the constant.
* The rotation and the final addition are one instruction,
  `add a, b, a, ror #(32 - s)`.
* The one temporary is `r12`. `r4`–`r7` are saved in `scratch[0..16)` and
  restored on exit; `r0` and `r3` are never written, and neither are
  `r8`–`r11` and `lr`.
* `r0`–`r3` (the pointers and the block count) are public; no address and
  no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Md5.Arm

open VG.Arm
open VG.Spec.Md5 (ks ss Ts)

/-- The registers holding the MD buffer. -/
def work : List Reg := [.r4, .r5, .r6, .r7]

/-- The register holding word `k` (`a = 0, …, d = 3`) at the start of operation `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 4 - t % 4) % 4) .r4

/-- The temporary: the word `X[k]`, then the constant, then the terms of the
auxiliary function. -/
def T : Reg := .r12

/-- What round `r`'s code leaves out of its function's value: `fn 3` adds
`I(b, c, d) + 1`. -/
def adj (r : Nat) : BitVec 32 := if r = 3 then 1 else 0

/-- `a := a + fn(b, c, d) + adj r`, the auxiliary function of round `r`, as
`F = ((c ⊕ d) ∧ b) ⊕ d`, `G = (c ∧ ¬d) + (b ∧ d)`, `H = (c ⊕ d) ⊕ b` and
`I = ¬(c ⊕ (d ∧ ¬b))`, whose sum with `a` and `1` is a subtraction. -/
def fn (r : Nat) (a b c d : Reg) : List Instr :=
  match r with
  | 0 => [.dp .eor T c (.reg d), .dp .and T T (.reg b), .dp .eor T T (.reg d),
      .dp .add a a (.reg T)]
  | 1 => [.dp .bic T c (.reg d), .dp .add a a (.reg T), .dp .and T b (.reg d),
      .dp .add a a (.reg T)]
  | 2 => [.dp .eor T c (.reg d), .dp .eor T T (.reg b), .dp .add a a (.reg T)]
  | _ => [.dp .bic T d (.reg b), .dp .eor T T (.reg c), .dp .sub a a (.reg T)]

/-- The rotation amount `s` of operation `t`. -/
def rot (t : Nat) : Nat := (ss.getD (t / 16) []).getD (t % 4) 0

/-- The constant of operation `t`, less what its function's code adds. -/
def konst (t : Nat) : BitVec 32 := Ts.getD t 0 - adj (t / 16)

/-- Operation `t`: `a := b + ((a + X[k] + T[t+1] + fn(b,c,d)) <<< s)`, the
rotation as a right rotation by `32 - s`. -/
def step (t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let c := var t 2; let d := var t 3
  ([.ldr T .r1 (4 * ks.getD t 0),
    .dp .add a a (.reg T),
    .movw T ((konst t).extractLsb' 0 16),
    .movt T ((konst t).extractLsb' 16 16),
    .dp .add a a (.reg T)] : List Instr) ++
  (fn (t / 16) a b c d ++ ([.dp .add a b (.shifted a .ror (32 - rot t))] : List Instr))

/-- Operations `0 … n-1`. -/
def steps : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (steps n) (.block (step n))

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) := [(.r4, 0), (.r5, 4), (.r6, 8), (.r7, 12)]

def save : List Instr := saved.map fun (r, d) => .str r .r3 d
def restore : List Instr := saved.map fun (r, d) => .ldr r .r3 d

/-- Load the MD buffer (`64 % 4 = 0`, so the words are in the same registers
after the 64 operations). -/
def load : List Instr := (List.range 4).map fun k => .ldr (var 0 k) .r0 (4 * k)

/-- Add the MD buffer into the words and store the result. -/
def update : List Instr :=
  (List.range 4).flatMap fun k => [
    .ldr T .r0 (4 * k),
    .dp .add (var 0 k) (var 0 k) (.reg T),
    .str (var 0 k) .r0 (4 * k)]

/-- Advance to the next block and decrement the count (setting Z when it hits 0). -/
def advance : List Instr := [.dp .add .r1 .r1 (.imm 64), .subs .r2 .r2 (.imm 1)]

/-- One block. -/
def body : Prog isa := .seq (steps 64) (.block (update ++ advance))

def compress : Prog isa :=
  .seq (.block (save ++ ([.cmp .r2 (.imm 0)] : List Instr)))
    (.seq (.ite .eq (.block []) (.seq (.block load) (.loop body .ne))) (.block restore))

end VG.Impl.Md5.Arm
