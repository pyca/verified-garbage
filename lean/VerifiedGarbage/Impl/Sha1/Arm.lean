module

public import VerifiedGarbage.Spec.Sha1
public import VerifiedGarbage.TCB.Arm.Isa

/-!
# SHA-1 compression function: ARMv7 implementation

`vg_sha1_compress(state = r0, blocks = r1, n = r2, scratch = r3)`.

* The working variables `a … e` live in `r4`–`r8`, from one block to the
  next; the fully unrolled rounds rename them: in round `t`, variable `k` is
  in `var t k`.
* A round rotates only where it adds: `ROTL³⁰(b)` is not computed, and `c`,
  `d` and `e`, which are such values, are in their registers rotated left by
  2 (the registers hold `b` as it was), each use rotating its operand right
  by 2. `T = ROTL⁵(a) + f + e + Kₜ + Wₜ` is added up in `e`'s register, the
  new `a`: `Kₜ` and `Wₜ` first, and `ROTL⁵(a)`, the round before's result,
  last.
* `Kₜ`, the same for twenty rounds, is in `r11`.
* The message schedule is a 16-word window in `scratch[0..64)`, and its last
  three words are also in `r9`, `r10` and `lr` (`wreg`): `Wₜ` is computed
  in the register of `Wₜ₋₃`, and added from there.
* `Maj(b, c, d)` is added as its two terms, which have no bit in common:
  `b ∧ c` and `(b ⊕ c) ∧ d`.
* The callee-saved registers `r4`–`r11` and `lr` are saved in
  `scratch[64..100)` and restored on exit; `r0`–`r3` are never written.
* `r0`–`r3` (the pointers and the block count) are public; no address and no
  branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Sha1.Arm

open VG.Arm
open VG.Spec.Sha1 (K)

/-- `++`, grouping to the right (the kernel evaluates the code). -/
local infixr:65 " +++ " => HAppend.hAppend

/-- The registers holding the working variables. -/
def work : List Reg := [.r4, .r5, .r6, .r7, .r8]

/-- The register holding working variable `k` (`a = 0, …, e = 4`) at the start of round `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 5 - t % 5) % 5) .r4

/-- The temporary, and the register of `Kₜ`. -/
def T : Reg := .r12
def KR : Reg := .r11

/-- The registers of the last three words of the schedule. -/
def wregs : List Reg := [.r9, .r10, .lr]

/-- The register of `Wₜ`, which held `Wₜ₋₃`. -/
def wreg (t : Nat) : Reg := wregs.getD (t % 3) .r9

/-- The offset of `W[i mod 16]` in the scratch buffer. -/
def slot (i : Nat) : Nat := 4 * (i % 16)

/-- `Wₜ` into `wreg t` and its slot. The operations are in the order of the
specification, `Wₜ₋₃` being in the register; `ROTL¹` is a rotation right by
31. -/
def schedule (t : Nat) : List Instr :=
  let w := wreg t
  if t < 16 then [
    .ldr w .r1 (4 * t),
    .rev w w,
    .str w .r3 (slot t)]
  else [
    -- Wₜ₋₃ ⊕ Wₜ₋₈ ⊕ Wₜ₋₁₄ ⊕ Wₜ₋₁₆
    .ldr T .r3 (slot (t + 8)),
    .dp .eor w w (.reg T),
    .ldr T .r3 (slot (t + 2)),
    .dp .eor w w (.reg T),
    .ldr T .r3 (slot t),
    .dp .eor w w (.reg T),
    .mov w (.shifted w .ror 31),
    .str w .r3 (slot t)]

/-- The logical functions of §4.1.1. -/
inductive Fn | ch | parity | maj
  deriving DecidableEq

/-- The function `fₜ` of round `t`. -/
def fn (t : Nat) : Fn :=
  if t < 20 then .ch else if t < 40 then .parity else if t < 60 then .maj else .parity

/-- `e := e + f(b, c, d)`, with `c` and `d` rotated left by 2 in their
registers. -/
def fcode (f : Fn) (b c d e : Reg) : List Instr :=
  match f with
  | .ch => -- `Ch(b, c, d)`, as `((c ⊕ d) ∧ b) ⊕ d`
    [.dp .eor T c (.reg d), .dp .and T b (.shifted T .ror 2), .dp .eor T T (.shifted d .ror 2),
      .dp .add e e (.reg T)]
  | .parity => [.dp .eor T c (.reg d), .dp .eor T b (.shifted T .ror 2), .dp .add e e (.reg T)]
  | .maj => -- `Maj(b, c, d)`, as `(b ∧ c) + ((b ⊕ c) ∧ d)`
    [.dp .and T b (.shifted c .ror 2), .dp .add e e (.reg T), .dp .eor T b (.shifted c .ror 2),
      .dp .and T T (.shifted d .ror 2), .dp .add e e (.reg T)]

/-- `KR := Kₜ`, in the first round that has it. -/
def kload (t : Nat) : List Instr :=
  if t % 20 = 0 then [.movw KR ((K t).extractLsb' 0 16), .movt KR ((K t).extractLsb' 16 16)] else []

/-- Round `t`, with `Wₜ` in `wreg t` and `Kₜ` in `KR`: `e`'s register, where
`e` is rotated left by 2, becomes `T = Kₜ + e + Wₜ + f(b, c, d) + ROTL⁵(a)`,
the new `a`, and `b`'s register is the new `c`'s as it is. `ROTL⁵` is a
rotation right by 27. -/
def round (t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let c := var t 2; let d := var t 3; let e := var t 4
  ([.dp .add e KR (.shifted e .ror 2), .dp .add e e (.reg (wreg t))] : List Instr) +++
    fcode (fn t) b c d e +++ ([.dp .add e e (.shifted a .ror 27)] : List Instr)

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (kload n +++ schedule n +++ round n))

/-- The callee-saved registers, and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.r4, 64), (.r5, 68), (.r6, 72), (.r7, 76), (.r8, 80), (.r9, 84), (.r10, 88), (.r11, 92),
   (.lr, 96)]

def save : List Instr := saved.map fun (r, d) => .str r .r3 d
def restore : List Instr := saved.map fun (r, d) => .ldr r .r3 d

/-- Load the hash value (`80 % 5 = 0`, so the variables are in the same
registers after the 80 rounds). -/
def load : List Instr := (List.range 5).map fun k => .ldr (var 0 k) .r0 (4 * k)

/-- `c`, `d` and `e` rotated left by 2, as the rounds keep them. -/
def enter : List Instr := [2, 3, 4].map fun k => .mov (var 0 k) (.shifted (var 0 k) .ror 30)

/-- Add the hash value into the working variables (`c`, `d` and `e` rotated
right by 2) and store the result. -/
def update : List Instr :=
  (List.range 5).flatMap fun k => [
    .ldr T .r0 (4 * k),
    if k < 2 then .dp .add (var 0 k) (var 0 k) (.reg T)
    else .dp .add (var 0 k) T (.shifted (var 0 k) .ror 2),
    .str (var 0 k) .r0 (4 * k)]

/-- Advance to the next block and decrement the count (setting Z when it hits 0). -/
def advance : List Instr := [.dp .add .r1 .r1 (.imm 64), .subs .r2 .r2 (.imm 1)]

/-- One block. -/
def body : Prog isa := .seq (.block enter) (.seq (rounds 80) (.block (update ++ advance)))

def compress : Prog isa :=
  .seq (.block (save ++ ([.cmp .r2 (.imm 0)] : List Instr)))
    (.seq (.ite .eq (.block []) (.seq (.block load) (.loop body .ne))) (.block restore))

end VG.Impl.Sha1.Arm
