module

public import VerifiedGarbage.Spec.Sha256
public import VerifiedGarbage.TCB.Arm.Isa

/-!
# SHA-256 compression function: ARMv7 implementation

`vg_sha256_compress(state = r0, blocks = r1, n = r2, scratch = r3)`.

* The working variables `a … h` live in `r4`–`r11`, from one block to the
  next; the fully unrolled rounds rename them: in round `t`, variable `k` is
  in `var t k`.
* The message schedule is a 16-word window in `scratch[0..64)`. `Wₜ` is
  added to `h` from the register the schedule leaves it in.
* The rotations of `Σ₀` and `Σ₁` are the rotated operands of two `eor`s and
  of the `add` of their value: `Σ₁(e) = ROTR⁶(e ⊕ ROTR⁵(e) ⊕ ROTR¹⁹(e))`.
* `Maj(a, b, c)` is `((b ⊕ c) ∧ (a ⊕ b)) ⊕ b`, and `a ⊕ b` is the next
  round's `b ⊕ c`: round `t` computes it in `mreg t`, its temporary until
  then, and finds `b ⊕ c` in `mreg (t + 1)`.
* `Wₜ` and `Kₜ`, which do not depend on the round before, are added to `h`
  first, and `Σ₁(e)` last.
* The schedule needs two more temporaries, `r1` and `r2`. The pointer to the
  block, which the first 16 rounds read, is kept in `scratch[104..108)`, and
  the count of the blocks left in `scratch[108..112)`.
* `r4`–`r11` and `lr` are saved in `scratch[68..104)` and restored on exit;
  `r0` and `r3` are never written.
* `r0`–`r3` (the pointers and the block count) are public; no address and no
  branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Sha256.Arm

open VG.Arm
open VG.Spec.Sha256 (K)

/-- The registers holding the working variables. -/
def work : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

/-- The register holding working variable `k` (`a = 0, …, h = 7`) at the start of round `t`. -/
def var (t k : Nat) : Reg := work.getD ((k + 8 - t % 8) % 8) .r4

/-- Round `t`'s temporary, which it leaves holding `a ⊕ b`, the `b ⊕ c` of
round `t + 1`: so `mreg (t + 1)` holds `b ⊕ c` in round `t`. -/
def mreg (t : Nat) : Reg := if t % 2 = 0 then .r12 else .lr

/-- The schedule's temporaries: the block pointer's and the count's registers. -/
def A : Reg := .r1
def B : Reg := .r2

/-- The offset of `W[i mod 16]` in the scratch buffer. -/
def slot (i : Nat) : Nat := 4 * (i % 16)

/-- The offsets of the block pointer and of the count of blocks left. -/
def ptrSlot : Nat := 104
def cntSlot : Nat := 108

/-- The register `schedule t` leaves `Wₜ` in. -/
def wreg (t : Nat) : Reg := if t < 16 then B else mreg t

/-- Store `Wₜ` in its slot, and leave it in `wreg t`. The additions are in
the order of the specification. -/
def schedule (t : Nat) : List Instr :=
  if t < 16 then [
    .ldr B .r1 (4 * t),
    .rev B B,
    .str B .r3 (slot t)]
  else
    let q := mreg t
    [ .ldr A .r3 (slot (t + 1)),
      .ldr B .r3 (slot (t + 14)),
      -- q := σ₀(Wₜ₋₁₅)
      .mov q (.shifted A .ror 7),
      .dp .eor q q (.shifted A .ror 18),
      .dp .eor q q (.shifted A .lsr 3),
      -- A := σ₁(Wₜ₋₂) + Wₜ₋₇
      .mov A (.shifted B .ror 17),
      .dp .eor A A (.shifted B .ror 19),
      .dp .eor A A (.shifted B .lsr 10),
      .ldr B .r3 (slot (t + 9)),
      .dp .add A A (.reg B),
      -- q := (σ₁(Wₜ₋₂) + Wₜ₋₇) + σ₀(Wₜ₋₁₅) + Wₜ₋₁₆
      .dp .add q A (.reg q),
      .ldr B .r3 (slot t),
      .dp .add q q (.reg B),
      .str q .r3 (slot t)]

/-- Round `t`, with `Wₜ` in `wreg t` and `b ⊕ c` in `mreg (t + 1)`. -/
def round (t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let d := var t 3
  let e := var t 4; let f := var t 5; let g := var t 6; let h := var t 7
  let q := mreg t; let p := mreg (t + 1)
  [ -- h := h + Wₜ + Kₜ
    .dp .add h h (.reg (wreg t)),
    .movw q ((K t).extractLsb' 0 16),
    .movt q ((K t).extractLsb' 16 16),
    .dp .add h h (.reg q),
    -- h := h + Ch(e, f, g), as ((f ⊕ g) ∧ e) ⊕ g
    .dp .eor q f (.reg g),
    .dp .and q q (.reg e),
    .dp .eor q q (.reg g),
    .dp .add h h (.reg q),
    -- h := h + Σ₁(e); now h is T₁
    .dp .eor q e (.shifted e .ror 5),
    .dp .eor q q (.shifted e .ror 19),
    .dp .add h h (.shifted q .ror 6),
    -- e' := d + T₁
    .dp .add d d (.reg h),
    -- h := h + Σ₀(a)
    .dp .eor q a (.shifted a .ror 11),
    .dp .eor q q (.shifted a .ror 20),
    .dp .add h h (.shifted q .ror 2),
    -- h := h + Maj(a, b, c), as ((b ⊕ c) ∧ (a ⊕ b)) ⊕ b; now h = a' = T₁ + T₂
    .dp .eor q a (.reg b),
    .dp .and p p (.reg q),
    .dp .eor p p (.reg b),
    .dp .add h h (.reg p)]

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ round n))

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.r4, 68), (.r5, 72), (.r6, 76), (.r7, 80), (.r8, 84), (.r9, 88), (.r10, 92), (.r11, 96),
   (.lr, 100)]

def save : List Instr := saved.map fun (r, d) => .str r .r3 d
def restore : List Instr := saved.map fun (r, d) => .ldr r .r3 d

/-- Load the hash value (`64 % 8 = 0`, so the variables are in the same
registers after the 64 rounds). -/
def load : List Instr := (List.range 8).map fun k => .ldr (var 0 k) .r0 (4 * k)

/-- Keep the count of blocks, and load the hash value. -/
def start : List Instr := .str .r2 .r3 cntSlot :: load

/-- Keep the block pointer, and `b ⊕ c` for round 0. -/
def enter : List Instr := [.str .r1 .r3 ptrSlot, .dp .eor (mreg 1) (var 0 1) (.reg (var 0 2))]

/-- Add the hash value into the working variables and store the result. -/
def update : List Instr :=
  (List.range 8).flatMap fun k => [
    .ldr (mreg 0) .r0 (4 * k),
    .dp .add (var 0 k) (var 0 k) (.reg (mreg 0)),
    .str (var 0 k) .r0 (4 * k)]

/-- Advance to the next block and decrement the count (setting Z when it hits 0). -/
def advance : List Instr := [
  .ldr .r1 .r3 ptrSlot,
  .dp .add .r1 .r1 (.imm 64),
  .ldr .r2 .r3 cntSlot,
  .subs .r2 .r2 (.imm 1),
  .str .r2 .r3 cntSlot]

/-- One block. -/
def body : Prog isa := .seq (.block enter) (.seq (rounds 64) (.block (update ++ advance)))

def compress : Prog isa :=
  .seq (.block (save ++ ([.cmp .r2 (.imm 0)] : List Instr)))
    (.seq (.ite .eq (.block []) (.seq (.block start) (.loop body .ne))) (.block restore))

end VG.Impl.Sha256.Arm
