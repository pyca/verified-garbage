module

public import VerifiedGarbage.Impl.Sha512.X86_64

/-!
# SHA-512 compression function: x86-64 implementation, rolled

The scalar technique of `Impl.Sha512.X86_64` (the working variables renamed
from round to round, a 16-word window of the schedule in the scratch space),
with rounds 16–79 rolled into a loop of sixteen and `Kₜ` added from a table
of constants (`aluTbl`, which carries the table, `Spec.Sha512.Ks`) rather
than loaded with `movabs`.

* Each round first adds `Kₜ` and `Wₜ` to `h`, off the path through `e` and
  `a` that the rest of the round depends on, then `Σ₁(e)` and `Ch(e, f, g)`.
* Sixteen rounds rename the working variables back to the registers they
  started in (`16 % 8 = 0`), and the window's slots repeat (`16 % 16 = 0`),
  so iteration `j` of the loop is the same code for every `j`: it reads `Kₜ`
  through an index, `rdx = 128 j`, at `rsi + rdx + 8 t'`.
* `rsi` (the blocks' address) and `rdx` (the block count) are kept in the
  scratch space while the rounds use them, at `176` and `184`; the first
  sixteen rounds read the block through `rdx` and `Kₜ` at `rsi + 8 t`.
  `rdi` and `rcx` are never written.
-/

@[expose] public section

namespace VG.Impl.Sha512.X86_64.Rolled

open VG.X86_64
open VG.Impl.Sha512.X86_64 (work var T0 T1 T2 at_ slot schedule saved save restore load update advance)

/-- The name of the table of round constants. -/
def kSym : String := "VG_SHA512_K"

/-- Where round `t` of the first sixteen reads `Kₜ`: the table at `rsi`. -/
def kSlot0 (t : Nat) : MemOp := { base := .rsi, disp := ((8 * t : Nat) : Int) }

/-- Where round `t'` of an iteration reads `Kₜ`: `t = 16 j + t'` with
`rdx = 128 j` and the table at `rsi`. -/
def kSlot (t' : Nat) : MemOp := { base := .rsi, index := some .rdx, scale := 1, disp := ((8 * t' : Nat) : Int) }

/-- Round `t` (`t % 16` in an iteration), with `Wₜ` in `T0` and `Kₜ` read at
`k`: `h := h + Kₜ + Wₜ + Σ₁(e) + Ch(e, f, g)`, then as `Impl.Sha512.X86_64.round`. -/
def round (t : Nat) (k : MemOp) : List Instr :=
  let a := var t 0; let b := var t 1; let c := var t 2; let d := var t 3
  let e := var t 4; let f := var t 5; let g := var t 6; let h := var t 7
  [ -- h := h + Kₜ + Wₜ
    .aluTbl .add h k kSym Spec.Sha512.Ks,
    .alu .add h (.reg T0),
    -- h := h + Σ₁(e)
    .mov T1 (.reg e),
    .shift .ror T1 14,
    .mov T2 (.reg e),
    .shift .ror T2 18,
    .alu .xor T1 (.reg T2),
    .shift .ror T2 23,
    .alu .xor T1 (.reg T2),
    .alu .add h (.reg T1),
    -- h := h + Ch(e, f, g), as ((f ⊕ g) ∧ e) ⊕ g; now h = T₁
    .mov T1 (.reg f),
    .alu .xor T1 (.reg g),
    .alu .and T1 (.reg e),
    .alu .xor T1 (.reg g),
    .alu .add h (.reg T1),
    -- e' := d + T₁
    .alu .add d (.reg h),
    -- h := h + Σ₀(a)
    .mov T1 (.reg a),
    .shift .ror T1 28,
    .mov T2 (.reg a),
    .shift .ror T2 34,
    .alu .xor T1 (.reg T2),
    .shift .ror T2 5,
    .alu .xor T1 (.reg T2),
    .alu .add h (.reg T1),
    -- h := h + Maj(a, b, c), as ((a ∨ b) ∧ c) ∨ (a ∧ b); now h = a' = T₁ + T₂
    .mov T1 (.reg a),
    .alu .or T1 (.reg b),
    .alu .and T1 (.reg c),
    .mov T2 (.reg a),
    .alu .and T2 (.reg b),
    .alu .or T1 (.reg T2),
    .alu .add h (.reg T1)]

/-- Leave `Wₜ` (`t < 16`) in `T0` and its slot, from the block at `rdx`. -/
def schedule0 (t : Nat) : List Instr :=
  [.mov T0 (.mem (at_ .rdx (8 * t))), .bswap T0, .store (slot t) T0]

/-- Rounds `0 … n-1` of the first sixteen. -/
def first : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (first n) (.block (schedule0 n ++ round n (kSlot0 n)))

/-- Rounds `0 … n-1` of an iteration: rounds `16 j + t'`, `t' < n`. -/
def iter : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (iter n) (.block (schedule (16 + n) ++ round n (kSlot n)))

/-- The next iteration: `rdx` steps by 128, up to 640 (round 80). -/
def step : List Instr := [.alu .add .rdx (.imm 128), .alu .cmp .rdx (.imm 640)]

/-- Keep `rsi` and `rdx` in the scratch space, read the block through `rdx`,
and point `rsi` at the table. -/
def enter : List Instr :=
  [.store (at_ .rcx 176) .rsi, .store (at_ .rcx 184) .rdx, .mov .rdx (.reg .rsi), .leaSym .rsi kSym]

/-- The index of the first iteration: round 16. -/
def toLoop : List Instr := [.mov .rdx (.imm 128)]

/-- Get back `rsi` and `rdx`. -/
def leave : List Instr := [.mov .rsi (.mem (at_ .rcx 176)), .mov .rdx (.mem (at_ .rcx 184))]

/-- One block. -/
def body : Prog isa :=
  .seq (.block (load ++ enter)) (.seq (first 16) (.seq (.block toLoop)
    (.seq (.loop (.seq (iter 16) (.block step)) .ne) (.block (leave ++ update ++ advance)))))

def compress : Prog isa :=
  .seq (.block (save ++ ([.alu .test .rdx (.reg .rdx)] : List Instr)))
    (.seq (.ite .e (.block []) (.loop body .ne)) (.block restore))

end VG.Impl.Sha512.X86_64.Rolled
