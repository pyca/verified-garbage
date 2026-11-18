module

public import VerifiedGarbage.Impl.Ed448.X86.ScalarBase

/-!
# X448 of the base point on x86 (32-bit): a fixed-base multiplication on edwards448

`vg_x448_base(out = [esp + 4], scalar = [esp + 8], scratch = [esp + 12])`
computes `X448(k, 5)` as the u-coordinate `y² / x²` of `[k] B` on edwards448
(Ed448's curve), `B` its base point (RFC 7748 §4.2's 4-isogeny;
`Proof/X448/BaseAdd.lean`).

`[k] B` is Ed448's base-point multiplication on this target
(`Impl/Ed448/X86/ScalarBase.lean`): its entry (the callee-saved registers
saved in the working space, and the slots initialized) and its four-column
comb (`combLoop`), which leaves `[k] B` as `(X : Y : Z)` in slots 0–2. The
comb reads 456 bits, a byte each at `BITS`: X448's `bits` expands the decoded
(clamped) scalar's 448, and the eight above them are zeroed (`zeroTop`).

Then `X448(k, 5) = Y² / X²`: the squares go to the ladder's `X2` and `Z2`,
inverted, multiplied, fully reduced and written as the ladder's result is
(`invert`, `finish`).

The only branches are on the loop counters, and every address is a pointer
plus a constant or a counter, so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.X448.X86

open VG.X86

/-- The bytes of bits 448–455 at `BITS`, zeroed. -/
def zeroTop : List Instr :=
  .mov .edx (.imm 0) :: (List.range 8).flatMap fun j => [.store8 (sc (BITS + 448 + j)) .dl]

/-- `X²` into `Z2` and `Y²` into `X2`, for `(X : Y : Z)` in slots 0–2. -/
def uOps : List Op := [.mul Z2 X1 X1, .mul X2 X2 X2]

/-- The callee-saved registers saved, the slots initialized, and the 456 bits the comb reads: the
decoded scalar's 448, and zeros above them. -/
def baseEntry : Prog isa :=
  .seq (.block (Impl.Ed448.X86.save 12)) <| .seq Impl.Ed448.X86.initSlots <| .seq (.block zeroTop) bits

/-- `vg_x448_base(out = [esp + 4], scalar = [esp + 8], scratch = [esp + 12])`. -/
def x448Base : Prog isa :=
  .seq baseEntry <| .seq Impl.Ed448.X86.combLoop <| .seq (ops uOps) <| .seq invert finish

end VG.Impl.X448.X86
