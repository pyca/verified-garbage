module

public import VerifiedGarbage.Impl.Ed448.X86.ScalarBase
public import VerifiedGarbage.Impl.X448.X86
public import VerifiedGarbage.Impl.Xdh.X86
public import VerifiedGarbage.Impl.Scrub.X86

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

/-! ## The functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubF rb W`): the `W`
bytes of stack below `esp` that its frames and calls use zeroed, and the
registers a callee may change cleared but the `rb` bits of the result, so
that it returns without secret residue. -/

namespace VG.Impl.X448.X86.Fn

open VG.X86

/-- `vg_x448_exchange`, as emitted. -/
def exchange : Prog isa :=
  Impl.Scrub.X86.scrubF 32 40 (Impl.Xdh.X86.exchange "vg_x448" Impl.X448.X86.x448 56)

/-- `vg_x448_base`, as emitted. -/
def base : Prog isa := Impl.Scrub.X86.scrubF 0 20 Impl.X448.X86.x448Base

end VG.Impl.X448.X86.Fn
