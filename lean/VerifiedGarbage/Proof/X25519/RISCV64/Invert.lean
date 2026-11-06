module

public import VerifiedGarbage.Proof.X25519.RISCV64.Ladder
import VerifiedGarbage.Proof.X25519.RISCV64.Mul
import VerifiedGarbage.Proof.Framework.Offset

/-!
# X25519 on RISCV64: the inversion's slots

The slots the inversion reads and writes (`IQ`: `z` at `Z2`, the result at
`R`), and the branches of its square-and-multiply resolved (`iteT`, `iteF`).
-/

@[expose] public section

namespace VG.Proof.X25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X25519.RISCV64
open VG.Spec.X25519 (P Fe)

/-! ## The bits of `p - 2` -/

theorem iteT {c : Prop} [Decidable c] {α : Type} {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem iteF {c : Prop} [Decidable c] {α : Type} {a b : α} (h : ¬c) : (if c then a else b) = b := by
  simp [h]

section
variable {b : Addr}

/-! ## The inversion -/

/-- The slots of the inversion. -/
def IQ : List Nat := [Z2, R, X2]

end

end VG.Proof.X25519.RISCV64
