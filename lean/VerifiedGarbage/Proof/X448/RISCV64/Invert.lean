module

public import VerifiedGarbage.Proof.X448.RISCV64.Ladder
import VerifiedGarbage.Proof.X448.RISCV64.Mul
import VerifiedGarbage.Proof.X25519.RISCV64.Mul
import VerifiedGarbage.Proof.Framework.Offset

/-!
# X448 on RISCV64: the inversion

The slots the inversion uses (`IQ`), and the resolution of an `if` by its
condition (`iteT`, `iteF`).
-/

@[expose] public section

namespace VG.Proof.X448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X448.RISCV64 VG.Proof.X25519 VG.Proof.X25519.RISCV64
open VG.Spec.X448 (P Fe)

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

end VG.Proof.X448.RISCV64
