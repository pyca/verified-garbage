module
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Proof.Bignum.Arm.Csub
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState

import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # RSA's shared array layout supplies every ARMv7 separation obligation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt Operand)

theorem array_sep {w j k : Nat} (h : j ≠ k) :
    arrAt w j + 8 * (w + 2) ≤ arrAt w k ∨ arrAt w k + 8 * (w + 2) ≤ arrAt w j := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact Or.inl (array_end_le h)
  · exact Or.inr (array_end_le h)

theorem layout_context {s : State} {base : BitVec 32} {size w o a b : Nat}
    (ws : Workspace s base size) (hw : 2 ≤ w) (fit : arrAt w 8 ≤ size)
    (ho : Operand o) (ha : Operand a) (hb : Operand b) :
    RoundCtx s base size (arrAt w 3) (arrAt w a) (arrAt w b) (arrAt w 0) (arrAt w 2) (2 * w) ∧
    CsubCtx s base size (arrAt w o) (arrAt w 2) (arrAt w 0) (arrAt w 3) (2 * w) := by
  obtain ⟨ho, ho2, ho3⟩ := ho
  obtain ⟨ha, ha2, ha3⟩ := ha
  obtain ⟨hb, hb2, hb3⟩ := hb
  change o ≠ 2 at ho2; change o ≠ 3 at ho3
  change a ≠ 2 at ha2; change a ≠ 3 at ha3
  change b ≠ 2 at hb2; change b ≠ 3 at hb3
  have fits (j : Nat) (hj : j < 8) : arrAt w j + 8 * (w + 2) ≤ size :=
    Nat.le_trans (array_end_le hj) fit
  have f0 := fits 0 (by decide)
  have f2 := fits 2 (by decide)
  have f3 := fits 3 (by decide)
  have fa := fits a ha
  have fb := fits b hb
  have fo := fits o ho
  have a2 := array_sep (w := w) ha2
  have b2 := array_sep (w := w) hb2
  have a3 := array_sep (w := w) ha3
  have b3 := array_sep (w := w) hb3
  have o2 := array_sep (w := w) ho2
  have o3 := array_sep (w := w) ho3
  have m2 := array_sep (w := w) (j := 0) (k := 2) (by decide)
  have m3 := array_sep (w := w) (j := 0) (k := 3) (by decide)
  have t2 := array_sep (w := w) (j := 2) (k := 3) (by decide)
  refine ⟨⟨ws, by omega_arith, ?_, by omega_arith, by omega_arith, by omega_arith, by omega_arith,
    by omega_arith, by omega_arith, by omega_arith, by omega_arith, by omega_arith, by omega_arith⟩,
    ⟨⟨ws.nowrap, by omega_arith, by omega_arith, by omega_arith, by omega_arith, by omega_arith, ws.writable⟩,
      by omega_arith, by omega_arith, by omega_arith, by omega_arith, by omega_arith⟩⟩
  simp only [arrAt, Proof.Rsa.Mont.hdrBytes]
  omega_arith

end VG.Proof.Bignum.Arm
