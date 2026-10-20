module
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Proof.Dsa.X86.ShapeCombine
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags

import VerifiedGarbage.Proof.Dsa.X86.ShapeParity
import VerifiedGarbage.Proof.Dsa.X86.ShapeLoadFrame
import VerifiedGarbage.Proof.Dsa.X86.ShapeLoadWidths
import VerifiedGarbage.Proof.Dsa.X86.ShapeMasks
import VerifiedGarbage.Proof.Mont.X86.ContextInit
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Completing public domain-size and oddness validation -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem inspectQ_ok {s : State} {base : Addr} {size len p q : Nat}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size) (h4 : 4 ≤ len) (hmax : len ≤ 384)
    (hw4 : len % 4 = 0) (R : OperandReady s base 48 (.input .q) len)
    (hq : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .q)).setWidth 64) len) = q)
    (P1 : shapeWord s base 32 = mask32 (Spec.Dsa.bitLength p = 1024))
    (P2 : shapeWord s base 36 = mask32 (Spec.Dsa.bitLength p = 2048))
    (P3 : shapeWord s base 40 = mask32 (Spec.Dsa.bitLength p = 3072))
    (Po : (shapeWord s base 56).toNat % 2 = p % 2) :
    WP isa (Shape.inspectQ len) s fun t =>
      shapeWord t base (Layout.field .mask) = mask32
        (Spec.Dsa.supportedSizes (Spec.Dsa.bitLength p) (Spec.Dsa.bitLength q) ∧ (q % 2 = 1 ∧ p % 2 = 1)) ∧
      shapeWord t base 44 = mask32 (Spec.Dsa.bitLength q = 160) ∧
      shapeWord t base 48 = mask32 (Spec.Dsa.bitLength q = 224) ∧
      shapeWord t base 52 = mask32 (Spec.Dsa.bitLength q = 256) ∧
      Keeps shapeClob s t ∧
      Outs base [(0, contextBytes 48), (Layout.field .mask, 4)] s.mem t.mem := by
  have hn : (len + 7) / 8 ≤ 48 := by omega
  have hn0 : 0 < (len + 7) / 8 := by omega
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn
  have hsaved : 8256 ≤ size := hz
  unfold Shape.inspectQ
  refine WP.seq (WP.mono (loadWidths_ok hs hz rfl h4 hmax hw4 R.toReadableComponent
    ((R.smaller hn).slot (by decide)) hq (by decide) (by decide) (by decide) (by decide))
    fun u ⟨Mu, Q1, Q2, Q3, Ku, Ou⟩ => ?_)
  refine WP.block_append (WP.mono (shapeParity_ok (hs.of_keeps Ku (by decide)) (by omega))
    fun v ⟨Pv, Kv, Ov⟩ => ?_)
  have Ksv := Ku.widen Kv
  have hsV := hs.of_keeps Ksv (by decide)
  have low := modulus_low hn0 Mu
  have parityQ : w32 u.mem base (slot ((len + 7) / 8) 0) % 2 = q % 2 := by omega
  rw [parityQ, loadWidths_header Ou (by decide) (.inr (by decide)), Po] at Pv
  have H1 : shapeWord v base 32 = mask32 (Spec.Dsa.bitLength p = 1024) := by
    rw [outside_shapeWord Ov (by decide) (.inl (by decide)), loadWidths_header Ou (by decide) (.inl (by decide)), P1]
  have H2 : shapeWord v base 36 = mask32 (Spec.Dsa.bitLength p = 2048) := by
    rw [outside_shapeWord Ov (by decide) (.inl (by decide)), loadWidths_header Ou (by decide) (.inl (by decide)), P2]
  have H3 : shapeWord v base 40 = mask32 (Spec.Dsa.bitLength p = 3072) := by
    rw [outside_shapeWord Ov (by decide) (.inl (by decide)), loadWidths_header Ou (by decide) (.inl (by decide)), P3]
  have J1 : shapeWord v base 44 = mask32 (Spec.Dsa.bitLength q = 160) := by
    rw [outside_shapeWord Ov (by decide) (.inl (by decide)), Q1]
  have J2 : shapeWord v base 48 = mask32 (Spec.Dsa.bitLength q = 224) := by
    rw [outside_shapeWord Ov (by decide) (.inl (by decide)), Q2]
  have J3 : shapeWord v base 52 = mask32 (Spec.Dsa.bitLength q = 256) := by
    rw [outside_shapeWord Ov (by decide) (.inl (by decide)), Q3]
  refine WP.mono (shapeCombine_ok hsV hsaved) fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨?_, ?_, ?_, ?_, Ksv.widen Kt, ?_⟩
  · rw [Vt, H1, H2, H3, J1, J2, J3, Pv]
    exact supported_masks _ _ _
  · rw [outside_shapeWord Ot (by decide) (.inl (by decide)), J1]
  · rw [outside_shapeWord Ot (by decide) (.inl (by decide)), J2]
  · rw [outside_shapeWord Ot (by decide) (.inl (by decide)), J3]
  · have Opre := (loadWidths_whole Ou hn (by decide)).trans
      (Ov.mono (o' := 0) (n' := contextBytes 48) (by decide) (by decide))
    exact (Outs.of_outside Opre (by simp)).trans (Outs.of_outside Ot (by simp))

end VG.Proof.Dsa.X86
