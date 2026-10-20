module

import VerifiedGarbage.Proof.Dsa.X86.ShapeInspectQ
import VerifiedGarbage.Proof.Dsa.X86.DigestPrefix
public import VerifiedGarbage.Proof.Dsa.Accepted
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Proof.Dsa.X86.ShapeCombine
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags
import VerifiedGarbage.Proof.Dsa.X86.DigestWidth
import VerifiedGarbage.Proof.Dsa.X86.ShapeInspectP
import VerifiedGarbage.Proof.Dsa.X86.ShapeLoadFrame
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Complete public domain-shape check, including its rejection flag -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem shape_ok {s : State} {base : Addr} {size pLen qLen p q : Nat}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hp4 : 4 ≤ pLen) (hpmax : pLen ≤ 384) (hq4 : 4 ≤ qLen) (hqmax : qLen ≤ 384)
    (hpw : pLen % 4 = 0) (hqw : qLen % 4 = 0)
    (Rp : OperandReady s base 48 (.input .p) pLen) (Rq : OperandReady s base 48 (.input .q) qLen)
    (hp : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .p)).setWidth 64) pLen) = p)
    (hq : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .q)).setWidth 64) qLen) = q) :
    WP isa (Shape.check pLen qLen) s fun t =>
      shapeWord t base (Layout.field .mask) = mask32 (shapeValid p q) ∧
      t.zf = some (!decide (shapeValid p q)) ∧
      (shapeValid p q → (shapeWord t base (Layout.field .digestPrefixLen)).toNat =
        min (shapeWord s base (Layout.field .digestLen)).toNat (Spec.Dsa.bitLength q / 8)) ∧
      Keeps shapeClob s t ∧
      Outs base [(0, contextBytes 48), (Layout.field .digestPrefixLen, 8)] s.mem t.mem := by
  have hsaved : 8256 ≤ size := hz
  unfold Shape.check Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (inspectP_ok hs hz hp4 hpmax hpw Rp hp) fun u ⟨P1, P2, P3, Po, Ku, Ou⟩ => ?_)
  have Rqu := Rq.keep Ku (by decide) Ou (by decide)
  have hqu : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt u.mem ((pointerValue base u (.input .q)).setWidth 64) qLen) = q := by
    rw [Rq.bytes Ku (by decide) Ou (by decide), hq]
  refine WP.seq (WP.mono (inspectQ_ok (hs.of_keeps Ku (by decide)) hz hq4 hqmax hqw Rqu hqu P1 P2 P3 Po)
    fun v ⟨Vv, Q1, Q2, Q3, Kv, Ov⟩ => ?_)
  have Opre : Outs base [(0, contextBytes 48), (Layout.field .mask, 4)] s.mem v.mem :=
    (Outs.of_outside Ou (by simp)).trans Ov
  have Dv : shapeWord v base (Layout.field .digestLen) = shapeWord s base (Layout.field .digestLen) := by
    apply BitVec.eq_of_toNat_eq
    have H : val32 v.mem base (Layout.field .digestLen) 1 = val32 s.mem base (Layout.field .digestLen) 1 := by
      apply Opre.val32
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> decide
      · decide
    simpa only [val32, Nat.mul_zero, Nat.add_zero] using H
  have Ksv := Ku.trans Kv
  refine WP.seq (WP.mono (digestPrefix_raw (hs.of_keeps Ksv (by decide)) hsaved)
    fun w ⟨Dw, Kw, Ow⟩ => ?_)
  rw [Dv, Q1, Q2, Q3] at Dw
  have Vw : shapeWord w base (Layout.field .mask) = mask32 (shapeValid p q) := by
    rw [outside_shapeWord Ow (by decide) (.inr (by decide))]
    exact Vv
  have DP : shapeValid p q → (shapeWord w base (Layout.field .digestPrefixLen)).toNat =
      min (shapeWord s base (Layout.field .digestLen)).toNat (Spec.Dsa.bitLength q / 8) := by
    intro hv
    have widths : Spec.Dsa.bitLength q = 160 ∨ Spec.Dsa.bitLength q = 224 ∨ Spec.Dsa.bitLength q = 256 := by
      have H := hv.1
      unfold Spec.Dsa.supportedSizes at H
      omega
    rw [Dw, digestWidth_value widths]
  have Ksw := Ksv.widen Kw
  refine WP.seq (wp_movS (readSrc_sc (hs.of_keeps Ksw (by decide))
    (d := Layout.field .mask) (by change 8248 ≤ size; omega)) fun x ux _ => ?_)
  refine wp_cmpS rfl fun y uy Zy => WP.block_nil ?_
  refine WP.block_nil ⟨?_, ?_, ?_, (Ksw.widen ux.keeps).widen (uy.keeps []), ?_⟩
  · simpa only [shapeWord, uy.mem, ux.mem] using Vw
  · rw [Zy, ux.gpr]
    change some (shapeWord w base (Layout.field .mask) - 0 == 0) = _
    rw [Vw]
    by_cases hv : shapeValid p q <;> simp only [mask32, hv, ite_true, ite_false, decide_true, decide_false] <;> rfl
  · intro hv
    simpa only [shapeWord, uy.mem, ux.mem] using DP hv
  · have Opre' : Outs base [(0, contextBytes 48), (Layout.field .digestPrefixLen, 8)] s.mem v.mem := by
      intro a ha
      apply Opre a
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ha _ (by simp)
      · have H := ha (Layout.field .digestPrefixLen, 8) (by simp)
        change ofs base a < 8240 ∨ 8248 ≤ ofs base a at H
        change ofs base a < 8244 ∨ 8248 ≤ ofs base a
        omega
    rw [uy.mem, ux.mem]
    exact Opre'.trans (Outs.of_outside (Ow.mono (n' := 8) (Nat.le_refl _) (by omega)) (by simp))

end VG.Proof.Dsa.X86
