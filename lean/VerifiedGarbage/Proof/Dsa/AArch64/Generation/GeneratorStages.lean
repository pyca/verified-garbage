module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorPlan
public import VerifiedGarbage.Proof.Dsa.Arithmetic
public import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.Omega

/-! # Generator range and power stages preserve their common memory invariant -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem generatorInputRange_ok {p : GeneratorPlan} {W : Nat → BitVec 64} {s : State}
    (h : GeneratorMemory p W s) :
    WP isa (Impl.Dsa.AArch64.Generation.generatorRangeFromFrame p.len false) s fun t =>
      t.gpr .x3 = mask (decide (1 < Spec.Dsa.decodeBE p.hb ∧
        Spec.Dsa.decodeBE p.hb < Spec.Dsa.decodeBE p.pb - 1)) ∧
      GeneratorMemory p W t ∧ Frame p.changed s.mem t.mem ∧ Keep (.x0 :: mmRegs) s t := by
  obtain ⟨V, R⟩ := h.rep
  refine WP.mono (generatorFromFrame_ok false h.layout R h.arithmetic
    (by rw [h.base]; exact p.arithmeticBase) p.width p.workspaceRoom p.frameHeaders p.frameOutside
    (p.frameSeparate _ (by simp)) (p.hashSeparate _ (by simp))
    (by simpa only [h.base] using h.pArithmetic) (by simpa only [Bool.false_eq_true, ↓reduceIte, h.input] using h.hArithmetic)
    p.pLength p.hLength (fun _ => p.pOdd) (fun he => Bool.noConfusion he))
    fun t ⟨hr, Lt, Rt, _, ft, kt⟩ => ?_
  have frame : Frame p.changed s.mem t.mem := ft.mono (by intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [GeneratorPlan.changed])
  exact ⟨hr, h.frame Lt ⟨V, Rt⟩ h.base h.input frame kt.rd kt.wr, frame, kt⟩

theorem generatorEvaluateStage_ok (M : Mont)
    {p : GeneratorPlan} {W : Nat → BitVec 64} {s : State} (h : GeneratorMemory p W s) :
    WP isa (Impl.Dsa.AArch64.Generation.generatorEvaluate M.mm p.len) s fun t =>
      Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off p.B g) p.len = Spec.Dsa.encodeBE p.len p.value ∧
      GeneratorMemory p W t ∧ Frame p.changed s.mem t.mem ∧ Keep (.x0 :: coreRegs) s t := by
  obtain ⟨V, R⟩ := h.rep
  refine WP.mono (generatorEvaluate_ok M h.layout R h.base h.input h.parent
    p.width p.pLength p.hLength p.eLength p.pPositive p.pOdd
    h.pParent h.hParent h.eParent h.gWrite p.gParentOutside
    (by intro r hr; exact p.frameSeparate r (by simp only [List.mem_cons] at hr ⊢; exact Or.inr hr))
    (by intro r hr; exact p.hashSeparate r (by simp only [List.mem_cons] at hr ⊢; exact Or.inr hr)))
    fun t ⟨result, Lt, Rt, ft, kt⟩ => ?_
  have frame : Frame p.changed s.mem t.mem := ft.mono (by
    intro r hr; simp only [GeneratorPlan.changed, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp [h])
  exact ⟨result, h.frame Lt ⟨V, Rt⟩ h.base h.input frame kt.rd kt.wr, frame, kt⟩

end VG.Proof.Dsa.AArch64.Generation
