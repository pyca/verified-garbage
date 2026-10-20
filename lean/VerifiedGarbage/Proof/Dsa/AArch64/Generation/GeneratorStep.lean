module
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorStep
public import VerifiedGarbage.Proof.Dsa.AArch64.Finish
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorPlan

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStatus
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorOutput
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStages

/-! A complete native generator attempt accepts exactly the specified nontrivial power. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def GeneratorPlan.accepts (p : GeneratorPlan) : Prop :=
  1 < Spec.Dsa.decodeBE p.hb ∧ Spec.Dsa.decodeBE p.hb < Spec.Dsa.decodeBE p.pb - 1 ∧ 1 < p.value

instance (p : GeneratorPlan) : Decidable p.accepts := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem generatorStep_ok (M : Mont)
    {p : GeneratorPlan} {W : Nat → BitVec 64} {s : State} (h : GeneratorMemory p W s) :
    WP isa (Impl.Dsa.AArch64.Generation.generatorStep M.mm p.len) s fun t =>
      GeneratorMemory p (upd W 19 (if p.accepts then 1 else 3)) t ∧
      (p.accepts → Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off p.B g) p.len = Spec.Dsa.encodeBE p.len p.value) ∧
      Frame p.changed s.mem t.mem ∧ Keep coreRegs s t := by
  unfold Impl.Dsa.AArch64.Generation.generatorStep
  refine WP.seq (WP.mono (generatorInputRange_ok h) fun u ⟨hr, hu, fu, ku⟩ => ?_)
  have hz := generatorTest_ok hr
  by_cases input : 1 < Spec.Dsa.decodeBE p.hb ∧ Spec.Dsa.decodeBE p.hb < Spec.Dsa.decodeBE p.pb - 1
  · refine WP.ite false (by simp [hz, input]) (fun he => Bool.noConfusion he) (fun _ => ?_)
    simp only [VG.Impl.Bignum.AArch64.seqs]
    refine WP.seq (WP.mono (generatorEvaluateStage_ok M hu) fun w ⟨gw, hw, fw, kw⟩ => ?_)
    refine WP.seq (WP.mono (generatorOutputRange_ok hw gw) fun x ⟨rx, hx, gx, fx, kx⟩ => ?_)
    have zx := generatorTest_ok rx
    have frame := (fu.trans fw).trans fx
    have keep := (ku.trans kw).trans kx
    by_cases output : 1 < p.value
    · have accepted : p.accepts := ⟨input.1, input.2, output⟩
      refine WP.ite false (by simp [zx, output]) (fun he => Bool.noConfusion he) (fun _ => ?_)
      refine WP.mono (generatorSetStatus_ok hx 1 (by decide)) fun t ⟨ht, gt, ft, kt⟩ => ?_
      exact ⟨by simpa [accepted] using ht, fun _ => gt.trans gx,
        frame.trans ft, (keep.trans kt).mono (by decide)⟩
    · have rejected : ¬ p.accepts := fun ha => output ha.2.2
      refine WP.ite true (by simp [zx, output]) (fun _ => ?_) (fun he => Bool.noConfusion he)
      refine WP.mono (generatorSetStatus_ok hx 3 (by decide)) fun t ⟨ht, _, ft, kt⟩ => ?_
      exact ⟨by simpa [rejected] using ht, fun ha => (rejected ha).elim,
        frame.trans ft, (keep.trans kt).mono (by decide)⟩
  · have rejected : ¬ p.accepts := fun ha => input ⟨ha.1, ha.2.1⟩
    refine WP.ite true (by simp [hz, input]) (fun _ => ?_) (fun he => Bool.noConfusion he)
    refine WP.mono (generatorSetStatus_ok hu 3 (by decide)) fun t ⟨ht, _, ft, kt⟩ => ?_
    exact ⟨by simpa [rejected] using ht, fun ha => (rejected ha).elim,
      fu.trans ft, (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.Generation
