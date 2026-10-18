module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorStatus
import VerifiedGarbage.Proof.Framework.Omega

/-! # Complete native generator attempt: input filter, power, output filter -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def GeneratorPlan.accepts (p : GeneratorPlan) : Prop :=
  1 < Spec.Dsa.decodeBE p.hb ∧ Spec.Dsa.decodeBE p.hb < Spec.Dsa.decodeBE p.pb - 1 ∧ 1 < p.value

instance (p : GeneratorPlan) : Decidable p.accepts := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem generatorStep_ok (M : Mont) (Sq : MontS)
    {p : GeneratorPlan} {W : Nat → BitVec 64} {s : State} (h : GeneratorMemory p W s) :
    WP isa (Impl.Dsa.X86_64.Generation.generatorStep Sq.mm M.mm p.len) s fun t =>
      GeneratorMemory p (upd W 19 (if p.accepts then 1 else 3)) t ∧
      (p.accepts → Spec.Rsa.bytesAt t.mem (off p.B g) p.len = Spec.Dsa.encodeBE p.len p.value) ∧
      Frame p.changed s.mem t.mem ∧ Keep coreRegs s t := by
  unfold Impl.Dsa.X86_64.Generation.generatorStep
  refine WP.seq (WP.mono (generatorInputRange_ok h) fun u ⟨hr, hu, fu, ku⟩ => ?_)
  refine WP.seq (WP.mono (generatorTest_ok hu hr) fun v ⟨hz, hv, hm, kv⟩ => ?_)
  have fv : Frame p.changed s.mem v.mem := hm ▸ fu
  by_cases input : 1 < Spec.Dsa.decodeBE p.hb ∧ Spec.Dsa.decodeBE p.hb < Spec.Dsa.decodeBE p.pb - 1
  · refine WP.ite false (by simp [eval, hz, input]) (fun he => Bool.noConfusion he) (fun _ => ?_)
    change WP isa (.seq _ (.seq _ (.seq _ _))) v _
    refine WP.seq (WP.mono (generatorEvaluateStage_ok M Sq hv) fun w ⟨gw, hw, fw, kw⟩ => ?_)
    refine WP.seq (WP.mono (generatorOutputRange_ok hw gw) fun x ⟨rx, hx, gx, fx, kx⟩ => ?_)
    refine WP.seq (WP.mono (generatorTest_ok hx rx) fun y ⟨zy, hy, my, ky⟩ => ?_)
    have fy : Frame p.changed s.mem y.mem := my ▸ ((fv.trans fw).trans fx)
    have gy : Spec.Rsa.bytesAt y.mem (off p.B g) p.len = Spec.Dsa.encodeBE p.len p.value := my ▸ gx
    have keep := (((ku.trans kv).trans kw).trans kx).trans ky
    by_cases output : 1 < p.value
    · have accepted : p.accepts := ⟨input.1, input.2, output⟩
      refine WP.ite false (by simp [eval, zy, output]) (fun he => Bool.noConfusion he) (fun _ => ?_)
      refine WP.mono (generatorSetStatus_ok hy 1 (by decide)) fun t ⟨ht, gt, ft, kt⟩ => ?_
      exact ⟨by simpa [accepted] using ht, fun _ => gt.trans gy,
        fy.trans ft, (keep.trans kt).mono (by decide)⟩
    · have rejected : ¬ p.accepts := fun ha => output ha.2.2
      refine WP.ite true (by simp [eval, zy, output]) (fun _ => ?_) (fun he => Bool.noConfusion he)
      refine WP.mono (generatorSetStatus_ok hy 3 (by decide)) fun t ⟨ht, _, ft, kt⟩ => ?_
      exact ⟨by simpa [rejected] using ht, fun ha => (rejected ha).elim,
        fy.trans ft, (keep.trans kt).mono (by decide)⟩
  · have rejected : ¬ p.accepts := fun ha => input ⟨ha.1, ha.2.1⟩
    refine WP.ite true (by simp [eval, hz, input]) (fun _ => ?_) (fun he => Bool.noConfusion he)
    refine WP.mono (generatorSetStatus_ok hv 3 (by decide)) fun t ⟨ht, _, ft, kt⟩ => ?_
    exact ⟨by simpa [rejected] using ht, fun ha => (rejected ha).elim,
      fv.trans ft, ((ku.trans kv).trans kt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation
