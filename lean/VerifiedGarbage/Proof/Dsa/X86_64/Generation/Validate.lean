module
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Validate
public import VerifiedGarbage.Proof.Dsa.X86_64.Parameters
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ValidateCore
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory

/-! # Domain-check results control native seed retry or acceptance -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem validate_ok (M : Mont) (Sq : MontS) {s : State} {F S : Addr}
    {V : Nat → Byte} {W : Nat → BitVec 64} (p : ParametersInput)
    (L : Lay s F S) (R : Rep s.mem F S V W)
    (hbase : p.base = off (W 5) domainCheck)
    (hp : p.pLen < 2 ^ 32) (hq : p.qLen < 2 ^ 32)
    (hs : Scr s p.base Impl.Dsa.Layout.usedBytes)
    (src : Src s p.base Impl.Dsa.Layout.usedBytes (off (W 5) packed) p.params)
    (hF : (⟨F, frameBytes⟩ : Region).Disjoint ⟨p.base, Impl.Dsa.Layout.usedBytes⟩)
    (hS : (⟨S, oRsa⟩ : Region).Disjoint ⟨p.base, Impl.Dsa.Layout.usedBytes⟩) :
    WP isa (Impl.Dsa.X86_64.Generation.validate Sq.mm M.mm p.pLen p.qLen) s fun t =>
      Lay t F S ∧ Rep t.mem F S V
        (upd W 19 (BitVec.ofNat 64 (if Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params then 1 else 3))) ∧
      Frame [⟨p.base, Impl.Dsa.Layout.usedBytes⟩, ⟨F, frameBytes⟩] s.mem t.mem ∧ Keep coreRegs s t := by
  unfold Impl.Dsa.X86_64.Generation.validate
  refine WP.seq (WP.mono (validateCore_ok M Sq p L R hbase hp hq hs src hF hS)
    fun u ⟨hr, Lu, Ru, fu, ku⟩ => ?_)
  refine WP.seq (WP.mono (validateTest_ok hr) fun v ⟨hz, hm, kv⟩ => ?_)
  have Rv : Rep v.mem F S V W := hm ▸ Ru
  have Lv := lay_of_rep Lu Ru Rv rfl (kv.gpr (by decide)) kv.2.2
  have fv : Frame [⟨p.base, Impl.Dsa.Layout.usedBytes⟩, ⟨F, frameBytes⟩] s.mem v.mem := by
    rw [hm]
    exact fu.mono (by intro r hr; rcases List.mem_singleton.mp hr with rfl; simp)
  have finish (status : Nat) (hstatus : status < 2 ^ 32) :
      WP isa (.block (Impl.Dsa.X86_64.Generation.stackStatus status)) v fun t =>
        Lay t F S ∧ Rep t.mem F S V (upd W 19 (BitVec.ofNat 64 status)) ∧
        Frame [⟨p.base, Impl.Dsa.Layout.usedBytes⟩, ⟨F, frameBytes⟩] s.mem t.mem ∧ Keep coreRegs s t := by
    refine WP.mono (stackStatus_ok Lv Rv status hstatus) fun t ⟨Lt, Rt, ft, kt⟩ => ?_
    refine ⟨Lt, Rt, fv.trans ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
    intro a ha
    apply ft a
    right
    have hn := ha ⟨F, frameBytes⟩ (by simp)
    change ¬ ofs F a < frameBytes at hn
    unfold frameBytes at hn
    omega
  cases hc : Spec.Dsa.checkParametersBytes p.pLen p.qLen p.params with
  | false =>
    refine WP.ite true (by simp [eval, hz, hc]) (fun _ => ?_) (fun he => Bool.noConfusion he)
    simpa only [hc, Bool.false_eq_true, ite_false] using finish 3 (by decide)
  | true =>
    refine WP.ite false (by simp [eval, hz, hc]) (fun he => Bool.noConfusion he) (fun _ => ?_)
    simpa only [hc, ite_true] using finish 1 (by decide)

end VG.Proof.Dsa.X86_64.Generation
