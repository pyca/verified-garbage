import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacAbi
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64

theorem jointVerify_callsKeep : CallsKeep P256Joint.verify := by lit_decide

theorem jointVerify_untouched : KeepsUntouched P256Joint.verify := by lit_decide

theorem jointVerify_keepsV : P256Joint.verify.allInstrs keepsV=true := by lit_decide

theorem jointVerify_a64_of_wp
    (correct : ∀ s,VPre p256 s → WP isa P256Joint.verify s fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p256 s t)
    (s : State) (hs : verifyAArch64.pre s) :
    ∃ t s',Exec isa P256Joint.verify s t s' ∧ abiPreserved s s' ∧ verifyAArch64.post s s' := by
  obtain ⟨t,s',he,hsv,hpost⟩ := correct s (jacPre_of hs)
  exact ⟨t,s',he,abiPreserved_of he jointVerify_callsKeep jointVerify_untouched jointVerify_keepsV hsv,hpost⟩

end VG.Proof.Ecdsa.Verify.AArch64
