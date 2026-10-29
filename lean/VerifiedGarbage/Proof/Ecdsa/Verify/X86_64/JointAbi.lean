module

import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointErased
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointCorrect
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.GContract
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointContract
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointLit
public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64.Joint
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Weierstrass.CombW
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Lit
import VerifiedGarbage.Proof.Framework.LitShare

/-! The joint verifier restores registers and keeps the caller's return address. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64
open VG.Proof.Ecdsa.X86_64

theorem verify_abi_of_wp {code : Prog isa} {s : State} (hs : verifyGX86_64.pre s)
    (hw : WP isa code s fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ verifyGX86_64.post s t)
    (hc : code.allInstrs (fun i => !Taint.clobbers i .rsp && !loadsMxcsr i)=true)
    (hnc : code.noCalls=true) :
    ∃ t s',Exec isa code s t s' ∧ abiPreserved s s' ∧ verifyGX86_64.post s s' := by
  obtain ⟨t,s',he,hsv,hpost⟩ := hw
  rw [Code.allInstrs_eq,List.all_eq_true] at hc
  have hsp : ∀ i∈instrs code,Taint.clobbers i .rsp=false := fun i hi => by
    have := hc i hi
    simp only [Bool.and_eq_true,Bool.not_eq_eq_eq_not,Bool.not_true] at this
    exact this.1
  have hmx : code.allInstrs (fun i => !loadsMxcsr i)=true := by
    rw [Code.allInstrs_eq,List.all_eq_true]
    intro i hi
    have := hc i hi
    simp only [Bool.and_eq_true] at this
    exact this.2
  have F := (Exec.regions he hnc).2.2
  obtain ⟨-,hwr,-,-,-,hrs,-,-⟩ := hs
  refine ⟨t,s',he,abiPreserved_of_exec hmx he ⟨fun r hr => ?_,?_⟩,hpost⟩
  · simp only [calleeSaved,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact Exec.gpr hsp he
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
  · rw [hwr] at F
    exact F.readW (r:=⟨s.gpr .rsp,8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      rintro r rfl
      exact hrs) (by decide)

theorem jointVerify_x86 (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 9 1 Impl.P256.p256G9 Impl.P256.p256G9Start)
    (hI : Weierstrass.X86_64.InvSounds) (hO : Weierstrass.PrimeOrder Spec.P256.curve)
    (s : State) (hs : verifyGX86_64.pre s) :
    ∃ t s',Exec isa jointVerifyP256.inline s t s' ∧ abiPreserved s s' ∧ verifyGX86_64.post s s' :=
  verify_abi_of_wp hs (jointVerify_p256_ok hL hT hI hO (preG_of hs))
    (by rw [Code.allInstrs_inline]; exact jointVerifyP256_rspMxcsr) (Code.noCalls_inline jointVerifyP256_inlineOk)

theorem jointVerify_x86_adx (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 9 1 Impl.P256.p256G9 Impl.P256.p256G9Start)
    (hI : Weierstrass.X86_64.InvSounds) (hO : Weierstrass.PrimeOrder Spec.P256.curve)
    (s : State) (hs : verifyGX86_64.pre s) :
    ∃ t s',Exec isa jointVerifyP256Adx.inline s t s' ∧ abiPreserved s s' ∧ verifyGX86_64.post s s' :=
  verify_abi_of_wp hs (jointVerify_p256_adx_ok hL hT hI hO (preG_of_x hs))
    (by rw [Code.allInstrs_inline]; exact jointVerifyP256Adx_rspMxcsr) (Code.noCalls_inline jointVerifyP256Adx_inlineOk)

end VG.Proof.Ecdsa.Verify.X86_64
