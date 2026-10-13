module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointCorrect
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointLit
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Verified
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Proof.P256.Prime

/-! The joint verifier restores registers and keeps the caller's return address. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64
open VG.Proof.Ecdsa.X86_64

theorem verify_abi_of_wp {code : Prog isa} {s : State} (hs : verifyX86_64.pre s)
    (hw : WP isa code s fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ verifyX86_64.post s t)
    (hsp : code.allInstrs (fun i => !Taint.clobbers i .rsp)=true)
    (hnc : code.noCalls=true) (hmx : code.allInstrs (fun i => !loadsMxcsr i)=true) :
    ∃ t s',Exec isa code s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' := by
  obtain ⟨t,s',he,hsv,hpost⟩ := hw
  have hsp : ∀ i∈instrs code,Taint.clobbers i .rsp=false := by
    rw [Code.allInstrs_eq,List.all_eq_true] at hsp
    intro i hi
    simpa using hsp i hi
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
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) (s : State) (hs : verifyX86_64.pre s) :
    ∃ t s',Exec isa jointVerifyP256.inline s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' :=
  verify_abi_of_wp hs (jointVerify_p256_ok hL hT hI (pre_of hs))
    (by rw [Code.allInstrs_inline]; lit_decide) (Code.noCalls_inline (by lit_decide))
    (by rw [Code.allInstrs_inline]; lit_decide)

theorem jointVerify_x86_adx (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) (s : State) (hs : verifyX86_64.pre s) :
    ∃ t s',Exec isa jointVerifyP256Adx.inline s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' :=
  verify_abi_of_wp hs (jointVerify_p256_adx_ok hL hT hI (show VPre p256x s from {pre_of hs with}))
    (by rw [Code.allInstrs_inline]; lit_decide) (Code.noCalls_inline (by lit_decide))
    (by rw [Code.allInstrs_inline]; lit_decide)

end VG.Proof.Ecdsa.Verify.X86_64
