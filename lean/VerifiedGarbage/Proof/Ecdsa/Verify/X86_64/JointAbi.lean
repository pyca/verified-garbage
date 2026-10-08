import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointCorrect
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointLit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Verified

/-! The joint verifier restores registers and keeps the caller's return address. -/
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
    ∃ t s',Exec isa jointVerifyP256 s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' :=
  verify_abi_of_wp hs (wp_of_inline (by lit_decide) <| jointVerify_p256_ok hL hT hI (pre_of hs))
    (by lit_decide) (by lit_decide) (by lit_decide)

theorem jointVerify_x86_adx (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) (s : State) (hs : verifyX86_64.pre s) :
    ∃ t s',Exec isa jointVerifyP256Adx s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' :=
  verify_abi_of_wp hs (wp_of_inline (by lit_decide) <| jointVerify_p256_adx_ok hL hT hI (show VPre p256x s from {pre_of hs with}))
    (by lit_decide) (by lit_decide) (by lit_decide)

end VG.Proof.Ecdsa.Verify.X86_64
