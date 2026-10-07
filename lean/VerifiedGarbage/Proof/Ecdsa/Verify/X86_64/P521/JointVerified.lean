import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P521.JointCorrect
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P521.JointCT
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P521.JointLit

/-!
# ECDSA verification over P-521 on x86-64: `Verified`

P-521 is a curve the proof supports (`p521_ok`, and `Law` for its group
law, its comb's tables and `InvSounds` for its inversions, which the
registration file supplies), so `jointVerify_ok` gives the contract's
postcondition; the callee-saved registers are restored, `rsp` is never
written, and every store is to `scratch`, which the return address is apart
from (`abiPreserved`). The timing depends only on what the shared contract
makes public: the pointers, the key, the digest and the signature
(`jointVerify_ct`).
-/

namespace VG.Proof.Ecdsa.Verify.X86_64.P521
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

section
variable (hL : Weierstrass.Law Spec.P521.curve)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds)
include hL hT hI

theorem jointVerify_x86 (s : State) (hs : verifyX86_64.pre s) :
    ∃ t s',Exec isa jointVerifyP521 s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' :=
  verify_abi_of_wp hs (jointVerify_p521_ok hL hT hI (pre_of hs))
    (by lit_decide) (by lit_decide) (by lit_decide)

theorem jointVerify_x86_adx (s : State) (hs : verifyX86_64.pre s) :
    ∃ t s',Exec isa jointVerifyP521Adx s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' :=
  verify_abi_of_wp hs (jointVerify_p521_adx_ok hL hT hI (pre_of_x hs))
    (by lit_decide) (by lit_decide) (by lit_decide)

theorem jointVerify_verified : Verified X86_64.target jointVerifyP521
    (Spec.Ecdsa.P521.inst.verifyContract (X86_64.abi.withConsts p521.combConsts)) := by
  refine ⟨fun s hs => ?_,jointVerify_ct hL hT hI,implies.sat⟩
  obtain ⟨t,s',he,ha,hp⟩ := jointVerify_x86 hL hT hI s (implies.pre _ hs)
  exact ⟨t,s',he,ha,implies.post s s' hs hp⟩

theorem jointVerify_verified_adx : Verified X86_64.target jointVerifyP521Adx
    (Spec.Ecdsa.P521.inst.verifyContract (X86_64.abi.withConsts p521.combConsts)) := by
  refine ⟨fun s hs => ?_,jointVerify_adx_ct hL hT hI,implies.sat⟩
  obtain ⟨t,s',he,ha,hp⟩ := jointVerify_x86_adx hL hT hI s (implies.pre _ hs)
  exact ⟨t,s',he,ha,implies.post s s' hs hp⟩

end
end VG.Proof.Ecdsa.Verify.X86_64.P521
