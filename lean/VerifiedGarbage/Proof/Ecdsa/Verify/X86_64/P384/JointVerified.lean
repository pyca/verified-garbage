import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointCorrect
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointCT
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointLit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointLitAdx
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified

/-!
# ECDSA verification over P-384 on x86-64: `Verified`

P-384 is a curve the proof supports (`p384v_ok`, and `Law` for its group
law, its comb's tables and `InvSounds` for its inversions, which the
registration file supplies), so `jointVerify_ok` gives the contract's
postcondition; the callee-saved registers are restored, `rsp` is never
written, and every store is to `scratch`, which the return address is apart
from (`abiPreserved`). The timing depends only on what the shared contract
makes public: the pointers, the key, the digest and the signature
(`jointVerify_ct`).
-/

namespace VG.Proof.Ecdsa.Verify.X86_64.P384
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64
open VG.Proof.Ecdsa.X86_64
open VG.Proof.Ecdsa.X86_64.P384 (p384W p384_constRegions p384_combConsts satMem_held)

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

/-- The shared contract, but with `verifyX86_64`'s postcondition: what the
proofs of the inlined code give. -/
def verifyK₀ : Contract isa :=
  { pre := (Spec.Ecdsa.P384.inst.verifyContract (X86_64.abi.withConsts p384.combConsts)).pre
    post := verifyX86_64.post
    pub := (Spec.Ecdsa.P384.inst.verifyContract (X86_64.abi.withConsts p384.combConsts)).pub }

theorem sat_spec8 :
    (Spec.Ecdsa.P384.inst.verifyContract (X86_64.abi.withConsts p384.combConsts) 8).pre satState := by
  have held : ∀ i < p384W.length, satState.mem.readW (satState.syms "VG_P384_COMB" +
      BitVec.ofNat 64 (8 * i)) 64 = p384W.getD i 0 := satMem_held
  sig_pre [Spec.Ecdsa.P384.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
    Spec.P384.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p384_combConsts,
    Abi.withConsts, p384_constRegions, Abi.constsHeld, stackBelow]
  sig_and_intros
  all_goals first | exact Region.disjoint_of_sep (by decide) | rfl | exact held | decide

/-- The contract with 8 bytes of stack, for the calls' return address. -/
theorem implies8 :
    verifyK₀.Implies (Spec.Ecdsa.P384.inst.verifyContract (X86_64.abi.withConsts p384.combConsts) 8) :=
  ⟨fun _ hs => Sig.pre_stack0 hs, fun s s' hs hp => implies.post s s' (Sig.pre_stack0 hs) hp,
    fun _ _ _ _ hp => hp, ⟨satState, sat_spec8⟩⟩

section
variable (hL : Weierstrass.Law Spec.P384.curve)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds)
include hL hT hI

theorem jointVerify_x86 (s : State) (hs : verifyX86_64.pre s) :
    ∃ t s',Exec isa jointVerifyP384.inline s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' :=
  verify_abi_of_wp hs (jointVerify_p384_ok hL hT hI (pre_of hs))
    (by rw [Code.allInstrs_inline]; lit_decide) (Code.noCalls_inline (by lit_decide))
    (by rw [Code.allInstrs_inline]; lit_decide)

theorem jointVerify_x86_adx (s : State) (hs : verifyX86_64.pre s) :
    ∃ t s',Exec isa jointVerifyP384Adx.inline s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' :=
  verify_abi_of_wp hs (jointVerify_p384_adx_ok hL hT hI (pre_of_x hs))
    (by rw [Code.allInstrs_inline]; lit_decide) (Code.noCalls_inline (by lit_decide))
    (by rw [Code.allInstrs_inline]; lit_decide)

theorem jointVerify_verified : Verified X86_64.target jointVerifyP384
    (Spec.Ecdsa.P384.inst.verifyContract (X86_64.abi.withConsts p384.combConsts) 8) :=
  Verified.of_inline (k₀ := verifyK₀) (by lit_decide) (fun s hs => jointVerify_x86 hL hT hI s (implies.pre _ hs))
    (jointVerify_ct hL hT hI) implies8 (fun _ h => Sig.clear_of_pre_consts h) (fun _ _ _ _ _ hp => hp)
    fun s₁ s₂ h₁ h₂ hp => (implies.pub s₁ s₂ (Sig.pre_stack0 h₁) (Sig.pre_stack0 h₂) hp).1

theorem jointVerify_verified_adx : Verified X86_64.target jointVerifyP384Adx
    (Spec.Ecdsa.P384.inst.verifyContract (X86_64.abi.withConsts p384.combConsts) 8) :=
  Verified.of_inline (k₀ := verifyK₀) (by lit_decide) (fun s hs => jointVerify_x86_adx hL hT hI s (implies.pre _ hs))
    (jointVerify_adx_ct hL hT hI) implies8 (fun _ h => Sig.clear_of_pre_consts h) (fun _ _ _ _ _ hp => hp)
    fun s₁ s₂ h₁ h₂ hp => (implies.pub s₁ s₂ (Sig.pre_stack0 h₁) (Sig.pre_stack0 h₂) hp).1

end
end VG.Proof.Ecdsa.Verify.X86_64.P384
