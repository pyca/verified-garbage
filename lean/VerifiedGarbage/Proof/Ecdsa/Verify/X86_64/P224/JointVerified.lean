module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P224.Contract
public import VerifiedGarbage.Impl.Ecdsa.Verify.P224.X86_64
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Weierstrass.CombW
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Framework.X86_64.Abi

import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P224.JointErased
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P224.JointCT
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P224.JointLit
import Batteries.Data.List.Lemmas
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Impl.P224.X86_64.Joint
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointFrame
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointMain
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P224.JointChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P224.JointContract
import VerifiedGarbage.Proof.P224.X86_64.JointLayout
/-!
# ECDSA verification over P-224 on x86-64: `Verified`

P-224 is a curve the proof supports (`p224v_ok`, and `Law` for its group
law, its comb's tables and `InvSounds` for its inversions, which the
registration file supplies), so `jointVerify_ok` gives the contract's
postcondition; the callee-saved registers are restored, `rsp` is never
written, and every store is to `scratch`, which the return address is apart
from (`abiPreserved`). The timing depends only on what the shared contract
makes public: the pointers, the key, the digest and the signature
(`jointVerify_ct`).
-/

-- Formerly `VerifiedGarbage/Proof/P224/X86_64/JointFrame.lean`, which only this module imported.
section

/-! The joint multiplication's writes are apart from the final check's fixed inputs. -/

section

namespace VG.Proof.P224.X86_64
open VG VG.Impl.P224.X86_64 VG.Proof.Ecdsa.Verify.X86_64

theorem joint_frame_layout : JointFrameLayout p224v publicJoint := by
  constructor
  · unfold VG.Proof.Ecdsa.X86_64.FixedOk
    decide +kernel
  · decide +kernel
  · decide +kernel

end VG.Proof.P224.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/X86_64/P224/JointCorrect.lean`, which only this module imported.
section

/-! Joint verification over P-224 satisfies the functional specification. -/

section

namespace VG.Proof.Ecdsa.Verify.X86_64.P224
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P224.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.P224.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

theorem jointVerify_p224_ok (hL : Law Spec.P224.curve)
    (hT : CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : InvSounds) {s : State} (hp : VPre p224v s) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p224v publicJoint (Joint.jacDouble publicJoint.K)).inline s
      fun t => (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p224v s t := by
  have hc := p224v_ok hI
  refine jointVerify_ok hc.toBaseCfgOk hL rfl (by decide +kernel) (by decide +kernel) hp ?_
  intro a g hM Q hQ hRep
  exact jointPoints_ok hc.toBaseCfgOk hL (.ofComb rfl hT (by decide) (by decide) rfl) rfl (hc.jdbl hL) (by decide +kernel)
    joint_add_layout joint_init_layout joint_prep_layout joint_frame_layout (joint_doubler hc hL)
    (fun h => absurd h (by decide)) hp hM hQ hRep

end VG.Proof.Ecdsa.Verify.X86_64.P224
end

end

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.P224
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64
open VG.Proof.Ecdsa.X86_64
open VG.Proof.Ecdsa.X86_64.P224 (p224W p224_constRegions p224_combConsts satMem_held)

theorem verify_abi_of_wp {code : Prog isa} {s : State} (hs : verifyX86_64.pre s)
    (hw : WP isa code s fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ verifyX86_64.post s t)
    (hc : code.allInstrs (fun i => !Taint.clobbers i .rsp && !loadsMxcsr i)=true)
    (hnc : code.noCalls=true) :
    ∃ t s',Exec isa code s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' := by
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

/-- The shared contract, but with `verifyX86_64`'s postcondition: what the
proofs of the inlined code give. -/
def verifyK₀ : Contract isa :=
  { pre := (Spec.Ecdsa.P224.inst.verifyContract (X86_64.abi.withConsts p224.combConsts)).pre
    post := verifyX86_64.post
    pub := (Spec.Ecdsa.P224.inst.verifyContract (X86_64.abi.withConsts p224.combConsts)).pub }

theorem sat_spec8 :
    (Spec.Ecdsa.P224.inst.verifyContract (X86_64.abi.withConsts p224.combConsts) 8).pre satState := by
  have held : ∀ i < p224W.length, satState.mem.readW (satState.syms "VG_P224_COMB" +
      BitVec.ofNat 64 (8 * i)) 64 = p224W.getD i 0 := satMem_held
  sig_pre [Spec.Ecdsa.P224.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
    Spec.P224.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, p224_combConsts,
    Abi.withConsts, p224_constRegions, Abi.constsHeld, stackBelow]
  sig_and_intros
  all_goals first | exact Region.disjoint_of_sep (by decide) | rfl | exact held | decide

/-- The contract with 8 bytes of stack, for the calls' return address. -/
theorem implies8 :
    verifyK₀.Implies (Spec.Ecdsa.P224.inst.verifyContract (X86_64.abi.withConsts p224.combConsts) 8) :=
  ⟨fun _ hs => Sig.pre_stack0 hs, fun s s' hs hp => implies.post s s' (Sig.pre_stack0 hs) hp,
    fun _ _ _ _ hp => hp, ⟨satState, sat_spec8⟩⟩

section
variable (hL : Weierstrass.Law Spec.P224.curve)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds)
include hL hT hI

theorem jointVerify_x86 (s : State) (hs : verifyX86_64.pre s) :
    ∃ t s',Exec isa jointVerifyP224.inline s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' :=
  verify_abi_of_wp hs (jointVerify_p224_ok hL hT hI (pre_of hs))
    (by rw [Code.allInstrs_inline]; exact jointVerifyP224_rspMxcsr) (Code.noCalls_inline jointVerifyP224_inlineOk)

theorem jointVerify_verified : Verified X86_64.target jointVerifyP224
    (Spec.Ecdsa.P224.inst.verifyContract (X86_64.abi.withConsts p224.combConsts) 8) :=
  Verified.of_inline (k₀ := verifyK₀) jointVerifyP224_inlineOk (fun s hs => jointVerify_x86 hL hT hI s (implies.pre _ hs))
    (jointVerify_ct hL hT hI) implies8 (fun _ h => Sig.clear_of_pre_consts h) (fun _ _ _ _ _ hp => hp)
    fun s₁ s₂ h₁ h₂ hp => (implies.pub s₁ s₂ (Sig.pre_stack0 h₁) (Sig.pre_stack0 h₂) hp).1

end
end VG.Proof.Ecdsa.Verify.X86_64.P224
