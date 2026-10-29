module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Secp256k1.Contract
public import VerifiedGarbage.Impl.Ecdsa.Verify.Secp256k1.X86_64
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Weierstrass.CombW
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Secp256k1.JointCT
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Secp256k1.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Secp256k1.JointErased
import Batteries.Data.List.Lemmas
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Secp256k1.JointContract
import VerifiedGarbage.Impl.Secp256k1.X86_64.Joint
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointFrame
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Front
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointMain
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Secp256k1.JointChecks
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Secp256k1.X86_64.JointLayout

/-!
# ECDSA verification over secp256k1 on x86-64: `Verified`

secp256k1 is a curve the proof supports (`secp256k1v_ok`, `a = 0` for its
doublings, and `Law` for its group law, its table of the generator's
multiples and `InvSounds` for its inversions, which the registration file
supplies), so `jointVerify_ok` gives the contract's postcondition; the
callee-saved registers are restored, `rsp` is never written, and every store
is to `scratch`, which the return address is apart from (`abiPreserved`).
The timing depends only on what the shared contract makes public: the
pointers, the key, the digest and the signature (`jointVerify_ct`).
-/

@[expose] public section

namespace VG.Proof.Secp256k1.X86_64
open VG VG.Impl.Secp256k1.X86_64 VG.Proof.Ecdsa.Verify.X86_64

/-- The joint multiplication's writes are apart from the final check's fixed inputs. -/
theorem joint_frame_layout : JointFrameLayout secp256k1v publicJoint := by
  constructor
  · unfold VG.Proof.Ecdsa.X86_64.FixedOk
    decide +kernel
  · decide +kernel
  · decide +kernel

end VG.Proof.Secp256k1.X86_64

namespace VG.Proof.Ecdsa.Verify.X86_64.Secp256k1
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64 VG.Impl.Secp256k1.X86_64
open VG.Impl.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Secp256k1.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

section
variable (hL : Law Spec.Secp256k1.curve)
    (hT : CombOkW Spec.Secp256k1.curve 9 1 Impl.Secp256k1.secp256k1G9 Impl.Secp256k1.secp256k1G9Start)
    (hI : InvSounds)
include hL hT hI

theorem jointVerify_secp256k1_ok {s : State} (hp : VPre secp256k1v s) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify secp256k1v publicJoint (jointDouble publicJoint.K)).inline s
      fun t => (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost secp256k1v s t := by
  have hc := secp256k1v_ok hI
  refine jointVerify_ok hc hL rfl (by decide +kernel) (by decide +kernel) hp ?_
  intro a g hM Q hQ hRep
  exact jointPoints_ok (j := publicJoint) hc hL (.ofGTab rfl hT (by decide) (by decide) rfl) rfl
    (jdblOk_dblJ0 hL secp256k1_a0)
    (by decide +kernel) joint_add_layout joint_init_layout joint_prep_layout joint_frame_layout
    (joint_doubler hc hL) (fun h => absurd h (by decide)) hp hM hQ hRep

end

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
  { pre := (Spec.Ecdsa.Secp256k1.inst.verifyContract (X86_64.abi.withConsts secp256k1v.combConsts)).pre
    post := verifyX86_64.post
    pub := (Spec.Ecdsa.Secp256k1.inst.verifyContract (X86_64.abi.withConsts secp256k1v.combConsts)).pub }

theorem sat_spec8 :
    (Spec.Ecdsa.Secp256k1.inst.verifyContract (X86_64.abi.withConsts secp256k1v.combConsts) 8).pre
      satState := by
  have held : ∀ i < secp256k1GW.length, satState.mem.readW (satState.syms "VG_SECP256K1_GTAB" +
      BitVec.ofNat 64 (8 * i)) 64 = secp256k1GW.getD i 0 := satMemG_held
  sig_pre [Spec.Ecdsa.Secp256k1.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
    Spec.Secp256k1.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, secp256k1v_combConsts,
    Abi.withConsts, secp256k1G_constRegions, Abi.constsHeld, stackBelow]
  sig_and_intros
  all_goals first | exact Region.disjoint_of_sep (by decide) | rfl | exact held | decide

/-- The contract with 8 bytes of stack, for the calls' return address. -/
theorem implies8 :
    verifyK₀.Implies
      (Spec.Ecdsa.Secp256k1.inst.verifyContract (X86_64.abi.withConsts secp256k1v.combConsts) 8) :=
  ⟨fun _ hs => Sig.pre_stack0 hs, fun s s' hs hp => implies.post s s' (Sig.pre_stack0 hs) hp,
    fun _ _ _ _ hp => hp, ⟨satState, sat_spec8⟩⟩

section
variable (hL : Law Spec.Secp256k1.curve)
    (hT : CombOkW Spec.Secp256k1.curve 9 1 Impl.Secp256k1.secp256k1G9 Impl.Secp256k1.secp256k1G9Start)
    (hI : InvSounds)
include hL hT hI

theorem verify_x86 (s : State) (hs : verifyX86_64.pre s) :
    ∃ t s',Exec isa verifySecp256k1.inline s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' :=
  verify_abi_of_wp hs (jointVerify_secp256k1_ok hL hT hI (pre_of hs))
    (by rw [Code.allInstrs_inline]; exact verify_rspMxcsr) (Code.noCalls_inline verify_inlineOk)

theorem verify_verified : Verified X86_64.target verifySecp256k1
    (Spec.Ecdsa.Secp256k1.inst.verifyContract (X86_64.abi.withConsts secp256k1v.combConsts) 8) :=
  Verified.of_inline (k₀ := verifyK₀) verify_inlineOk (fun s hs => verify_x86 hL hT hI s (implies.pre _ hs))
    (jointVerify_ct hL hT hI) implies8 (fun _ h => Sig.clear_of_pre_consts h) (fun _ _ _ _ _ hp => hp)
    fun s₁ s₂ h₁ h₂ hp => (implies.pub s₁ s₂ (Sig.pre_stack0 h₁) (Sig.pre_stack0 h₂) hp).1

end
end VG.Proof.Ecdsa.Verify.X86_64.Secp256k1
