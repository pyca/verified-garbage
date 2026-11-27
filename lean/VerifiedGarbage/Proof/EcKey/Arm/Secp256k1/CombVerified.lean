module

public import VerifiedGarbage.Proof.Secp256k1.Arm.CombSat
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Secp256k1.Arm.CombSat
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.EcKey.Arm.Secp256k1.CombMain
import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombLit
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombLit
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.ArmComb
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData

/-! ### `EcKey.Arm.Secp256k1.CombCT`, which only this module used -/

section

/-! Key generation's comb depends only on public pointers and counters. -/

@[expose] public section
namespace VG.Proof.EcKey.Arm.Secp256k1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm

def combPkPub (u : Bool) (s t : State) : Prop :=
  pkArm.pub s t ∧ s.syms secp256k1Comb.tsym=t.syms secp256k1Comb.tsym ∧ s.syms (secp256k1With u).constSym=t.syms (secp256k1With u).constSym

/-- The taint analysis's start, and the tables' addresses, agree in the two states. -/
theorem combPk_agree {u : Bool} {s t : State} (h : combPkPub u s t) :
    VG.Arm.Taint.Agree (Taint.ofRegs [.r0,.r1,.r2]) s t ∧
      ∀ n ∈ [secp256k1Comb.tsym,(secp256k1With u).constSym], s.syms n = t.syms n := by
  obtain ⟨⟨_,h0,h1,h2⟩,sy,sy'⟩ := h
  refine ⟨Taint.agree_ofRegs (fun r hr => ?_),fun n hn => ?_⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    exacts [h0,h1,h2]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl|rfl
    exacts [sy,sy']

theorem combPk_ct : ConstantTime isa (combPkPre false) (combPkPub false) publicKeySecp256k1Comb :=
  VG.Taint.constantTime (A := taintSym [secp256k1Comb.tsym,(secp256k1With false).constSym]) (Taint.ofRegs [.r0,.r1,.r2])
    (fun _ _ _ _ h => combPk_agree h) (by native_taint_decide)

theorem combPkU_ct : ConstantTime isa (combPkPre true) (combPkPub true) publicKeySecp256k1CombU :=
  VG.Taint.constantTime (A := taintSymU [secp256k1Comb.tsym,(secp256k1With true).constSym]) (Taint.ofRegs [.r0,.r1,.r2])
    (fun _ _ _ _ h => combPk_agree h) (by taint_decide)

end VG.Proof.EcKey.Arm.Secp256k1

end

end

/-! The public-key API uses the same checked generator comb as signing. -/

@[expose] public section
namespace VG.Proof.EcKey.Arm.Secp256k1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Secp256k1.Arm

/-- A state satisfying the precondition without the tables, which it holds
in `constMem`: the comb's at `0x100000`, then the setup's constants at
`0x125000`. -/
def combPkSat (u : Bool) : State := {combSatState with
  gpr := fun r => match r with | .r0 => 0x10000 | .r1 => 0x12000 | _ => 0
  mem := constMem ((0x100000 : BitVec 32).setWidth 64) (secp256k1CombWords ++ (secp256k1With u).constTbl)
  rd := [⟨0x12000,32⟩]
  wr := [⟨0x10000,65⟩,⟨0,8192⟩]
  syms := fun n => if n = (secp256k1With u).constSym then 0x125000 else 0x100000 }

theorem combPk_sat (u : Bool) : ∃ s, (combPkSpec u).pre s :=
  sat_consts (s := combPkSat u)
    (by
      cases u <;>
      (sig_pre [Spec.EcKey.Secp256k1.inst,Spec.EcKey.Instance.publicKeyContract,Spec.EcKey.Instance.publicKeySig,
    Spec.Secp256k1.curve,Spec.EcKey.scratchWords,abi,argRegs,reduceClassify,Loc.val,State.addr,combPkSat,combSatState]
       sig_and_intros
       all_goals first
         | rfl
         | decide
         | exact Region.disjoint_of_sep (by decide)))
    (VG.Proof.Ecdsa.Arm.constsOk_two _ (T := 0x100000) (T₂ := 0x125000) (by cases u <;> decide) (by cases u <;> decide)
      (by rw [comb_words_length]; decide) rfl (by cases u <;> decide) (by decide) (by decide)
      (by rw [comb_words_length]; cases u <;> decide) (by cases u <;> decide)
      (by rw [comb_words_length]; cases u <;> decide) (by cases u <;> decide))

def combPkLocal (u : Bool) : Contract isa where
  pre := combPkPre u
  post := PkPost (secp256k1With u)
  pub := combPkPub u

theorem combPkWith_verified (hC : Weierstrass.Law Spec.Secp256k1.curve) (u : Bool)
    (hct : ConstantTime isa (combPkPre u) (combPkPub u) (publicKeySecp256k1CombWith u)) :
    Verified Arm.target (publicKeySecp256k1CombWith u) (combPkSpec u) := by
  refine Verified.of_correct (k := combPkLocal u) (fun s hs => ?_) hct
    ⟨fun _ h => combPk_pre h,?_,?_,combPk_sat u⟩
  · obtain ⟨tr,t,exec,keep,post⟩ := combPk_ok hC hs
    exact ⟨tr,t,exec,VG.Proof.Ecdsa.Arm.abi_of_saved keep.saved keep.sp,post⟩
  · intro s t _ post
    sig_post [combPkSpec,Spec.EcKey.Secp256k1.inst,Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig,Spec.Secp256k1.curve,Spec.EcKey.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr,Abi.withConsts]
    have pp := post_of (u := u) post
    simp only [pkArm,pk,Spec.Secp256k1.curve,State.addr] at pp
    revert pp
    generalize Spec.EcKey.publicKey _ _=q
    rcases q with _|_|⟨x,y⟩ <;> exact id
  · intro s t _ _ pub
    obtain ⟨pub, sy⟩ := pub_consts.mp pub
    sig_pub [Spec.EcKey.Secp256k1.inst,Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig,Spec.Secp256k1.curve,Spec.EcKey.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr] at pub
    obtain ⟨sp,h0,h1,h2⟩ := pub
    exact ⟨⟨sp,h0,h1,h2⟩,symAddr_eq_iff.mp (sy (secp256k1Comb.tsym, secp256k1CombWords) List.mem_cons_self),
      symAddr_eq_iff.mp (sy ((secp256k1With u).constSym, (secp256k1With u).constTbl) (List.mem_cons_of_mem _ (List.mem_singleton_self _)))⟩

theorem combPk_verified (hC : Weierstrass.Law Spec.Secp256k1.curve) :
    Verified Arm.target publicKeySecp256k1Comb (combPkSpec false) :=
  combPkWith_verified hC false combPk_ct

theorem combPkU_verified (hC : Weierstrass.Law Spec.Secp256k1.curve) :
    Verified Arm.target publicKeySecp256k1CombU (combPkSpec true) :=
  combPkWith_verified hC true combPkU_ct

end VG.Proof.EcKey.Arm.Secp256k1
