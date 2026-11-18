module

public import VerifiedGarbage.Proof.Secp256k1.Arm.CombSat
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

def combPkPub (s t : State) : Prop := pkArm.pub s t ∧ s.syms secp256k1Comb.tsym=t.syms secp256k1Comb.tsym

theorem combPk_ct : ConstantTime isa (combPkPre false) combPkPub publicKeySecp256k1Comb := by
  refine VG.Taint.constantTime (A := taintSym [secp256k1Comb.tsym]) (Taint.ofRegs [.r0,.r1,.r2]) ?_
    (by native_taint_decide)
  intro s t _ _ ⟨⟨_,h0,h1,h2⟩,sy⟩
  refine ⟨Taint.agree_ofRegs (fun r hr => ?_),fun n hn => ?_⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    exacts [h0,h1,h2]
  · obtain rfl := List.mem_singleton.mp hn
    exact sy

theorem combPkU_ct : ConstantTime isa (combPkPre true) combPkPub publicKeySecp256k1CombU := by
  refine VG.Taint.constantTime (A := taintSymU [secp256k1Comb.tsym]) (Taint.ofRegs [.r0,.r1,.r2]) ?_
    (by taint_decide)
  intro s t _ _ ⟨⟨_,h0,h1,h2⟩,sy⟩
  refine ⟨Taint.agree_ofRegs (fun r hr => ?_),fun n hn => ?_⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    exacts [h0,h1,h2]
  · obtain rfl := List.mem_singleton.mp hn
    exact sy

end VG.Proof.EcKey.Arm.Secp256k1

end

end

/-! The public-key API uses the same checked generator comb as signing. -/

@[expose] public section
namespace VG.Proof.EcKey.Arm.Secp256k1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Secp256k1.Arm

def combPkSat : State := {combSatState with
  gpr := fun r => match r with | .r0 => 0x10000 | .r1 => 0x12000 | _ => 0
  rd := [⟨0x12000,32⟩,⟨0x100000,151552⟩]
  wr := [⟨0x10000,65⟩,⟨0,8192⟩] }

theorem combPk_sat : combPkSpec.pre combPkSat := by
  have held := combSat_held
  generalize eqs : combPkSat=s
  sig_pre [combPkSpec,Spec.EcKey.Secp256k1.inst,Spec.EcKey.Instance.publicKeyContract,
    Spec.EcKey.Instance.publicKeySig,Spec.Secp256k1.curve,Spec.EcKey.scratchWords,abi,argRegs,reduceClassify,
    Loc.val,State.addr,secp256k1CombConsts,Abi.withConsts,Abi.constRegions_cons,Abi.constRegions_nil,Abi.constsHeld,
    stackBelow]
  subst s
  rw [comb_words_length]
  rw [comb_words_length] at held
  refine ⟨by decide,by decide,held,by decide,?_,by decide,by decide,?_⟩
  · intro r hr
    change r∈[⟨0x10000,65⟩,⟨0,8192⟩] at hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

def combPkLocal (u : Bool) : Contract isa where
  pre := combPkPre u
  post := PkPost (secp256k1With u)
  pub := combPkPub

theorem combPkWith_verified (hC : Weierstrass.Law Spec.Secp256k1.curve) (u : Bool)
    (hct : ConstantTime isa (combPkPre u) combPkPub (publicKeySecp256k1CombWith u)) :
    Verified Arm.target (publicKeySecp256k1CombWith u) combPkSpec := by
  refine Verified.of_correct (k := combPkLocal u) (fun s hs => ?_) hct
    ⟨fun _ h => combPk_pre h,?_,?_,⟨combPkSat,combPk_sat⟩⟩
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
    sig_pub [combPkSpec,Spec.EcKey.Secp256k1.inst,Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig,Spec.Secp256k1.curve,Spec.EcKey.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr,secp256k1CombConsts,Abi.withConsts] at pub
    obtain ⟨sp,sy,h0,h1,h2⟩ := pub
    exact ⟨⟨sp,h0,h1,h2⟩,sy⟩

theorem combPk_verified (hC : Weierstrass.Law Spec.Secp256k1.curve) :
    Verified Arm.target publicKeySecp256k1Comb combPkSpec :=
  combPkWith_verified hC false combPk_ct

theorem combPkU_verified (hC : Weierstrass.Law Spec.Secp256k1.curve) :
    Verified Arm.target publicKeySecp256k1CombU combPkSpec :=
  combPkWith_verified hC true combPkU_ct

end VG.Proof.EcKey.Arm.Secp256k1
