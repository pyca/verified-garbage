module

public import VerifiedGarbage.Proof.EcKey.Arm.Secp256k1.CombCT
public import VerifiedGarbage.Proof.Secp256k1.Arm.CombSat
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.EcKey.Arm.Secp256k1.Verified

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
    Loc.val,State.addr,secp256k1CombConsts,Abi.withConsts,Abi.constRegions,Abi.constsHeld,stackBelow]
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

def combPkLocal : Contract isa where
  pre := combPkPre
  post := PkPost secp256k1
  pub := combPkPub

theorem combPk_verified (hC : Weierstrass.Law Spec.Secp256k1.curve) :
    Verified Arm.target publicKeySecp256k1Comb combPkSpec := by
  refine Verified.of_correct (k := combPkLocal) (fun s hs => ?_) combPk_ct
    ⟨fun _ h => combPk_pre h,?_,?_,⟨combPkSat,combPk_sat⟩⟩
  · obtain ⟨tr,t,exec,keep,post⟩ := combPk_ok hC hs
    exact ⟨tr,t,exec,VG.Proof.Ecdsa.Arm.abi_of_saved keep.saved keep.sp,post⟩
  · intro s t _ post
    sig_post [combPkSpec,Spec.EcKey.Secp256k1.inst,Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig,Spec.Secp256k1.curve,Spec.EcKey.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr,Abi.withConsts]
    have pp := post_of post
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

end VG.Proof.EcKey.Arm.Secp256k1
