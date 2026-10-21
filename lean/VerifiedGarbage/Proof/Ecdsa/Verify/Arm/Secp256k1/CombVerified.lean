module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Secp256k1.CombCT
public import VerifiedGarbage.Proof.Secp256k1.Arm.CombSat
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! The generator comb satisfies the public verification contract. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.Arm.Secp256k1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Secp256k1.Arm

def combVerifySat : State := {combSatState with
  gpr := fun r => match r with | .r0 => 0x10000 | .r1 => 0x12000 | .r2 => 0x14000 | _ => 0
  rd := [⟨0x10000,65⟩,⟨0x12000,32⟩,⟨0x14000,64⟩,⟨0x100000,151552⟩]
  wr := [⟨0,8192⟩] }

theorem combVerify_sat : combVerifySpec.pre combVerifySat := by
  have held := combSat_held
  generalize eqs : combVerifySat=s
  sig_pre [combVerifySpec,Spec.Ecdsa.Secp256k1.inst,Spec.Ecdsa.Instance.verifyContract,
    Spec.Ecdsa.Instance.verifySig,Spec.Secp256k1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,
    Loc.val,State.addr,secp256k1CombConsts,Abi.withConsts,Abi.constRegions,Abi.constsHeld,stackBelow]
  subst s
  rw [comb_words_length]
  rw [comb_words_length] at held
  refine ⟨by decide,by decide,held,by decide,?_,by decide,by decide,?_⟩
  · intro r hr
    change r∈[⟨0,8192⟩] at hr
    obtain rfl := List.mem_singleton.mp hr
    exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

def combVerifyLocal : Contract isa where
  pre := combVerifyPre
  post := VPost secp256k1
  pub := combVerifyPub

theorem combVerify_verified (hC : Weierstrass.Law Spec.Secp256k1.curve) :
    Verified Arm.target verifySecp256k1Comb combVerifySpec := by
  refine Verified.of_correct (k := combVerifyLocal) (fun s hs => ?_) combVerify_ct
    ⟨fun _ h => combVerify_pre h,?_,?_,⟨combVerifySat,combVerify_sat⟩⟩
  · obtain ⟨tr,t,exec,keep,post⟩ := combVerify_ok hC hs
    exact ⟨tr,t,exec,VG.Proof.Ecdsa.Arm.abi_of_saved keep.saved keep.sp,post⟩
  · intro s t _ post
    sig_post [combVerifySpec,Spec.Ecdsa.Secp256k1.inst,Spec.Ecdsa.Instance.verifyContract,
      Spec.Ecdsa.Instance.verifySig,Spec.Secp256k1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr,Abi.withConsts]
    rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
    exact post
  · intro s t _ _ pub
    sig_pub [combVerifySpec,Spec.Ecdsa.Secp256k1.inst,Spec.Ecdsa.Instance.verifyContract,
      Spec.Ecdsa.Instance.verifySig,Spec.Secp256k1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr,secp256k1CombConsts,Abi.withConsts] at pub
    obtain ⟨sp,sy,_inputs,h0,h1,h2,h3⟩ := pub
    exact ⟨⟨sp,h0,h1,h2,h3⟩,sy⟩

end VG.Proof.Ecdsa.Verify.Arm.Secp256k1
