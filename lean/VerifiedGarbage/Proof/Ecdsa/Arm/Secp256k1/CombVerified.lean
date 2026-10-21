module

import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombMain
public import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombCT
import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombSat
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
public import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombContract

/-! The generator comb satisfies the public signing API with its ROM constants. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Arm.Secp256k1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm

def combSignLocal : Contract isa where
  pre := combSignPre
  post := SignPost secp256k1
  pub := combSignPub

theorem combSign_verified (hC : Weierstrass.Law Spec.Secp256k1.curve) :
    Verified Arm.target signSecp256k1Comb combSignSpec := by
  refine Verified.of_correct (k := combSignLocal) (fun s hs => ?_) combSign_ct
    ⟨fun _ h => combSign_pre h,?_,?_,⟨VG.Proof.Secp256k1.Arm.combSatState,combSign_sat⟩⟩
  · obtain ⟨tr,t,exec,keep,post⟩ := combSign_ok hC hs
    exact ⟨tr,t,exec,abi_of_saved keep.saved keep.sp,post⟩
  · intro s t _ post
    sig_post [combSignSpec,Spec.Ecdsa.Secp256k1.inst,Spec.Ecdsa.Instance.signContract,
      Spec.Ecdsa.Instance.signSig,Spec.Secp256k1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr,stackArgAddr,BitVec.add_zero,Abi.withConsts]
    rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
    exact post
  · intro s t _ _ pub
    sig_pub [combSignSpec,Spec.Ecdsa.Secp256k1.inst,Spec.Ecdsa.Instance.signContract,
      Spec.Ecdsa.Instance.signSig,Spec.Secp256k1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr,stackArgAddr,BitVec.add_zero,secp256k1CombConsts,Abi.withConsts] at pub
    obtain ⟨sp,sy,h0,h1,h2,h3,ha⟩ := pub
    exact ⟨⟨sp,h0,h1,h2,h3,ha⟩,sy⟩

end VG.Proof.Ecdsa.Arm.Secp256k1
