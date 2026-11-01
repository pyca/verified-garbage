module

import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombMain
public import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombCT
import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombSat
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
public import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombContract
public import VerifiedGarbage.Proof.Ecdsa.Contract

/-! The generator comb satisfies the public signing API with its ROM constants. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Arm.Secp256k1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm

def combSignLocal (u : Bool) : Contract isa where
  pre := combSignPre u
  post := SignPost (secp256k1With u)
  pub := combSignPub

theorem combSignWith_verified (hC : Weierstrass.Law Spec.Secp256k1.curve) (u : Bool)
    (hct : ConstantTime isa (combSignPre u) combSignPub (signSecp256k1CombWith u)) :
    Verified Arm.target (signSecp256k1CombWith u) combSignSpec := by
  refine Verified.of_correct (k := combSignLocal u) (fun s hs => ?_) hct
    ⟨fun _ h => combSign_pre h,?_,?_,⟨VG.Proof.Secp256k1.Arm.combSatState,combSign_sat⟩⟩
  · obtain ⟨tr,t,exec,keep,post⟩ := combSign_ok hC hs
    exact ⟨tr,t,exec,abi_of_saved keep.saved keep.sp,post⟩
  · intro s t _ post
    sig_post [combSignSpec,Spec.Ecdsa.Secp256k1.inst,Proof.Ecdsa.Instance.signContract,
      Proof.Ecdsa.Instance.signSig,Spec.Secp256k1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr,stackArgAddr,BitVec.add_zero,Abi.withConsts]
    rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
    exact post
  · intro s t _ _ pub
    sig_pub [combSignSpec,Spec.Ecdsa.Secp256k1.inst,Proof.Ecdsa.Instance.signContract,
      Proof.Ecdsa.Instance.signSig,Spec.Secp256k1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr,stackArgAddr,BitVec.add_zero,secp256k1CombConsts,Abi.withConsts] at pub
    obtain ⟨sp,sy,h0,h1,h2,h3,ha⟩ := pub
    exact ⟨⟨sp,h0,h1,h2,h3,ha⟩,sy⟩

theorem combSign_verified (hC : Weierstrass.Law Spec.Secp256k1.curve) :
    Verified Arm.target signSecp256k1Comb combSignSpec :=
  combSignWith_verified hC false combSign_ct

theorem combSignU_verified (hC : Weierstrass.Law Spec.Secp256k1.curve) :
    Verified Arm.target signSecp256k1CombU combSignSpec :=
  combSignWith_verified hC true combSignU_ct

end VG.Proof.Ecdsa.Arm.Secp256k1
