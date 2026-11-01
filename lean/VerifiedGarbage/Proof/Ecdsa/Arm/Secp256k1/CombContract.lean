module

public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.NatPairs
import Mathlib.Logic.Function.Basic
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.Arm
public import VerifiedGarbage.Impl.Weierstrass.Arm.TCombSecp256k1
import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Verified
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Weierstrass.MulContract

/-! The existing ECDSA contract with its read-only comb table. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Arm.Secp256k1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm

abbrev combSignSpec : Contract isa :=
  Proof.Ecdsa.Instance.signContract Spec.Ecdsa.Secp256k1.inst (abi.withConsts secp256k1CombConsts)

def combSignPre (u : Bool) (s : State) : Prop :=
  Pre (secp256k1With u) s (constRegs secp256k1CombConsts s) ∧ ConstsOk secp256k1CombConsts 0 s

theorem sign_spec_pre {u : Bool} {s : State}
    (h : (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.Secp256k1.inst abi).pre s) : Pre (secp256k1With u) s := by
  sig_pre [Spec.Ecdsa.Secp256k1.inst,Proof.Ecdsa.Instance.signContract,Proof.Ecdsa.Instance.signSig,
    Spec.Secp256k1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,Loc.val,State.addr,stackArgAddr,
    BitVec.add_zero] at h
  obtain ⟨sp,rd,wr,_od,_oh,_ok,os,oa,ds,hs,ks,sa,fo,fd,fh,fk,fs⟩ := h
  exact ⟨rd,wr,os,ds,hs,ks,oa,sa,fo,fd,fh,fk,fs,sp⟩

theorem combSign_pre {u : Bool} {s : State} (h : combSignSpec.pre s) : combSignPre u s := by
  have hp : (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.Secp256k1.inst abi).pre (stripConsts secp256k1CombConsts s) ∧
      ConstsOk secp256k1CombConsts 0 s := pre_consts.mp h
  have p := sign_spec_pre (u := u) hp.1
  refine ⟨⟨?_,p.wr,p.out_sc,p.d_sc,p.digest_sc,p.k_sc,p.out_args,p.sc_args,
    p.out_fit,p.d_fit,p.digest_fit,p.k_fit,p.sc_fit,p.sp_fit⟩,hp.2⟩
  rw [← List.take_append_drop (s.rd.length-secp256k1CombConsts.length) s.rd,hp.2.1]
  exact congrArg (fun rs => rs++constRegs secp256k1CombConsts s) p.rd

end VG.Proof.Ecdsa.Arm.Secp256k1
