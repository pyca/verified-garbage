module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPublic
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.LitErase
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Ecdh.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.Tables
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.GContract
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.PubVerify
import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx

/-! The existing verification contract makes all inputs to the joint routine public. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG.Proof.Ecdsa.X86_64
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Proof.Weierstrass VG.Proof.Ecdh.X86_64
open VG.Impl.P256.X86_64 (p256v p256vx p256GTab)
open VG.Proof.Weierstrass.X86_64 (InvSounds)

theorem p256v_ok (hI : InvSounds) : CfgOk p256v := cfgOk_gtab (p256_ok hI) _

theorem p256vx_ok (hI : InvSounds) : CfgOk p256vx := cfgOk_gtab (p256x_ok hI) _

theorem preG_of {s : State} (h : verifyGX86_64.pre s) : VPre p256v s := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, p256v_combConsts, show p256v.C.len = 32 from rfl]; simp only [Abi.constRegions_cons,
    Abi.constRegions_nil, List.cons_append, List.nil_append], h2, h3, h4, h5, h7, ?_⟩
  rw [TblsHeld, p256v_combConsts, Abi.constRegions_cons, Abi.constRegions_nil, Sig.forall_mem_const_single]
  refine ⟨fun c hc => ?_, fit, fun r hr => hdw r ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    simp [hr]

theorem preG_of_x {s : State} (h : verifyGX86_64.pre s) : VPre p256vx s :=
  { preG_of h with }

theorem jointPublic_of_spec {a b : State}
    (pub : (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256v.combConsts)).pub a b) :
    JointPublic p256v p256GTab a b := by
  sig_pub [Spec.Ecdsa.P256.inst,Spec.Ecdsa.Instance.verifyContract,Spec.Ecdsa.Instance.verifySig,
    Spec.P256.curve,Spec.Ecdsa.scratchWords,X86_64.abi,X86_64.argRegs,p256v_combConsts,
    Abi.withConsts] at pub
  obtain ⟨_,hsy,inputs,h0,h1,h2,h3⟩ := pub
  have eqBytes := (List.map_inj_right (fun (a b : BitVec 8) h => BitVec.eq_of_toNat_eq h)).mp inputs
  have parts := List.append_inj eqBytes (by simp only [List.length_append,length_bytesAt])
  have kd := List.append_inj parts.1 (by simp only [length_bytesAt])
  have key := kd.1
  rw [peer_bytes _ _ 32,peer_bytes _ _ 32] at key
  obtain ⟨tag,xy⟩ := List.cons.inj key
  have coords := List.append_inj xy (by simp only [length_bytesAt])
  have sig := parts.2
  change Spec.Ecdsa.bytesAt a.mem (a.gpr .rdx) (32+32)=
    Spec.Ecdsa.bytesAt b.mem (b.gpr .rdx) (32+32) at sig
  rw [bytesAt_add,bytesAt_add] at sig
  have rs := List.append_inj sig (by simp only [length_bytesAt])
  refine ⟨Taint.agree_ofRegs ?_,hsy,tag,congrArg Spec.Weierstrass.ofBytes coords.1,
    congrArg Spec.Weierstrass.ofBytes coords.2,
    congrArg (fun bs => Spec.Weierstrass.ofBytes bs >>> p256v.sh) kd.2,
    congrArg Spec.Weierstrass.ofBytes rs.1,congrArg Spec.Weierstrass.ofBytes rs.2⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

end VG.Proof.Ecdsa.Verify.X86_64
