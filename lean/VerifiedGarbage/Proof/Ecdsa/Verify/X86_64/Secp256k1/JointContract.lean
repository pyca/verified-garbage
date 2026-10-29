module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Secp256k1.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPublic
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.PubVerify
public import VerifiedGarbage.Impl.Secp256k1.X86_64.Joint
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Ecdh.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.Verified

/-!
# ECDSA verification over secp256k1 on x86-64: the joint verifier's curve and contract

`secp256k1v` is `secp256k1` with `pubVerify`, which only verification reads,
and with the table of the generator's multiples: the same curve, layout and
multiplications, so the same facts (`secp256k1v_ok`, from `secp256k1_ok`:
those that do not need `a = -3`), and the contract's precondition gives
theirs (`pre_of`). The shared contract makes the key, the digest and the
signature public (`jointPublic_of_spec`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.Secp256k1

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Secp256k1.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.Secp256k1 VG.Proof.Weierstrass VG.Proof.Ecdh.X86_64
open VG.Proof.Weierstrass.X86_64 (InvSounds)

theorem secp256k1v_ok (hI : InvSounds) : BaseCfgOk secp256k1v :=
  baseCfgOk_pubVerify_gtab (secp256k1_ok hI) rfl true _

theorem pre_of {s : State} (h : verifyX86_64.pre s) : VPre secp256k1v s := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, secp256k1v_combConsts, show secp256k1v.C.len = 32 from rfl]; simp only [Abi.constRegions_cons,
    Abi.constRegions_nil, List.cons_append, List.nil_append], h2, h3, h4, h5, h7, ?_⟩
  rw [TblsHeld, secp256k1v_combConsts, Abi.constRegions_cons, Abi.constRegions_nil, Sig.forall_mem_const_single]
  refine ⟨fun c hc => ?_, fit, fun r hr => hdw r ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    simp [hr]

theorem jointPublic_of_spec {a b : State}
    (pub : (Spec.Ecdsa.Secp256k1.inst.verifyContract (X86_64.abi.withConsts secp256k1v.combConsts)).pub a b) :
    JointPublic secp256k1v secp256k1GTab a b := by
  sig_pub [Spec.Ecdsa.Secp256k1.inst,Spec.Ecdsa.Instance.verifyContract,Spec.Ecdsa.Instance.verifySig,
    Spec.Secp256k1.curve,Spec.Ecdsa.scratchWords,X86_64.abi,X86_64.argRegs,secp256k1v_combConsts,
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
    congrArg (fun bs => Spec.Weierstrass.ofBytes bs >>> secp256k1v.sh) kd.2,
    congrArg Spec.Weierstrass.ofBytes rs.1,congrArg Spec.Weierstrass.ofBytes rs.2⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

end VG.Proof.Ecdsa.Verify.X86_64.Secp256k1
