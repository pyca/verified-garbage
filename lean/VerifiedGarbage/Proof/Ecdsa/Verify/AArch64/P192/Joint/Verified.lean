module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Joint.Public
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Contract
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Verified
import VerifiedGarbage.Proof.Ecdsa.AArch64.P192.Config
import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Joint.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Joint.Lit
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Joint.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Hash
public import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Hash
meta import VerifiedGarbage.Impl.Ecdsa.AArch64.VerifyHash
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Spec.Ecdsa.P192
meta import VerifiedGarbage.Spec.Ecdsa.P192
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Contract

/-! The joint verifier implements the unchanged public ECDSA contract. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P192.Joint
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P192
open VG.Impl.Ecdsa.Verify.AArch64.P192.Joint

theorem public_of_spec {s t : State}
    (pub : (Spec.Ecdsa.P192.inst.verifyContract AArch64.abi).pub s t) : Public s t := by
  sig_pub [Spec.Ecdsa.P192.inst,Spec.Ecdsa.Instance.verifyContract,Spec.Ecdsa.Instance.verifySig,
    Spec.P192.curve,Spec.Ecdsa.scratchWords,AArch64.abi,AArch64.argRegs] at pub
  obtain ⟨hsp,inputs,h0,h1,h2,h3⟩ := pub
  refine ⟨⟨hsp,fun r hr => ?_⟩,?_,?_⟩
  · simp only [Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  all_goals
    have eqBytes := (List.map_inj_right (fun (a b : BitVec 8) h => BitVec.eq_of_toNat_eq h)).mp inputs
    have parts := List.append_inj eqBytes (by simp only [List.length_append,Weierstrass.length_bytesAt])
    have front := List.append_inj parts.1 (by simp only [Weierstrass.length_bytesAt])
  · exact front.2
  · exact parts.2

theorem verify_a64 (hL : Weierstrass.Law Spec.P192.curve)
    (hI : Weierstrass.AArch64.InvSounds) (s : State) (hs : verifyAArch64.pre s) :
    ∃ t s',Exec isa verify s t s' ∧ abiPreserved s s' ∧ verifyAArch64.post s s' := by
  obtain ⟨t,s',he,hsv,hpost⟩ := verify_ok (p192_ok hI) hL (pre_of hs)
  exact ⟨t,s',he,abiPreserved_of he (by lit_decide) (by lit_decide) (by lit_decide) hsv,hpost⟩

theorem verify_verified (hL : Weierstrass.Law Spec.P192.curve)
    (hI : Weierstrass.AArch64.InvSounds) :
    Verified AArch64.target verify (Spec.Ecdsa.P192.inst.verifyContract AArch64.abi) := by
  refine ⟨?_,?_,implies.sat⟩
  · intro s hs
    obtain ⟨t,s',he,ha,hp⟩ := verify_a64 hL hI s (implies.pre s hs)
    exact ⟨t,s',he,ha,implies.post s s' hs hp⟩
  · intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
    exact verify_ct (p192_ok hI) hL _ _ _ _ _ _
      (pre_of (implies.pre _ pre₁)) (pre_of (implies.pre _ pre₂)) (public_of_spec pub) e₁ e₂

/-- `P192.satState` satisfies the precondition of the verification of the `len` bytes. -/
theorem sat_spec : (Spec.Ecdsa.P192.inst.verifyContract AArch64.abi).pre P192.satState := by
  sig_pre [Spec.Ecdsa.P192.inst, Spec.Ecdsa.Instance.verifyContract, Spec.Ecdsa.Instance.verifySig,
    Spec.P192.curve, Spec.Ecdsa.scratchWords, AArch64.abi, AArch64.argRegs, P192.satState]
  repeat' (first | exact Region.disjoint_of_sep (by decide) | decide | rfl | constructor)

/-- `vg_ecdsa_p192_verify`, taking the hash function's output: the
verification above, run on the `len` bytes of the hash
(`Hash.verifyHash_verified_nil`). -/
theorem verifyHash_verified (hL : Weierstrass.Law Spec.P192.curve) (hI : Weierstrass.AArch64.InvSounds) :
    Verified AArch64.target
      (Impl.Ecdsa.AArch64.VerifyHash.verifyHash Spec.Ecdsa.P192.inst.curve.len false verify)
      (Spec.Ecdsa.P192.inst.verifyHashContract AArch64.abi 80) :=
  Hash.verifyHash_verified_nil Proof.Ecdsa.Verify.p192_len (by decide) (verify_verified hL hI)
    (by taint_decide) (Hash.hashSat_nil (by decide) sat_spec (by decide) fun r hr => by
      simp only [P192.satState, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

end VG.Proof.Ecdsa.Verify.AArch64.P192.Joint
