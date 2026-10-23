module

import VerifiedGarbage.Proof.Ffdh.Arm.SharedDeriveCorrect
import VerifiedGarbage.Proof.Ffdh.Arm.SharedDeriveFnCT
import VerifiedGarbage.Proof.Ffdh.Arm.SharedDerivePre
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedDerive
public import VerifiedGarbage.Spec.Ffdh.DerivePublicContract
public import VerifiedGarbage.TCB.Arm.Target

/-! The derivation's timing depends on the domain, the lengths and the status alone. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedDerive
open VG VG.Arm

theorem contract_ct (backend : Bignum.Arm.MontBackend) : ConstantTime isa
    (Spec.Ffdh.derivePublicContract abi 176).pre (Spec.Ffdh.derivePublicContract abi 176).pub
    (VG.Impl.Ffdh.Arm.SharedDerive.code (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, xb, base, out, domain, scalar, publicValue, count, capacity, privateCount,
    domainBytes, scalarBytes, inputS⟩ := data s hs
  sig_pub [Spec.Ffdh.derivePublicContract, Spec.Ffdh.derivePublicSig, abi, argRegs, reduceClassify,
    Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, p3, p4, p5, p6, p7, p8⟩ := hp
  rw [← p2, ← p3, ← p4, ← p5, ← p6] at bytes
  obtain ⟨domEqNat, statusEq⟩ := List.append_inj bytes
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  have recover {a b : List Byte} (h : a.map BitVec.toNat = b.map BitVec.toNat) : a = b := by
    have eq := congrArg (List.map (BitVec.ofNat 8)) h
    simpa only [List.map_map, Function.comp_def, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, List.map_id'] using eq
  have domEq := recover domEqNat
  let xb2 := Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.privateLength
  have domT : Spec.Rsa.bytesAt t.mem (State.addr p.domain) (s.gpr .r3).toNat = p.dom := by
    rw [← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r2)) (s.gpr .r3).toNat = p.dom
    rw [← domEq, domain]
    exact domainBytes
  have inputT := input t ht (p := p) (xb := xb2)
    (p7.symm.trans base) (p0.symm.trans out) (p2.symm.trans domain) (p5.symm.trans scalar) publicValue
    (by rw [← p4]; exact count) (by rw [← p8]; exact capacity) (by rw [← p6]; exact privateCount)
    (by rw [← p3]; exact domT) rfl
  have xLength : xb.length = p.privateLength := by
    have eq := congrArg List.length scalarBytes
    simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
  have x2Length : xb2.length = p.privateLength := VG.Proof.Bignum.bytesAt_length _ _ _
  have status : Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip xb) =
      Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf p.k p.dom) (Spec.Rsa.os2ip xb2) := by
    have eq := List.singleton_inj.mp statusEq
    simp only [State.addr] at domainBytes scalarBytes domT
    rw [count, scalar, privateCount, ← domEq, domain, domainBytes, scalarBytes] at eq
    exact eq
  have classification : (0 < Spec.Rsa.os2ip xb ∧ Spec.Rsa.os2ip xb < scalarBound p) ↔
      (0 < Spec.Rsa.os2ip xb2 ∧ Spec.Rsa.os2ip xb2 < scalarBound p) := by
    have a := keyStatus_two_iff p (Spec.Rsa.os2ip xb)
    have b := keyStatus_two_iff p (Spec.Rsa.os2ip xb2)
    rw [status] at a
    have n := a.symm.trans b
    exact ⟨fun h => Classical.byContradiction fun h2 => n.mpr h2 h,
      fun h => Classical.byContradiction fun h1 => n.mp h1 h⟩
  exact (fn_ct backend (by rw [xLength, x2Length]) classification s t tr1 tr2 u v
    ⟨inputS, inputT, sp⟩ e1 e2).1

end VG.Proof.Ffdh.Arm.SharedDerive
