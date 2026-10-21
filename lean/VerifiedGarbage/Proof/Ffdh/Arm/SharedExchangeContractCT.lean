module

public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangeCorrect
import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangeFnCT
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.Octets
public import Init.Data.BitVec.Basic
public import VerifiedGarbage.Impl.Ffdh.Arm.SharedExchange
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.SharedExchangePre

/-! The shared exchange timing policy is satisfied even when private values and statuses differ. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.SharedExchange
open VG VG.Arm

theorem contract_ct (backend : Bignum.Arm.MontBackend) : ConstantTime isa (Spec.Ffdh.exchangeContract abi 176).pre
    (Spec.Ffdh.exchangeContract abi 176).pub (VG.Impl.Ffdh.Arm.SharedExchange.code (VG.Impl.Bignum.Arm.MontCall.op backend.name backend.mul)) := by
  intro s t tr1 tr2 u v hs ht hp e1 e2
  obtain ⟨p, yb, xb, base, out, domain, peer, scalar, count, capacity, privateCount,
    domainBytes, peerBytes, scalarBytes, inputS⟩ := data s hs
  have peerLength (a : State) (h : (Spec.Ffdh.exchangeContract abi 176).pre a) :
      (stackArg a 4).toNat = (stackArg a 0).toNat := by
    sig_pre [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, length, _, _, _⟩ := h
    exact length
  sig_pub [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, _, p2, p3, p4, p5, p6, p7, _, p9, p10⟩ := hp
  rw [peerLength s hs, peerLength t ht, ← p2, ← p3, ← p7, ← p4] at bytes
  simp only [List.append_assoc] at bytes
  obtain ⟨domEqNat, tailEq⟩ := List.append_inj bytes
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  obtain ⟨peerEqNat, _⟩ := List.append_inj tailEq
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range])
  have recover {a b : List Byte} (h : a.map BitVec.toNat = b.map BitVec.toNat) : a = b := by
    have eq := congrArg (List.map (BitVec.ofNat 8)) h
    simpa only [List.map_map, Function.comp_def, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, List.map_id'] using eq
  have domEq := recover domEqNat
  have peerEq := recover peerEqNat
  let xb2 := Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.privateLength
  have inputT := input t ht (p := p) (yb := yb) (xb := xb2)
    (p9.symm.trans base) (p0.symm.trans out) (p2.symm.trans domain) (p7.symm.trans peer) (p5.symm.trans scalar)
    (by rw [← p4]; exact count) (by rw [← p10]; exact capacity) (by rw [← p6]; exact privateCount) ?_ ?_ rfl
  · have xLength : xb.length = p.privateLength := by
      have eq := congrArg List.length scalarBytes
      simpa only [VG.Proof.Bignum.bytesAt_length] using eq.symm
    have x2Length : xb2.length = p.privateLength := VG.Proof.Bignum.bytesAt_length _ _ _
    exact (fn_ct backend (by rw [xLength, x2Length]) s t tr1 tr2 u v ⟨inputS, inputT, sp⟩ e1 e2).1
  · rw [← p3, ← domain]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (s.gpr .r2)) (s.gpr .r3).toNat = p.dom
    rw [← domEq, domain]
    exact domainBytes
  · rw [← peer, ← count]
    change Spec.Rsa.bytesAt t.mem (BitVec.setWidth 64 (stackArg s 3)) (stackArg s 0).toNat = yb
    rw [← peerEq, peer, count]
    exact peerBytes

end VG.Proof.Ffdh.Arm.SharedExchange
