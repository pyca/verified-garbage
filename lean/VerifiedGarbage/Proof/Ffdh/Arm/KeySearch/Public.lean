module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Correct
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.Octets

/-! The shared search leakage policy fixes precisely the public descriptor
and the remaining attempt-status sequence used by the native timing proof. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Spec.Ffdh

private theorem recover {w : Nat} {a b : List (BitVec w)}
    (h : a.map BitVec.toNat = b.map BitVec.toNat) : a = b := by
  have values := congrArg (List.map (BitVec.ofNat w)) h
  simpa only [List.map_map, Function.comp_def, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.map_id'] using values

theorem public_inputs {s t : State} (hs : (keySearchContract abi stackUse).pre s)
    (ht : (keySearchContract abi stackUse).pre t) (pub : (keySearchContract abi stackUse).pub s t) :
    ∃ p, KeyInput p s ∧ KeyInput p t ∧ (searchResult p s).statuses = (searchResult p t).statuses ∧ s.sp = t.sp := by
  sig_pub [keySearchContract, keySearchSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pub
  obtain ⟨sp, leak, p0, _, p2, _, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := pub
  change (keyOfState s).dom.map BitVec.toNat ++
      (Spec.Rsa.wordsAt s.mem (State.addr (stackArg s 8)) 4).map BitVec.toNat ++
      (searchResult (keyOfState s) s).statuses =
    (keyOfState t).dom.map BitVec.toNat ++
      (Spec.Rsa.wordsAt t.mem (State.addr (stackArg t 8)) 4).map BitVec.toNat ++
      (searchResult (keyOfState t) t).statuses at leak
  simp only [List.append_assoc] at leak
  have domainSize : ((keyOfState s).dom.map BitVec.toNat).length = ((keyOfState t).dom.map BitVec.toNat).length := by
    simp only [List.length_map, keyOfState, VG.Proof.Bignum.bytesAt_length]
    rw [p6]
  obtain ⟨domainNat, rest⟩ := List.append_inj leak domainSize
  have policySize : ((Spec.Rsa.wordsAt s.mem (State.addr (stackArg s 8)) 4).map BitVec.toNat).length =
      ((Spec.Rsa.wordsAt t.mem (State.addr (stackArg t 8)) 4).map BitVec.toNat).length := by
    simp only [Spec.Rsa.wordsAt, List.length_map, List.length_range]
  obtain ⟨policyNat, statuses⟩ := List.append_inj rest policySize
  have domain := recover domainNat
  have keys := congrArg (fun xs : List Nat => xs[0]!) policyNat
  have scalars := congrArg (fun xs : List Nat => xs[1]!) policyNat
  have ks : (keyOfState s).keys = (keyOfState t).keys := by
    simpa only [keyOfState, Spec.Rsa.wordsAt, show List.range 4 = [0, 1, 2, 3] from rfl,
      List.map_cons, List.map_nil, List.getElem!_cons_zero, Nat.mul_zero, BitVec.add_zero] using keys
  have cs : (keyOfState s).scalars = (keyOfState t).scalars := by
    simpa only [keyOfState, Spec.Rsa.wordsAt, show List.range 4 = [0, 1, 2, 3] from rfl,
      List.map_cons, List.map_nil, List.getElem!_cons_succ, List.getElem!_cons_zero] using scalars
  have point : keyOfState s = keyOfState t := by
    unfold keyOfState
    rw [KeyPublic.mk.injEq]
    exact ⟨p0, p2, p4, p5, p8, p10, p12, sp, congrArg BitVec.toNat p7,
      congrArg BitVec.toNat p6, congrArg BitVec.toNat p9, congrArg BitVec.toNat p11, ks, cs, domain⟩
  refine ⟨keyOfState s, ⟨hs, rfl⟩, ⟨ht, point.symm⟩, ?_, sp⟩
  simpa only [← point] using statuses

end VG.Proof.Ffdh.Arm.KeySearch
