module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Correct
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ConstantContract

/-! The shared search leakage sampling fixes precisely the public descriptor
and the remaining attempt-status sequence used by the native timing proof. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Spec.Ffdh

private theorem recover {w : Nat} {a b : List (BitVec w)}
    (h : a.map BitVec.toNat = b.map BitVec.toNat) : a = b := by
  have values := congrArg (List.map (BitVec.ofNat w)) h
  simpa only [List.map_map, Function.comp_def, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.map_id'] using values

private theorem public_inputs_of_args {s t : State}
    (preS : KeyInput (keyOfState sampling s) s)
    (preT : KeyInput (keyOfState sampling t) t)
    (sp : s.sp = t.sp)
    (leak : (keyOfState sampling s).dom.map BitVec.toNat ++
      (Spec.Rsa.wordsAt s.mem (State.addr (stackArg s 8)) 4).map BitVec.toNat ++
      (searchResult (keyOfState sampling s) s).statuses =
      (keyOfState sampling t).dom.map BitVec.toNat ++
      (Spec.Rsa.wordsAt t.mem (State.addr (stackArg t 8)) 4).map BitVec.toNat ++
      (searchResult (keyOfState sampling t) t).statuses)
    (p0 : s.gpr .r0 = t.gpr .r0) (p2 : s.gpr .r2 = t.gpr .r2)
    (p4 : stackArg s 0 = stackArg t 0) (p5 : stackArg s 1 = stackArg t 1)
    (p6 : stackArg s 2 = stackArg t 2) (p7 : stackArg s 3 = stackArg t 3)
    (p8 : stackArg s 4 = stackArg t 4) (p9 : stackArg s 5 = stackArg t 5)
    (p10 : stackArg s 6 = stackArg t 6) (p11 : stackArg s 7 = stackArg t 7)
    (p12 : stackArg s 8 = stackArg t 8)
    (table : KeyConstants.tablePtr sampling s = KeyConstants.tablePtr sampling t)
    (ctx : sampling.cachedContext = true → stackArg s 9 = stackArg t 9 ∧ stackArg s 10 = stackArg t 10) :
    ∃ p : KeyPublic sampling, KeyInput p s ∧ KeyInput p t ∧
      (searchResult p s).statuses = (searchResult p t).statuses ∧ s.sp = t.sp := by
  simp only [List.append_assoc] at leak
  have domainSize : ((keyOfState sampling s).dom.map BitVec.toNat).length = ((keyOfState sampling t).dom.map BitVec.toNat).length := by
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
  have ks : (keyOfState sampling s).keys = (keyOfState sampling t).keys := by
    simpa only [keyOfState, Spec.Rsa.wordsAt, show List.range 4 = [0, 1, 2, 3] from rfl,
      List.map_cons, List.map_nil, List.getElem!_cons_zero, Nat.mul_zero, BitVec.add_zero] using keys
  have cs : (keyOfState sampling s).scalars = (keyOfState sampling t).scalars := by
    simpa only [keyOfState, Spec.Rsa.wordsAt, show List.range 4 = [0, 1, 2, 3] from rfl,
      List.map_cons, List.map_nil, List.getElem!_cons_succ, List.getElem!_cons_zero] using scalars
  have point : keyOfState sampling s = keyOfState sampling t := by
    unfold keyOfState
    rw [KeyPublic.mk.injEq]
    refine ⟨p0, p2, p4, p5, p8, p10, p12, sp, congrArg BitVec.toNat p7,
      congrArg BitVec.toNat p6, congrArg BitVec.toNat p9, congrArg BitVec.toNat p11, ks, cs, domain, table, ?_, ?_⟩
    · by_cases active : sampling.cachedContext = true
      · simp only [active, ite_true]; exact (ctx active).1
      · simp only [active, Bool.false_eq_true, ite_false]
    · by_cases active : sampling.cachedContext = true
      · simp only [active, ite_true]; exact congrArg BitVec.toNat (ctx active).2
      · simp only [active, Bool.false_eq_true, ite_false]
  refine ⟨keyOfState sampling s, preS, ⟨preT.1, point.symm, preT.2.2⟩, ?_, sp⟩
  simpa only [← point] using statuses


theorem public_inputs {s t : State} (hs : (GenerationPolicy.searchContract sampling (KeyConstants.abi sampling) (stackUse sampling)).pre s)
    (ht : (GenerationPolicy.searchContract sampling (KeyConstants.abi sampling) (stackUse sampling)).pre t) (pub : (GenerationPolicy.searchContract sampling (KeyConstants.abi sampling) (stackUse sampling)).pub s t) :
    ∃ p : KeyPublic sampling, KeyInput p s ∧ KeyInput p t ∧ (searchResult p s).statuses = (searchResult p t).statuses ∧ s.sp = t.sp := by
  have partsS := selected_pre.mp hs
  have partsT := selected_pre.mp ht
  have preS : KeyInput (keyOfState sampling s) s := ⟨partsS.1, rfl, partsS.2⟩
  have preT : KeyInput (keyOfState sampling t) t := ⟨partsT.1, rfl, partsT.2⟩
  obtain ⟨pub, table⟩ := selected_pub.mp pub
  cases sampling <;>
    sig_pub [GenerationPolicy.searchContract, GenerationPolicy.legacySearchContract,
      cachedKeySearchContract, cachedKeySearchSig, keySearchSig, abi, argRegs,
      reduceClassify, Loc.val, State.addr] at pub
  · obtain ⟨sp, leak, p0, _, p2, _, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := pub
    exact public_inputs_of_args preS preT sp leak p0 p2 p4 p5 p6 p7 p8 p9 p10 p11 p12 table (by intro h; cases h)
  · obtain ⟨sp, leak, p0, _, p2, _, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := pub
    exact public_inputs_of_args preS preT sp leak p0 p2 p4 p5 p6 p7 p8 p9 p10 p11 p12 table (by intro h; cases h)
  · obtain ⟨sp, leak, p0, _, p2, _, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14⟩ := pub
    exact public_inputs_of_args preS preT sp leak p0 p2 p4 p5 p6 p7 p8 p9 p10 p11 p12 table (fun _ => ⟨p13, p14⟩)

end VG.Proof.Ffdh.Arm.KeySearch
