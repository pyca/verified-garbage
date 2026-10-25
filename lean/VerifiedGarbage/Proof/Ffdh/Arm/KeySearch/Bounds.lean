module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Tactic.CasesM
import VerifiedGarbage.Proof.Bignum.Octets

/-! Public bounded counters and native-pointer bounds supplied by the shared
key-search signature. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Spec.Ffdh

structure KeyBounds (p : KeyPublic sampling) : Prop where
  minLength : 64 ≤ p.len
  maxLength : p.len ≤ 1024
  domainLength : domainLenValid p.len p.dlen
  domainValid : domainValid p.len p.dom = true
  domSize : p.dom.length = p.dlen
  keys : p.keys ≤ 128
  scalars : p.scalars ≤ 128
  scratchSpace : Spec.Rsa.scratchWords p.len ≤ p.capacity
  randomFits : p.randLen < 2 ^ 32
  capacityFits : p.capacity < 2 ^ 32
  stackFits : (stackUse sampling) ≤ p.sp.toNat
  argsFit : p.sp.toNat + argsBytes sampling ≤ 2 ^ 32
  controlFit : p.control.toNat + 128 ≤ 2 ^ 32
  xFit : p.xp.toNat + p.len ≤ 2 ^ 32
  yFit : p.yp.toNat + p.len ≤ 2 ^ 32
  randomFit : p.rp.toNat + p.randLen ≤ 2 ^ 32
  domainFit : p.dp.toNat + p.dlen ≤ 2 ^ 32
  usedFit : p.up.toNat + 8 ≤ 2 ^ 32
  scratchFit : p.scratch.toNat + 8 * p.capacity ≤ 2 ^ 32

theorem KeyInput.bounds {p : KeyPublic sampling} {s : State} (h : KeyInput p s) : KeyBounds p := by
  cases sampling <;> (
    have pre := h.1
    cases h.2.1
    sig_pre [GenerationPolicy.searchContract, GenerationPolicy.legacySearchContract,
      cachedKeySearchContract, cachedKeySearchSig, keySearchSig, abi, argRegs,
      reduceClassify, Loc.val, State.addr] at pre
    simp only [KeyConstants.stackArg_stripConsts, KeyConstants.stackArgAddr_stripConsts] at pre
    simp only [pLenValid] at pre
    clear h
    have randBound := (stackArg s 5).isLt
    have capacityBound := (stackArg s 7).isLt
    cases_type* And
    constructor <;> simp only [keyOfState, argsBytes, GenerationPolicy.cachedContext,
      State.addr, VG.Proof.Mont.off, Bool.false_eq_true, ite_false, ite_true]
    sig_close
    all_goals first | exact VG.Proof.Bignum.bytesAt_length _ _ _ | omega_arith)

end VG.Proof.Ffdh.Arm.KeySearch
