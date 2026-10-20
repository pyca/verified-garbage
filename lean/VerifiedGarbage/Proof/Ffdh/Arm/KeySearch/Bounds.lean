module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.Octets

/-! Public bounded counters and native-pointer bounds supplied by the shared
key-search signature. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Spec.Ffdh

structure KeyBounds (p : KeyPublic) : Prop where
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
  stackFits : stackUse ≤ p.sp.toNat
  argsFit : p.sp.toNat + 36 ≤ 2 ^ 32
  controlFit : p.control.toNat + 128 ≤ 2 ^ 32
  xFit : p.xp.toNat + p.len ≤ 2 ^ 32
  yFit : p.yp.toNat + p.len ≤ 2 ^ 32
  randomFit : p.rp.toNat + p.randLen ≤ 2 ^ 32
  domainFit : p.dp.toNat + p.dlen ≤ 2 ^ 32
  usedFit : p.up.toNat + 8 ≤ 2 ^ 32
  scratchFit : p.scratch.toNat + 8 * p.capacity ≤ 2 ^ 32

theorem KeyInput.bounds {p : KeyPublic} {s : State} (h : KeyInput p s) : KeyBounds p := by
  have pre := h.1
  cases h.2
  sig_pre [keySearchContract, keySearchSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at pre
  obtain ⟨stackFit, argsFit, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, xFit, yFit, usedFit, domainFit, randomFit, scratchFit, controlFit, lengths, domainLength, xLen, yLen, scratchSpace, domainValid, keys, scalars, _⟩ := pre
  rw [xLen] at xFit
  rw [yLen] at yFit
  refine ⟨lengths.1, lengths.2, domainLength, domainValid, ?_, keys, scalars, scratchSpace,
    (stackArg s 5).isLt, (stackArg s 7).isLt, stackFit, ?_, ?_, xFit, yFit,
    randomFit, domainFit, ?_, ?_⟩
  · exact VG.Proof.Bignum.bytesAt_length _ _ _
  · change s.sp.toNat + 36 ≤ 2 ^ 32
    omega
  · change (stackArg s 8).toNat + 128 ≤ 2 ^ 32
    omega
  · change (stackArg s 0).toNat + 8 ≤ 2 ^ 32
    omega
  · change (stackArg s 6).toNat + 8 * (stackArg s 7).toNat ≤ 2 ^ 32
    simpa only [Nat.mul_comm] using scratchFit

end VG.Proof.Ffdh.Arm.KeySearch
