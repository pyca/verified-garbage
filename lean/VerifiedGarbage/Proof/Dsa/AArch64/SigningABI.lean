module

public import VerifiedGarbage.Proof.Dsa.AArch64.SigningInput
import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Bignum.Octets
public import Mathlib.Algebra.Group.Nat.Defs

/-! # The signing ABI and its shared-contract precondition -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem dsaSignStackArgs (s : State) : List.map (stackArg s) (List.range 3) =
    [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

structure SigningABI (s : State) : Prop where
  stackBound : s.sp.toNat + 24 ≤ 2 ^ 64
  rd : s.rd = [⟨s.gpr .x2, (s.gpr .x3).toNat⟩, ⟨s.gpr .x5, (s.gpr .x6).toNat⟩,
    ⟨s.gpr .x7, (stackArg s 0).toNat⟩, ⟨stackArgAddr s 0, 24⟩]
  wr : s.wr = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩]
  outScratch : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  keyScratch : (⟨s.gpr .x2, (s.gpr .x3).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  nonceScratch : (⟨s.gpr .x5, (s.gpr .x6).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  digestScratch : (⟨s.gpr .x7, (stackArg s 0).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
  scratchArgs : (⟨stackArg s 1, (stackArg s 2).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 24⟩
  outBound : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  keyBound : (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64
  nonceBound : (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64
  digestBound : (s.gpr .x7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  scratchBound : (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .x4).toNat (s.gpr .x6).toNat
  outLength : (s.gpr .x1).toNat = 2 * (s.gpr .x6).toNat
  keyLength : (s.gpr .x3).toNat = 3 * (s.gpr .x4).toNat + 2 * (s.gpr .x6).toNat
  scratchLength : Spec.Dsa.scratchWords (s.gpr .x4).toNat ≤ (stackArg s 2).toNat

theorem signingABI_of {s : State} (h : (Spec.Dsa.signContract abi).pre s) : SigningABI s := by
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs] at h
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs] at h
  sig_split h
  constructor <;> with_reducible assumption

def SigningABI.input {s : State} (h : SigningABI s) : SigningInput where
  base := stackArg s 1
  digestPointer := s.gpr .x7
  pLen := (s.gpr .x4).toNat
  qLen := (s.gpr .x6).toNat
  key := Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat
  nonce := Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat
  digest := Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat
  lengths := h.lengths
  keyLength := (bytesAt_length _ _ _).trans h.keyLength
  nonceLength := bytesAt_length _ _ _
  digestBound := by rw [bytesAt_length]; exact (stackArg s 0).isLt

theorem SigningABI.used {s : State} (h : SigningABI s) : usedBytes ≤ (stackArg s 2).toNat * 8 := by
  have hl := h.lengths
  have hs := h.scratchLength
  unfold Spec.Dsa.lengthsValid at hl
  unfold Spec.Dsa.scratchWords at hs
  change 15712 ≤ _
  omega

end VG.Proof.Dsa.AArch64
