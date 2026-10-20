module

public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingInput
import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Bignum.Octets

/-! # The shared verification contract as machine-level resources -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem dsaVerifyStackArgs (s : State) : List.map (stackArg s) (List.range 2) =
    [stackArg s 0, stackArg s 1] := rfl

structure VerifyingABI (s : State) : Prop where
  stackBound : s.sp.toNat + 16 ≤ 2 ^ 64
  rd : s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ⟨s.gpr .x4, (s.gpr .x5).toNat⟩,
    ⟨s.gpr .x6, (s.gpr .x7).toNat⟩, ⟨stackArgAddr s 0, 16⟩]
  wr : s.wr = [⟨stackArg s 0, (stackArg s 1).toNat * 8⟩]
  keyScratch : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
  signatureScratch : (⟨s.gpr .x4, (s.gpr .x5).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
  digestScratch : (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
  scratchArgs : (⟨stackArg s 0, (stackArg s 1).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 16⟩
  keyBound : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  signatureBound : (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64
  digestBound : (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64
  scratchBound : (stackArg s 0).toNat + (stackArg s 1).toNat * 8 ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .x2).toNat (s.gpr .x3).toNat
  keyLength : (s.gpr .x1).toNat = 3 * (s.gpr .x2).toNat + (s.gpr .x3).toNat
  signatureLength : (s.gpr .x5).toNat = 2 * (s.gpr .x3).toNat
  scratchLength : Spec.Dsa.scratchWords (s.gpr .x2).toNat ≤ (stackArg s 1).toNat

theorem verifyingABI_of {s : State} (h : (Spec.Dsa.verifyContract abi).pre s) : VerifyingABI s := by
  sig_pre [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, dsaVerifyStackArgs] at h
  sig_pre [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, dsaVerifyStackArgs] at h
  sig_split h
  constructor <;> with_reducible assumption

def VerifyingABI.input {s : State} (h : VerifyingABI s) : VerifyingInput where
  base := stackArg s 0
  digestPointer := s.gpr .x6
  pLen := (s.gpr .x2).toNat
  qLen := (s.gpr .x3).toNat
  key := Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat
  signature := Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat
  digest := Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat
  lengths := h.lengths
  keyLength := (bytesAt_length _ _ _).trans h.keyLength
  signatureLength := (bytesAt_length _ _ _).trans h.signatureLength
  digestBound := by rw [bytesAt_length]; exact (s.gpr .x7).isLt

theorem VerifyingABI.used {s : State} (h : VerifyingABI s) : usedBytes ≤ (stackArg s 1).toNat * 8 := by
  have hl := h.lengths
  have hs := h.scratchLength
  unfold Spec.Dsa.lengthsValid at hl
  unfold Spec.Dsa.scratchWords at hs
  change 15712 ≤ _
  omega

end VG.Proof.Dsa.AArch64
