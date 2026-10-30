module

public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingInput
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Bignum.Octets

/-! # The shared verification contract as machine-level resources -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem stackArgs_four (s : State) : List.map (stackArg s) (List.range 4) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3] := rfl

structure VerifyingABI (s : State) : Prop where
  stackBound : (s.gpr .rsp).toNat + 40 ≤ 2 ^ 64
  rd : s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
    ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArgAddr s 0, 32⟩]
  wr : s.wr = [⟨stackArg s 2, (stackArg s 3).toNat * 8⟩]
  keyScratch : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
  signatureScratch : (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
  digestScratch : (⟨stackArg s 0, (stackArg s 1).toNat⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
  scratchArgs : (⟨stackArg s 2, (stackArg s 3).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 32⟩
  retScratch : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
  keyBound : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  signatureBound : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  digestBound : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  scratchBound : (stackArg s 2).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .rdx).toNat (s.gpr .rcx).toNat
  keyLength : (s.gpr .rsi).toNat = 3 * (s.gpr .rdx).toNat + (s.gpr .rcx).toNat
  signatureLength : (s.gpr .r9).toNat = 2 * (s.gpr .rcx).toNat
  scratchLength : Spec.Dsa.scratchWords (s.gpr .rdx).toNat ≤ (stackArg s 3).toNat

theorem verifyingABI_of {s : State} (h : (Spec.Dsa.verifyContract abi).pre s) : VerifyingABI s := by
  sig_pre [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four, List.range, List.range.loop] at h
  sig_pre [Spec.Dsa.verifyContract, Spec.Dsa.verifySig, abi, argRegs, stackArgs_four, List.range, List.range.loop] at h
  sig_split h
  constructor <;> with_reducible assumption

def VerifyingABI.input {s : State} (h : VerifyingABI s) : VerifyingInput where
  base := stackArg s 2
  digestPointer := stackArg s 0
  pLen := (s.gpr .rdx).toNat
  qLen := (s.gpr .rcx).toNat
  key := Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
  signature := Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat
  digest := Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat
  lengths := h.lengths
  keyLength := (bytesAt_length _ _ _).trans h.keyLength
  signatureLength := (bytesAt_length _ _ _).trans h.signatureLength
  digestBound := by rw [bytesAt_length]; exact (stackArg s 1).isLt

theorem VerifyingABI.used {s : State} (h : VerifyingABI s) : usedBytes ≤ (stackArg s 3).toNat * 8 := by
  have hl := h.lengths
  have hs := h.scratchLength
  unfold Spec.Dsa.lengthsValid at hl
  unfold Spec.Dsa.scratchWords at hs
  change 15712 ≤ _
  omega

end VG.Proof.Dsa.X86_64
