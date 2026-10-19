module

public import VerifiedGarbage.Proof.Dsa.X86_64.SigningInput
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Bignum.Octets

/-! # The signing ABI and its shared-contract precondition -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem stackArgs_five (s : State) : List.map (stackArg s) (List.range 5) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4] := rfl

structure SigningABI (s : State) : Prop where
  stackBound : (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64
  rd : s.rd = [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r9, (stackArg s 0).toNat⟩,
    ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArgAddr s 0, 40⟩]
  wr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩]
  outScratch : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  keyScratch : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  nonceScratch : (⟨s.gpr .r9, (stackArg s 0).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  digestScratch : (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  scratchArgs : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  retScratch : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  retOut : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  outBound : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  keyBound : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  nonceBound : (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  digestBound : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64
  scratchBound : (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .r8).toNat (stackArg s 0).toNat
  outLength : (s.gpr .rsi).toNat = 2 * (stackArg s 0).toNat
  keyLength : (s.gpr .rcx).toNat = 3 * (s.gpr .r8).toNat + 2 * (stackArg s 0).toNat
  scratchLength : Spec.Dsa.scratchWords (s.gpr .r8).toNat ≤ (stackArg s 4).toNat

theorem signingABI_of {s : State} (h : (Spec.Dsa.signContract abi).pre s) : SigningABI s := by
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five] at h
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five] at h
  sig_split h
  constructor <;> with_reducible assumption

def SigningABI.input {s : State} (h : SigningABI s) : SigningInput where
  base := stackArg s 3
  digestPointer := stackArg s 1
  pLen := (s.gpr .r8).toNat
  qLen := (stackArg s 0).toNat
  key := Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat
  nonce := Spec.Rsa.bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat
  digest := Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat
  lengths := h.lengths
  keyLength := (bytesAt_length _ _ _).trans h.keyLength
  nonceLength := bytesAt_length _ _ _
  digestBound := by rw [bytesAt_length]; exact (stackArg s 2).isLt

theorem SigningABI.used {s : State} (h : SigningABI s) : usedBytes ≤ (stackArg s 4).toNat * 8 := by
  have hl := h.lengths
  have hs := h.scratchLength
  unfold Spec.Dsa.lengthsValid at hl
  unfold Spec.Dsa.scratchWords at hs
  change 15712 ≤ _
  omega

end VG.Proof.Dsa.X86_64
