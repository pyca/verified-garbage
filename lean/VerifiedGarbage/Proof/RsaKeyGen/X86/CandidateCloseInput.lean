module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateMemory
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateInput
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.TCB.X86.State

/-! # Optional-prime distance filtering retains the drawn candidate and input snapshots -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

theorem MemoryFacts.other_choice {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (M : MemoryFacts E eBytes pBytes entropy s) :
    (if BitVec.ofNat 32 E.otherLength = 0#32 then none else
      some (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (E.other.setWidth 64) (8 * E.width)))) = Spec.RsaKeyGen.otherPrime pBytes := by
  have pLength : pBytes.length = E.otherLength := by rw [← M.otherBytes]; exact VG.Proof.Bignum.bytesAt_length _ _ _
  have lengthBound : E.otherLength < 2 ^ 32 := by
    have prime := v.length; unfold Spec.RsaKeyGen.primeLenValid at prime
    have := v.otherLength; omega
  by_cases empty : E.otherLength = 0
  · have pEmpty : pBytes = [] := List.length_eq_zero_iff.mp (by rw [pLength, empty])
    rw [empty, pEmpty]
    rfl
  · have lengthEq : E.otherLength = E.length := v.otherLength.resolve_left empty
    have pNonempty : pBytes ≠ [] := by intro nil; rw [nil] at pLength; exact empty pLength.symm
    have nativeNonzero : BitVec.ofNat 32 E.otherLength ≠ 0#32 := by
      intro zero
      have H := congrArg BitVec.toNat zero
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lengthBound] at H
      exact empty H
    simp only [nativeNonzero, ↓reduceIte, Spec.RsaKeyGen.otherPrime, pNonempty]
    rw [v.length_eq, ← lengthEq, M.otherBytes]

end VG.Proof.RsaKeyGen.X86.Candidate
