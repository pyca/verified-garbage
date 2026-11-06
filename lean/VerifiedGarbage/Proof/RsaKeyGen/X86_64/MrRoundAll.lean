module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrRound
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrExp
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Bignum.CrtExp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-!
# A candidate on x86-64: a round's ranges and witness

What a round changes (`roundRanges`), and its witness `b` from the next
`8 w` octets and whether it passes (`wtOf`, `passOf`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- What a round changes. -/
def roundRanges (w : Nat) : List (Nat × Nat) :=
  preRanges w ++ expRanges w ++ [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)]

/-- `roundRanges`'s ranges, in the header and in the arrays. -/
theorem roundRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w [(200, 8), (240, 8), (208, 8), (224, 8), (248, 8), (176, 8), (216, 8), (160, 8), (168, 8), (232, 8)]
    [(1, 1), (2, 1), (3, 1), (5, 1), (8, 16), (6, 1)] (roundRanges w) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append,
    expRanges, preRanges, roundRanges, tabRanges, winRanges, witRanges, Public.aX, Public.aAcc, Public.aTmp, Public.aXm, Public.aY, aX, aAcc, aTmp, aXm, aY, VG.Proof.Bignum.tabBytes, kT0, sFn, kG, kV, kWords, kBits, kFlag, kPlen, kI, kElen, kU, kUni, kP, kStat, kT1, kT2, kUsed] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr ⟨(1, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inr ⟨(2, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(3, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(5, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(8, 16), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(2, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(3, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(6, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inr ⟨(2, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(3, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(6, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(5, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inl (by decide)

/-- The witness of a round, and whether it passes. -/
abbrev wtOf (c w used : Nat) (r : List Byte) : Nat × Bool :=
  Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))

abbrev passOf (c w used : Nat) (r : List Byte) : Bool :=
  Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2 (wtOf c w used r).1

end VG.Proof.RsaKeyGen.X86_64
