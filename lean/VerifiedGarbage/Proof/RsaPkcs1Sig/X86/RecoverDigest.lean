module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverLocal

/-! # Locate the trailing digest within the recovered encoding -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86 VG.Impl.RsaPkcs1Sig.X86.Verify

namespace Geometry

def digest (g : Geometry) : BitVec 32 := g.em1 + BitVec.ofNat 32 (g.length - g.outputLength)

theorem Valid.outputPositive {g : Geometry} (h : g.Valid) : 0 < g.outputLength := by
  obtain ⟨hash, _, eq⟩ := h.hashValid
  rw [eq]
  cases hash <;> decide

theorem Valid.outputBound {g : Geometry} (h : g.Valid) : g.outputLength ≤ 64 := by
  obtain ⟨hash, _, eq⟩ := h.hashValid
  rw [eq]
  cases hash <;> decide

theorem Valid.outputFits {g : Geometry} (h : g.Valid) : g.outputLength ≤ g.length := by
  have := h.outputBound
  have := h.minLength
  omega

theorem Valid.em1Fit {g : Geometry} (h : g.Valid) : g.em1.toNat + g.length ≤ 2 ^ 32 :=
  h.encodingFit (by have := h.maxLength; simp only [em1Offset, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes]; omega)

theorem Valid.digestNat {g : Geometry} (h : g.Valid) :
    g.digest.toNat = g.em1.toNat + (g.length - g.outputLength) := by
  have sum : g.em1.toNat + (g.length - g.outputLength) < 2 ^ 32 := by
    have := h.em1Fit
    have := h.outputPositive
    have := h.outputFits
    omega
  unfold digest
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : g.length - g.outputLength < 2 ^ 32),
    Nat.mod_eq_of_lt sum]

theorem Valid.digestFit {g : Geometry} (h : g.Valid) : g.digest.toNat + g.outputLength ≤ 2 ^ 32 := by
  rw [h.digestNat]
  have := h.em1Fit
  have := h.outputFits
  omega

theorem Valid.digestAddr {g : Geometry} (h : g.Valid) :
    byteAddr g.digest = byteAddr g.em1 + BitVec.ofNat 64 (g.length - g.outputLength) :=
  byteAddr_add (by have := h.em1Fit; have := h.outputPositive; have := h.outputFits; omega)

theorem Valid.digestSub {g : Geometry} (h : g.Valid) :
    (⟨byteAddr g.digest, g.outputLength⟩ : Region).Sub ⟨byteAddr g.em1, g.length⟩ := by
  rw [h.digestAddr]
  exact Offset.sub_base _ (by have := h.outputFits; omega)

theorem Valid.digestPointer {g : Geometry} (h : g.Valid) :
    g.em1 + BitVec.ofNat 32 g.length - BitVec.ofNat 32 g.outputLength = g.digest := by
  have split : BitVec.ofNat 32 g.length = BitVec.ofNat 32 (g.length - g.outputLength) + BitVec.ofNat 32 g.outputLength := by
    rw [← BitVec.ofNat_add]
    congr 1
    have := h.outputFits
    omega
  rw [split, ← BitVec.add_assoc, BitVec.add_sub_cancel]
  rfl

end Geometry
end VG.Proof.RsaPkcs1Sig.X86.Rcv
