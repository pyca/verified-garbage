module

public import VerifiedGarbage.Proof.MillerRabin.X86.StageProduct

/-! # Immutable inputs shared by the round's operational proofs -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

structure RoundFacts (σ : State) (base : Addr) (bytes w : Nat) : Prop where
  lower : 4 ≤ w
  upper : w ≤ 128
  fit : arrAt w 28 ≤ bytes
  width : σ.mem.readW (off base 48) 32 = BitVec.ofNat 32 w
  length : ∃ len : BitVec 32, bytes = len.toNat * 8 ∧
    σ.mem.readW (off (byteAddr (σ.gpr .esp)) VG.Impl.MillerRabin.X86.savedLength) 32 = len
  inverse : (val32 σ.mem base 256 (2 * w) * w32 σ.mem base 56 + 1) % 2 ^ 32 = 0
  odd : val32 σ.mem base 256 (2 * w) % 2 = 1
  one : numAt σ.mem base w 9 < val32 σ.mem base 256 (2 * w)
  witness : numAt σ.mem base w 5 < val32 σ.mem base 256 (2 * w)

namespace RoundFacts

theorem multiply {σ s : State} {base : Addr} {bytes w o a b : Nat}
    (facts : RoundFacts σ base bytes w) (h : Stage base bytes w σ s)
    (ho : 5 ≤ o ∧ o < 28) (ha : 5 ≤ a ∧ a < 28) (hb : 5 ≤ b ∧ b < 28)
    (mutable : o = 5 ∨ o = 6 ∨ o = 8 ∨ (11 ≤ o ∧ o < 27))
    (bLt : numAt s.mem base w b < val32 σ.mem base 256 (2 * w)) :
    WP isa (VG.Impl.MillerRabin.X86.product o a b) s fun t =>
      numAt t.mem base w o = VG.Proof.MillerRabin.Math.mm (val32 σ.mem base 256 (2 * w)) w
        (numAt s.mem base w a) (numAt s.mem base w b) ∧
      Stage base bytes w σ t ∧ Keeps [.eax, .ecx, .edx] s t ∧
      Frame [⟨off base (arrAt w o), 8 * w⟩, ⟨off base (scratch w), Spec.Rsa.MontMul.scratchBytes w⟩,
        below (s.gpr .esp) 40] s.mem t.mem := by
  obtain ⟨len, size, length⟩ := facts.length
  simp only [candidate_words] at bLt ⊢
  exact h.product_value (o := o) (a := a) (b := b) size facts.lower facts.upper facts.fit ho ha hb mutable facts.width length facts.inverse facts.odd bLt

end RoundFacts
end VG.Proof.MillerRabin.X86
