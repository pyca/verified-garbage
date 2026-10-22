module

public import VerifiedGarbage.Proof.MillerRabin.X86.FourSquares
public import VerifiedGarbage.Proof.MillerRabin.X86.WindowProduct
public import VerifiedGarbage.Proof.MillerRabin.X86.WindowEqualEnd

/-! # An exponent window implements the existing Montgomery window function -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

theorem window_ok {σ s : State} {base : Addr} {bytes w d k : Nat} {v : BitVec 32} {F : Bool}
    {T : Nat → Nat} (facts : RoundFacts σ base bytes w) (h : Stage base bytes w σ s)
    (headers : WindowHeaders s.mem base v k F) (hd : d < 16) (hk : 0 < k ∧ k < 2 ^ 32)
    (digit : v >>> 28 = BitVec.ofNat 32 d)
    (table : ∀ i, i < 16 → numAt s.mem base w (11 + i) = T i)
    (tableLt : ∀ i, i < 16 → T i < val32 σ.mem base 256 (2 * w))
    (reduced : numAt s.mem base w 6 < val32 σ.mem base 256 (2 * w)) :
    WP isa win s fun t => Stage base bytes w σ t ∧
      numAt t.mem base w 6 = (VG.Proof.MillerRabin.Math.mwin (val32 σ.mem base 256 (2 * w)) w
        (numAt s.mem base w 8) T d (numAt s.mem base w 6, F)).1 ∧
      w32 t.mem base sF = (VG.Proof.MillerRabin.Math.mwin (val32 σ.mem base 256 (2 * w)) w
        (numAt s.mem base w 8) T d (numAt s.mem base w 6, F)).2.toNat ∧
      w32 t.mem base sV = (v <<< 4).toNat ∧ w32 t.mem base sK = k - 1 ∧
      t.zf = some (decide ((k - 1) % 8 = 0)) ∧
      (∀ a, 5 ≤ a → a < 28 → a ≠ 5 → a ≠ 6 → numAt t.mem base w a = numAt s.mem base w a) := by
  have boolSmall (b : Bool) : b.toNat < 2 ^ 32 := by cases b <;> decide
  have flag : w32 s.mem base sF = F.toNat := by
    have e := congrArg BitVec.toNat headers.flag
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (boolSmall F)] using e
  unfold win
  refine WP.seq (WP.mono (four_squares facts h flag reduced) ?_)
  rintro u ⟨hu, yU, flagU, reducedU, sameU, sameHeaderU⟩
  have headersU : WindowHeaders u.mem base v k (squareRun σ s base w 4 0 F 4).2 :=
    ⟨(sameHeaderU sV (.inl rfl)).trans headers.word, (sameHeaderU sK (.inr rfl)).trans headers.count,
      readW_of_w32 (boolSmall _) flagU⟩
  have tableU : ∀ i, i < 16 → numAt u.mem base w (11 + i) = T i := by
    intro i hi
    exact (sameU (11 + i) (by omega) (by omega) (by omega)).trans (table i hi)
  refine WP.seq (WP.mono (window_product facts hu headersU hd digit tableU tableLt) ?_)
  rintro z ⟨hz, headersZ, yZ, sameZ⟩
  refine WP.mono (window_equal_end hz facts.lower facts.upper facts.fit facts.width headersZ hd hk digit) ?_
  rintro t ⟨ht, flagT, wordT, countT, zeroT, sameT⟩
  have oneZ : numAt z.mem base w 11 = T 0 :=
    (sameZ 11 (by decide) (by decide) (by decide) (by decide)).trans (tableU 0 (by decide))
  have minusZ : numAt z.mem base w 8 = numAt s.mem base w 8 :=
    (sameZ 8 (by decide) (by decide) (by decide) (by decide)).trans
      (sameU 8 (by decide) (by decide) (by decide))
  rw [yU] at yZ
  refine ⟨ht, ?_, ?_, wordT, countT, zeroT, ?_⟩
  · exact (sameT 6 (by decide)).trans yZ
  · rw [yZ, oneZ, minusZ] at flagT
    exact flagT
  · intro a lo hi ne5 ne6
    exact (sameT a hi).trans ((sameZ a lo hi ne5 ne6).trans (sameU a lo hi ne6))

end VG.Proof.MillerRabin.X86
