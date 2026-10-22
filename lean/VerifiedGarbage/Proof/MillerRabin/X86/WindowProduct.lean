module

public import VerifiedGarbage.Proof.MillerRabin.X86.Scan
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFacts
public import VerifiedGarbage.Proof.MillerRabin.X86.WindowHeaders

/-! # Select the digit's table power and multiply the accumulator by it -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

theorem window_product {σ s : State} {base : Addr} {bytes w d k : Nat} {v : BitVec 32} {F : Bool}
    {T : Nat → Nat} (facts : RoundFacts σ base bytes w) (h : Stage base bytes w σ s)
    (headers : WindowHeaders s.mem base v k F) (hd : d < 16)
    (digit : v >>> 28 = BitVec.ofNat 32 d)
    (table : ∀ i, i < 16 → numAt s.mem base w (11 + i) = T i)
    (tableLt : ∀ i, i < 16 → T i < val32 σ.mem base 256 (2 * w)) :
    WP isa (.seq scan (product aY aY aX)) s fun t => Stage base bytes w σ t ∧
      WindowHeaders t.mem base v k F ∧
      numAt t.mem base w 6 = VG.Proof.MillerRabin.Math.mm (val32 σ.mem base 256 (2 * w)) w
        (numAt s.mem base w 6) (T d) ∧
      (∀ a, 5 ≤ a → a < 28 → a ≠ 5 → a ≠ 6 → numAt t.mem base w a = numAt s.mem base w a) := by
  refine WP.seq (WP.mono (scan_ok h facts.lower facts.upper facts.fit hd facts.width table
    (by rw [headers.word, digit])) ?_)
  rintro u ⟨selected, hu, scanFrame⟩
  have headersU := headers.of_array h.context facts.fit (by decide : 5 < 28) scanFrame
  have yU := array_frame_num h.context.ws.nowrap facts.fit (show 6 < 28 by decide)
    (show 5 < 28 by decide) (by decide) scanFrame
  refine WP.mono (facts.multiply (o := 6) (a := 6) (b := 5) hu (by decide) (by decide)
    (by decide) (.inr (.inl rfl)) (by rw [selected]; exact tableLt d hd)) ?_
  rintro t ⟨value, ht, _, productFrame⟩
  rw [yU, selected] at value
  refine ⟨ht, headersU.of_product hu.context hu.room facts.fit (by decide) productFrame, value, ?_⟩
  intro a lo hi ne5 ne6
  exact (product_frame_num hu.context hu.room facts.fit (by decide) ⟨lo, hi⟩ ne6 productFrame).trans
    (array_frame_num h.context.ws.nowrap facts.fit hi (by decide) ne5 scanFrame)

end VG.Proof.MillerRabin.X86
