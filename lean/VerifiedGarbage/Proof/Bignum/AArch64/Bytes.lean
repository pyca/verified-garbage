import VerifiedGarbage.Proof.Bignum.AArch64.Double

/-!
# Multiword arithmetic on AArch64: big-endian bytes into words

`loadBE` reads `k` bytes most significant first into the `w = ⌈k / 8⌉`
words of an array (`loadBE_ok`): after `i` bytes, `x2 = p = k - i`, the
partial word in `x3` holds the bytes since the last word boundary
(`pre bs i mod 256^r`), and the words `p / 8` and above are complete
(`LInv`). A word is stored at `x8 + p` when `p % 8 = 0`.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_zero eq_zero_iff)

theorem and7_toNat (x : BitVec 64) : (x &&& 7#64).toNat = x.toNat % 8 := by
  rw [BitVec.toNat_and, show (7#64 : BitVec 64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem ofNat_sub_one' {p : Nat} (hp : 1 ≤ p) (hp' : p < 2 ^ 64) :
    BitVec.ofNat 64 p - BitVec.ofNat 64 1 = BitVec.ofNat 64 (p - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- After `i` bytes of `loadBE` from `s₀`. -/
structure LInv (s₀ : State) (B : Addr) (Z ed k w : Nat) (src : Addr) (bs : List Byte) (i : Nat)
    (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x1, .x2, .x3, .x4, .x5, .x6] s₀ t
  x1 : t.gpr .x1 = src + BitVec.ofNat 64 i
  x6 : t.gpr .x6 = 7#64
  x3 : (t.gpr .x3).toNat = pre bs i % 256 ^ ((8 - (k - i) % 8) % 8)
  words : ∀ q < w, k - i ≤ 8 * q → word t.mem B (ed + 8 * q) = BitVec.ofNat 64 (pre bs i / 256 ^ (8 * q - (k - i)))
  out : Outside B ed (8 * w) s₀.mem t.mem

theorem loadStep_ok {s₀ : State} {B : Addr} {Z ed k w : Nat} {src : Addr} {bs : List Byte}
    (hk : bs.length = k) (hk' : k < 2 ^ 31) (hw : w = (k + 7) / 8) (hed : ed + 8 * w ≤ Z)
    (h8 : s₀.gpr .x8 = off B ed)
    (hsrc : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (src + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < k), s₀.mem (src + BitVec.ofNat 64 i) = bs[i]'(by omega))
    (hsep : ∀ i < k, ofs B (src + BitVec.ofNat 64 i) < ed ∨ ed + 8 * w ≤ ofs B (src + BitVec.ofNat 64 i))
    {i : Nat} (hi : i < k) {t : State} (hI : LInv s₀ B Z ed k w src bs i t)
    (h2 : t.gpr .x2 = BitVec.ofNat 64 (k - i)) :
    WP isa (.seq (.block [.subImm .x .x2 .x2 1, .lsl .x .x3 .x3 8, .ldrb .x4 .x1 0, .add .x .x3 .x3 .x4,
        .addImm .x .x1 .x1 1, .logic .and .x .x5 .x2 .x6])
      (.ite (.zero .x .x5) (.block [.add .x .x5 .x8 .x2, st .x3 .x5, movi .x3 0]) (.block []))) t fun t' =>
      LInv s₀ B Z ed k w src bs (i + 1) t' ∧ t'.gpr .x2 = t.gpr .x2 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t8 : t.gpr .x8 = off B ed := (hI.keep.gpr .x8 (by decide)).trans h8
  have hr7 : (8 - (k - i) % 8) % 8 ≤ 7 := by omega
  have hax : (t.gpr .x3).toNat < 2 ^ 56 := by
    rw [hI.x3]
    have : 256 ^ ((8 - (k - i) % 8) % 8) ≤ 256 ^ 7 := Nat.pow_le_pow_right (by decide) hr7
    have := Nat.mod_lt (pre bs i) (show 0 < 256 ^ ((8 - (k - i) % 8) % 8) by exact Nat.pow_pos (by decide))
    have : (256 : Nat) ^ 7 = 2 ^ 56 := by decide
    omega
  have hb : t.mem (src + BitVec.ofNat 64 i) = bs[i]'(by omega) := by
    rw [hI.out _ (hsep i hi)]; exact hbytes i hi
  have hld : InRegions (t.rd ++ t.wr) (src + BitVec.ofNat 64 i) 1 := by
    rw [hI.keep.rd, hI.keep.wr]; exact hsrc i hi
  refine WP.seq (WP.mono (WP.keep [.x1, .x2, .x3, .x4, .x5] (Q := fun t₁ =>
      t₁.gpr .x2 = BitVec.ofNat 64 (k - i - 1) ∧
      t₁.gpr .x3 = (t.gpr .x3 <<< 8) + ((t.mem.read (src + BitVec.ofNat 64 i) 1).setWidth 32).setWidth 64 ∧
      t₁.gpr .x1 = src + BitVec.ofNat 64 i + BitVec.ofNat 64 1 ∧
      t₁.gpr .x5 = BitVec.ofNat 64 (k - i - 1) &&& 7#64 ∧ t₁.mem = t.mem)
    (by brun [h2, hI.x1, hI.x6, hld, ofNat_sub_one' (show 1 ≤ k - i by omega) (show k - i < 2 ^ 64 by omega)])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hdx₁, hax₁, h1₁, h5₁, hm₁⟩, k₁⟩ => ?_)
  have hpre := pre_succ bs (i := i) (by omega)
  have hbyte : (((t.mem.read (src + BitVec.ofNat 64 i) 1).setWidth 32).setWidth 64 : BitVec 64).toNat =
      (bs[i]'(by omega)).toNat := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, VG.Proof.MlKem.AArch64.read_one, hb]
    have := (bs[i]'(by omega)).isLt
    omega
  have e1 : (t.gpr .x3 <<< 8).toNat = (t.gpr .x3).toNat * 256 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  -- The new partial word.
  have hax₁' : (t₁.gpr .x3).toNat = pre bs (i + 1) % 256 ^ ((8 - (k - i) % 8) % 8 + 1) := by
    have hb' := (bs[i]'(by omega)).isLt
    rw [hax₁, BitVec.toNat_add, e1, hbyte,
      Nat.mod_eq_of_lt (show (t.gpr .x3).toNat * 256 + (bs[i]'(by omega)).toNat < 2 ^ 64 by omega), hI.x3, hpre,
      VG.Proof.Bignum.bytes_mod_step _ _ _ hb']
    grind
  have hs₁ := hI.scr.congr k₁.wr
  have t₁8 : t₁.gpr .x8 = off B ed := (k₁.gpr .x8 (by decide)).trans t8
  have hx1 : t₁.gpr .x1 = src + BitVec.ofNat 64 (i + 1) := by
    rw [h1₁, BitVec.add_assoc, ← BitVec.ofNat_add]
  -- The old words, one byte on.
  have hwords : ∀ q < w, k - i ≤ 8 * q → word t.mem B (ed + 8 * q) =
      BitVec.ofNat 64 (pre bs (i + 1) / 256 ^ (8 * q - (k - (i + 1)))) := by
    intro q hq hle
    rw [hI.words q hq hle, hpre, show 8 * q - (k - (i + 1)) = 8 * q - (k - i) + 1 by omega,
      VG.Proof.Bignum.bytes_div_step _ _ _ (bs[i]'(by omega)).isLt]
  have hz5 : (t₁.gpr .x5 == 0) = decide ((k - i - 1) % 8 = 0) := by
    rw [eq_zero_iff, h5₁, and7_toNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show k - i - 1 < 2 ^ 64 by omega)]
  by_cases hz : (k - i - 1) % 8 = 0
  · -- A word is complete: it is stored.
    refine WP.ite true (by rw [eval_zero, hz5, decide_eq_true hz]) (fun _ => ?_) (by simp)
    refine WP.mono (WP.keep [.x3, .x5] (Q := fun t' =>
        t'.mem = t₁.mem.writeW (off B (ed + (k - i - 1))) (t₁.gpr .x3) ∧ t'.gpr .x3 = 0)
      (by brun [t₁8, hdx₁, off_add, hs₁.st (show ed + (k - i - 1) + 8 ≤ Z by omega)])
      (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨hm', hax'⟩, k'⟩ => ⟨?_, ?_⟩
    · refine ⟨hs₁.congr k'.wr, ((hI.keep.trans k₁).trans k').mono (by decide),
        by rw [k'.gpr .x1 (by decide), hx1], by rw [k'.gpr .x6 (by decide), k₁.gpr .x6 (by decide), hI.x6],
        ?_, ?_, ?_⟩
      · rw [hax', show (8 - (k - (i + 1)) % 8) % 8 = 0 by omega, Nat.pow_zero, Nat.mod_one]; rfl
      · intro q hq hle
        rw [hm', hm₁]
        by_cases hq' : 8 * q = k - i - 1
        · have : q = (k - i - 1) / 8 := by omega
          subst this
          rw [show ed + (k - i - 1) = ed + 8 * ((k - i - 1) / 8) by omega, word_writeW_self,
            show 8 * ((k - i - 1) / 8) - (k - (i + 1)) = 0 by omega, Nat.pow_zero, Nat.div_one]
          apply BitVec.eq_of_toNat_eq
          rw [hax₁', BitVec.toNat_ofNat, show (8 - (k - i) % 8) % 8 + 1 = 8 by omega,
            VG.Proof.Bignum.pow256_8]
        · rw [(writeW_outside t.mem B _ (by omega)).word (by omega) (by omega)]
          exact hwords q hq (by omega)
      · rw [hm', hm₁]
        intro x hx
        rw [writeW_outside t.mem B _ (by omega) x (by omega)]
        exact hI.out x hx
    · rw [k'.gpr .x2 (by decide), hdx₁, h2, ofNat_sub_one' (by omega) (by omega)]
  · -- No word is complete.
    refine WP.ite false (by rw [eval_zero, hz5, decide_eq_false hz]) (by simp) (fun _ => WP.block_nil ⟨?_, ?_⟩)
    · refine ⟨hs₁, (hI.keep.trans k₁).mono (by decide), hx1, by rw [k₁.gpr .x6 (by decide), hI.x6], ?_, ?_, ?_⟩
      · rw [hax₁', show (8 - (k - i) % 8) % 8 + 1 = (8 - (k - (i + 1)) % 8) % 8 by omega]
      · intro q hq hle
        rw [hm₁]
        exact hwords q hq (by omega)
      · rw [hm₁]; exact hI.out
    · rw [hdx₁, h2, ofNat_sub_one' (by omega) (by omega)]

/-- `loadBE`: the `k` bytes at `x1`, most significant first, as the
`w = ⌈k / 8⌉` words of the array at `x8`. -/
theorem loadBE_ok {s : State} {B : Addr} {Z ed k w : Nat} {src : Addr} {bs : List Byte}
    (hs : Scr s B Z) (h1 : s.gpr .x1 = src) (h2 : s.gpr .x2 = BitVec.ofNat 64 k)
    (h8 : s.gpr .x8 = off B ed) (hk : bs.length = k) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hw : w = (k + 7) / 8) (hed : ed + 8 * w ≤ Z)
    (hsrc : ∀ i < k, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < k), s.mem (src + BitVec.ofNat 64 i) = bs[i]'(by omega))
    (hsep : ∀ i < k, ofs B (src + BitVec.ofNat 64 i) < ed ∨ ed + 8 * w ≤ ofs B (src + BitVec.ofNat 64 i)) :
    WP isa loadBE s fun t =>
      wv t.mem B ed w = Spec.Rsa.os2ip bs ∧ Outside B ed (8 * w) s.mem t.mem ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6] s t := by
  unfold loadBE
  refine WP.seq (WP.mono (WP.keep [.x3, .x6] (Q := fun t => t.gpr .x3 = 0 ∧ t.gpr .x6 = 7#64 ∧ t.mem = s.mem)
    (by brun) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨hax, h6, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  refine WP.mono (wp_countdown (N := k) (by omega) (by omega) (LInv s B Z ed k w src bs)
    (fun i hi t hI h2' => loadStep_ok hk hk' hw hed h8 hsrc hbytes hsep hi hI (by rw [h2']))
    ⟨hs₁, k₁.mono (by decide), by rw [k₁.gpr .x1 (by decide), h1]; exact (BitVec.add_zero src).symm, h6,
      by rw [hax, pre_zero]; rfl, fun q hq hle => absurd hle (by omega), by rw [hm₁]; exact Outside.refl _ _ _ _⟩
    (by rw [k₁.gpr .x2 (by decide), h2])) fun t hI => ⟨?_, hI.out, hI.keep⟩
  rw [wv_digits w fun q hq => by rw [hI.words q hq (by omega), Nat.sub_self, Nat.sub_zero],
    ← hk, pre_len, Nat.mod_eq_of_lt]
  have := pre_lt bs (Nat.le_refl _)
  rw [pre_len, hk] at this
  have : (256 : Nat) ^ k ≤ 2 ^ (64 * w) := by
    rw [← pow256]; exact Nat.pow_le_pow_right (by decide) (by omega)
  omega

end VG.Proof.Bignum.AArch64
