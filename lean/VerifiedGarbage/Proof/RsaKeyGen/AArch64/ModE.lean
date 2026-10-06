import VerifiedGarbage.Proof.RsaKeyGen.AArch64.GcdStep

/-!
# A candidate on AArch64: `(c − 1) mod e`

The 64 bits of a word, from the top, into `r = x3 < e = x13`: `modBits_ok`,
`r := (r 2^64 + x) mod e` (by `modBit_ok` and `shift_step`); the words of a
number from the top, `x10` walking down and `x14` counting
(`modWords_ok`): the number mod `e`.
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The 64 bits of the word `x` in `x2` into `r = x3 < e` (`x13`):
`(r 2^64 + x) mod e`. -/
theorem modBits_ok {s : State} (h7 : s.gpr .x7 = 0) (h8 : s.gpr .x8 = mask true)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 64) (hre : (s.gpr .x3).toNat < (s.gpr .x13).toNat) :
    WP isa (countLoop .x9 modBit) s fun t =>
      (t.gpr .x3).toNat = ((s.gpr .x3).toNat * 2 ^ 64 + (s.gpr .x2).toNat) % (s.gpr .x13).toNat ∧
      t.mem = s.mem ∧ Keep [.x2, .x3, .x4, .x5, .x6, .x9] s t := by
  have he0 : 0 < (s.gpr .x13).toNat := by omega
  have hX := (s.gpr .x2).isLt
  refine WP.mono (wp_countdown (cnt := .x9) (N := 64) (by decide) (by decide)
    (fun i t => (t.gpr .x3).toNat = ((s.gpr .x3).toNat * 2 ^ i + (s.gpr .x2).toNat / 2 ^ (64 - i)) %
        (s.gpr .x13).toNat ∧
      (t.gpr .x2).toNat = ((s.gpr .x2).toNat % 2 ^ (64 - i)) * 2 ^ i ∧ t.mem = s.mem ∧
      Keep [.x2, .x3, .x4, .x5, .x6, .x9] s t) ?_ ⟨?_, ?_, rfl, Keep.refl _ _⟩ h9) fun t ⟨hr, _, hm, k⟩ => ?_
  · intro i hi t ⟨hr, hd, hm, k⟩ _
    have h13 : t.gpr .x13 = s.gpr .x13 := k.gpr .x13 (by decide)
    refine WP.block_append_iff.mpr (WP.mono (modBit_ok t ((k.gpr .x7 (by decide)).trans h7)
      ((k.gpr .x8 (by decide)).trans h8) (by rw [h13, hr]; exact Nat.mod_lt _ he0))
      fun t₁ ⟨⟨h1, h2, m₁⟩, k₁⟩ => ?_)
    refine WP.mono (dec_ok t₁ .x9) fun t' ⟨⟨h9', m', _⟩, k'⟩ => ⟨⟨?_, ?_, by rw [m', m₁, hm], ?_⟩, ?_⟩
    · obtain ⟨_, hbit, _, hdiv⟩ := shift_step (s.gpr .x2).toNat (63 - i) i (by omega)
      rw [show 63 - i + 1 = 64 - i by omega] at hbit hdiv
      rw [k'.gpr .x3 (by decide), h1, h13, hd, hbit, hr, show 64 - (i + 1) = 63 - i by omega, ← hdiv, Nat.pow_succ]
      have hm2 : ∀ V b E : Nat, (2 * (V % E) + b) % E = (2 * V + b) % E := fun V b E => by
        rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
      rw [hm2]
      congr 1
      have hb2 : (s.gpr .x2).toNat / 2 ^ (63 - i) % 2 < 2 := Nat.mod_lt _ (by decide)
      generalize (s.gpr .x3).toNat = R
      generalize (s.gpr .x2).toNat / 2 ^ (64 - i) = Q
      generalize (s.gpr .x2).toNat / 2 ^ (63 - i) % 2 = b at hb2 ⊢
      rw [Nat.mul_add, Nat.mul_comm 2 (R * 2 ^ i), Nat.mul_assoc, Nat.mul_comm 2 Q]
      omega
    · obtain ⟨_, _, hsh, _⟩ := shift_step (s.gpr .x2).toNat (63 - i) i (by omega)
      rw [show 63 - i + 1 = 64 - i by omega] at hsh
      rw [k'.gpr .x2 (by decide), h2, BitVec.toNat_add, hd, hsh, show 64 - (i + 1) = 63 - i by omega]
    · exact ((k.trans k₁).trans k').mono (by decide)
    · rw [h9', k₁.gpr .x9 (by decide)]
  · rw [Nat.pow_zero, Nat.mul_one, Nat.div_eq_of_lt hX, Nat.add_zero, Nat.mod_eq_of_lt hre]
  · rw [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hX]
  · refine ⟨?_, hm, k⟩
    rw [hr, Nat.sub_self, Nat.pow_zero, Nat.div_one]

/-- The words `m` to `w − 1` of the number at `d`. -/
abbrev hiw (mem : Mem) (B : Addr) (d w m : Nat) : Nat := wv mem B (d + 8 * m) (w - m)

theorem hiw_step (mem : Mem) (B : Addr) (d w m : Nat) (hm : m < w) :
    hiw mem B d w m = (word mem B (d + 8 * m)).toNat + 2 ^ 64 * hiw mem B d w (m + 1) := by
  unfold hiw
  rw [show w - m = 1 + (w - (m + 1)) by omega, wv_add, show d + 8 * m + 8 * 1 = d + 8 * (m + 1) by omega]
  simp [wv]

/-- One word: `x10` down a word, the word into `x2`, `x9 := 64`. -/
theorem modWordHead_ok {s : State} {B : Addr} {Z d k : Nat} (hs : Scr s B Z) (h10 : s.gpr .x10 = off B (d + 8 * (k + 1)))
    (hd : d + 8 * (k + 1) ≤ Z) :
    WP isa (.block [.subImm .x .x10 .x10 8, ld .x2 .x10, movi .x9 64]) s fun t =>
      (t.gpr .x10 = off B (d + 8 * k) ∧ t.gpr .x2 = word s.mem B (d + 8 * k) ∧ t.gpr .x9 = BitVec.ofNat 64 64 ∧
        t.mem = s.mem) ∧ Keep [.x10, .x2, .x9] s t := by
  have hn := hs.nowrap
  have ha : off B (d + 8 * (k + 1)) - BitVec.ofNat 64 8 = off B (d + 8 * k) := by
    rw [show d + 8 * (k + 1) = d + 8 * k + 8 by omega, ← off_add, BitVec.add_sub_cancel]
  refine WP.keep [.x10, .x2, .x9] ?_ (by decide) (by decide) (by decide +kernel)
  brun [h10, ha, hs.ld (d := d + 8 * k) (by omega)]

/-- After `j` words of the loop from the top. -/
structure ModInv (s₀ : State) (B : Addr) (d w : Nat) (j : Nat) (t : State) : Prop where
  val : (t.gpr .x3).toNat = hiw s₀.mem B d w (w - j) % (s₀.gpr .x13).toNat
  x10 : t.gpr .x10 = off B (d + 8 * (w - j))
  mem : t.mem = s₀.mem
  keep : Keep [.x2, .x3, .x4, .x5, .x6, .x9, .x10, .x14] s₀ t

/-- The words of the number at `d`, from the top, into `r = x3 = 0` modulo
the `e > 1` in `x13`. -/
theorem modWords_ok {s : State} {B : Addr} {Z d w : Nat} (hs : Scr s B Z) (h10 : s.gpr .x10 = off B (d + 8 * w))
    (h14 : s.gpr .x14 = BitVec.ofNat 64 w) (h7 : s.gpr .x7 = 0) (h8 : s.gpr .x8 = mask true) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hd : d + 8 * w ≤ Z) (h3 : s.gpr .x3 = 0) (he : 1 < (s.gpr .x13).toNat) :
    WP isa (.loop (seqs [.block [.subImm .x .x10 .x10 8, ld .x2 .x10, movi .x9 64], countLoop .x9 modBit,
      .block [.subImm .x .x14 .x14 1]]) (.nonzero .x .x14)) s fun t =>
      (t.gpr .x3).toNat = wv s.mem B d w % (s.gpr .x13).toNat ∧ t.mem = s.mem ∧
      Keep [.x2, .x3, .x4, .x5, .x6, .x9, .x10, .x14] s t := by
  refine WP.mono (wp_countdown (cnt := .x14) (N := w) (by omega) (by omega) (ModInv s B d w) ?_
    ⟨by rw [h3, Nat.sub_zero]; unfold hiw; rw [Nat.sub_self]; simp [wv], by rw [h10, Nat.sub_zero], rfl,
      Keep.refl _ _⟩ h14) fun t hI => ⟨?_, hI.mem, hI.keep⟩
  · intro j hj t hI _
    have t13 : t.gpr .x13 = s.gpr .x13 := hI.keep.gpr .x13 (by decide)
    simp only [seqs]
    refine WP.seq (WP.mono (modWordHead_ok (B := B) (Z := Z) (d := d) (k := w - (j + 1)) (hs.congr hI.keep.wr)
      (by rw [hI.x10, show w - (j + 1) + 1 = w - j by omega]) (by omega)) fun t₁ ⟨⟨h10₁, h2₁, h9₁, m₁⟩, k₁⟩ => ?_)
    have k01 := hI.keep.trans k₁
    have r13 : t₁.gpr .x13 = s.gpr .x13 := k01.gpr .x13 (by decide)
    have r3 : t₁.gpr .x3 = t.gpr .x3 := k₁.gpr .x3 (by decide)
    refine WP.seq (WP.mono (modBits_ok ((k01.gpr .x7 (by decide)).trans h7) ((k01.gpr .x8 (by decide)).trans h8) h9₁
      (by rw [r13, r3, hI.val]; exact Nat.mod_lt _ (by omega))) fun t₂ ⟨h3₂, m₂, k₂⟩ => ?_)
    refine WP.mono (dec_ok t₂ .x14) fun t' ⟨⟨h14', m', _⟩, k'⟩ => ⟨⟨?_, ?_, by rw [m', m₂, m₁, hI.mem], ?_⟩, ?_⟩
    · rw [k'.gpr .x3 (by decide), h3₂, r13, r3, h2₁, hI.val, hI.mem, hiw_step s.mem B d w (w - (j + 1)) (by omega),
        show w - (j + 1) + 1 = w - j by omega]
      have hm2 : ∀ V x E : Nat, ((V % E) * 2 ^ 64 + x) % E = (x + 2 ^ 64 * V) % E := fun V x E => by
        rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod, Nat.add_comm, Nat.mul_comm]
      exact hm2 _ _ _
    · rw [k'.gpr .x10 (by decide), k₂.gpr .x10 (by decide), h10₁]
    · exact ((k01.trans k₂).trans k').mono (by decide)
    · rw [h14', k₂.gpr .x14 (by decide), k₁.gpr .x14 (by decide)]
  · rw [hI.val, Nat.sub_self]; unfold hiw; simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero]

end VG.Proof.RsaKeyGen.AArch64
