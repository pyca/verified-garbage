import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified

/-!
# `vg_rsa_public_precomputed` on AArch64: the load and the checks

The load of `m` and `R² mod m` from `pre`, and `x9` nonzero iff they pass
the checks that refuse values no modulus has (`pdLoad_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

theorem ne_sel (v : BitVec 64) :
    (if decide (2 ^ 64 ≤ v.toNat + (~~~(1 : BitVec 64)).toNat + true.toNat) = true then (1 : BitVec 64) else 0) =
      BitVec.ofNat 64 (decide (v ≠ 0)).toNat := by
  have e : (~~~(1 : BitVec 64)).toNat = 2 ^ 64 - 2 := by decide
  rw [e, show true.toNat = 1 from rfl]
  by_cases h : v = 0
  · subst h
    have h' : ¬ 2 ^ 64 ≤ (0 : BitVec 64).toNat + (2 ^ 64 - 2) + 1 := by decide
    simp only [h', decide_false, Bool.false_eq_true, ite_false, ne_eq, not_true_eq_false]; rfl
  · have h0 : v.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
    have h' : 2 ^ 64 ≤ v.toNat + (2 ^ 64 - 2) + 1 := by omega
    simp only [h', decide_true, ite_true, ne_eq, h, not_false_eq_true]; rfl

theorem and1_mod2 (a : BitVec 64) : a &&& 1 = BitVec.ofNat 64 (a.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat]
  omega

theorem and_bits (a b : Bool) : BitVec.ofNat 64 a.toNat &&& BitVec.ofNat 64 b.toNat = BitVec.ofNat 64 (a && b).toNat := by
  cases a <;> cases b <;> decide

theorem mod2_bit (n : Nat) : BitVec.ofNat 64 (n % 2) = BitVec.ofNat 64 (decide (n % 2 = 1)).toNat := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> rfl

/-- The checks' last block: `x9` is 1 iff the carry `c` of `R - m` was clear
(`R < m`), `m` (at array `aN`, `w` words) is odd and its top word is not
zero, else 0. -/
theorem pdCheck_ok {t : State} {B : Addr} {Z w : Nat} (hs : Scr t B Z) (h0 : t.gpr .x0 = B)
    (hb : word t.mem B (8 * sArr aN) = off B (slot w aN)) (h12 : t.gpr .x12 = BitVec.ofNat 64 w)
    (h7 : t.gpr .x7 = 0) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z) {c : Bool} (hc : t.c = c) :
    WP isa (.block [movi .x8 1, .csel .x .x9 .x7 .x8, ldh .x17 (sArr aN), ld .x3 .x17, .logic .and .x .x3 .x3 .x8,
      .logic .and .x .x9 .x9 .x3, .subImm .x .x4 .x12 1, .lsl .x .x4 .x4 3, .add .x .x4 .x17 .x4, ld .x3 .x4,
      .subs .x .x3 .x3 .x8, .csel .x .x3 .x8 .x7, .logic .and .x .x9 .x9 .x3]) t fun t' =>
      t'.gpr .x9 = BitVec.ofNat 64 ((!c) && decide ((word t.mem B (slot w aN)).toNat % 2 = 1) &&
        decide (word t.mem B (slot w aN + 8 * (w - 1)) ≠ 0)).toNat ∧ t'.mem = t.mem ∧
      Keep [.x3, .x4, .x8, .x9, .x17] t t' := by
  have hn := hs.nowrap
  have := slot_le (w := w) (show aN < 8 by decide)
  have hl : InRegions (t.rd ++ t.wr) (off B (8 * sArr aN)) 8 :=
    hs.ld (by have := hdr_lt_slot w 8 (show sArr aN < 32 by decide); omega)
  have hw8 : (BitVec.ofNat 64 w - BitVec.ofNat 64 1) <<< 3 = BitVec.ofNat 64 (8 * (w - 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  rw [show ([movi .x8 1, .csel .x .x9 .x7 .x8, ldh .x17 (sArr aN), ld .x3 .x17, .logic .and .x .x3 .x3 .x8,
      .logic .and .x .x9 .x9 .x3, .subImm .x .x4 .x12 1, .lsl .x .x4 .x4 3, .add .x .x4 .x17 .x4, ld .x3 .x4,
      .subs .x .x3 .x3 .x8, .csel .x .x3 .x8 .x7, .logic .and .x .x9 .x9 .x3] : List Instr) =
    ([movi .x8 1, .csel .x .x9 .x7 .x8, ldh .x17 (sArr aN), ld .x3 .x17, .logic .and .x .x3 .x3 .x8] : List Instr) ++
    ([.logic .and .x .x9 .x9 .x3] : List Instr) ++
    ([.subImm .x .x4 .x12 1, .lsl .x .x4 .x4 3, .add .x .x4 .x17 .x4, ld .x3 .x4,
      .subs .x .x3 .x3 .x8, .csel .x .x3 .x8 .x7] : List Instr) ++ ([.logic .and .x .x9 .x9 .x3] : List Instr) from rfl,
    WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x8, .x9, .x17] (Q := fun t₁ =>
      t₁.gpr .x9 = BitVec.ofNat 64 (!c).toNat ∧ t₁.gpr .x8 = 1 ∧ t₁.gpr .x17 = off B (slot w aN) ∧
      t₁.gpr .x3 = BitVec.ofNat 64 ((word t.mem B (slot w aN)).toNat % 2) ∧ t₁.mem = t.mem) (by
    brun [h7, hc, h0, hdr_enc (show sArr aN < 32 by decide), hl, hb, hs.ld (d := slot w aN) (by omega),
      show BitVec.setWidth 64 (1#16) = (1 : BitVec 64) from rfl, and1_mod2]
    cases c <;> rfl) (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨h9₁, h8₁, h17₁, h3₁, hm₁⟩, k₁⟩ => ?_
  refine WP.mono (WP.keep [.x9] (Q := fun t₂ => t₂.gpr .x9 = t₁.gpr .x9 &&& t₁.gpr .x3 ∧ t₂.mem = t₁.mem)
    (by brun) (by decide) (by decide) (by decide +kernel)) fun t₂ ⟨⟨h9₂, hm₂⟩, k₂⟩ => ?_
  have hm₂' : t₂.mem = t.mem := hm₂.trans hm₁
  have hs₂ := hs.congr (k₁.trans k₂).wr
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t₃ =>
      t₃.gpr .x3 = BitVec.ofNat 64 (decide (word t.mem B (slot w aN + 8 * (w - 1)) ≠ 0)).toNat ∧ t₃.mem = t₂.mem)
    (by
      brun [(k₂.gpr .x7 (by decide)).trans ((k₁.gpr .x7 (by decide)).trans h7), (k₂.gpr .x8 (by decide)).trans h8₁,
        (k₂.gpr .x12 (by decide)).trans ((k₁.gpr .x12 (by decide)).trans h12), (k₂.gpr .x17 (by decide)).trans h17₁,
        hw8, off_add, hm₂', hs₂.ld (d := slot w aN + 8 * (w - 1)) (by omega)]
      exact ne_sel _) (by decide) (by decide) (by decide +kernel)) fun t₃ ⟨⟨h3₃, hm₃⟩, k₃⟩ => ?_
  refine WP.mono (WP.keep [.x9] (Q := fun t₄ => t₄.gpr .x9 = t₃.gpr .x9 &&& t₃.gpr .x3 ∧ t₄.mem = t₃.mem)
    (by brun) (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨h9', hm'⟩, k₄⟩ => ?_
  refine ⟨?_, by rw [hm', hm₃, hm₂'], (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  rw [h9', h3₃, k₃.gpr .x9 (by decide), h9₂, h9₁, h3₁, mod2_bit, and_bits, and_bits]

/-- `load`'s first block: `head`, then `pre`'s pointer and `m`'s base. -/
theorem pdHead_ok {s : State} {B : Addr} {Z k : Nat} {pp : Addr} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk : k < 2 ^ 32)
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hN : word s.mem B (8 * sN) = pp) :
    WP isa (.block (head ++ ([ldh .x16 sN, ldh .x17 (sArr aN)] : List Instr))) s fun t =>
      t.gpr .x16 = off pp 0 ∧ t.gpr .x17 = off B (slot ((k + 7) / 8) aN) ∧
      t.gpr .x12 = BitVec.ofNat 64 ((k + 7) / 8) ∧
      word t.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) ∧
      (∀ j < 8, word t.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j)) ∧
      Frm B [(8 * sW, 8), (8 * sArr 0, 64)] s.mem t.mem ∧ Keep [.x3, .x4, .x12, .x16, .x17] s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have eN : sN = 17 := rfl
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eAN : sArr aN = 8 := rfl
  rw [WP.block_append_iff]
  refine WP.mono (head_ok hs h0 hZ hk hK) fun t₁ ⟨h12, hW₁, hb₁, hf₁, k₁⟩ => ?_
  have hs₁ := hs.congr k₁.wr
  have hw₁ : ∀ i, 8 * i + 8 ≤ 8 * sW ∨ (16 ≤ i ∧ i < 32) → word t₁.mem B (8 * i) = word s.mem B (8 * i) :=
    fun i hi => hf₁.word_eq (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl) <;> omega) (by omega)
  refine WP.mono (WP.keep [.x16, .x17] (Q := fun t => t.gpr .x16 = off pp 0 ∧
      t.gpr .x17 = off B (slot ((k + 7) / 8) aN) ∧ t.mem = t₁.mem) (by
    brun [(k₁.gpr .x0 (by decide)).trans h0, hdr_enc (show sN < 32 by decide),
      hdr_enc (show sArr aN < 32 by decide), hs₁.ld (d := 8 * sN) (by omega),
      hs₁.ld (d := 8 * sArr aN) (by omega), hw₁ sN (by omega), hN, hb₁ aN (by decide)])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h16, h17, hm⟩, k₂⟩ => ?_
  exact ⟨h16, h17, (k₂.gpr .x12 (by decide)).trans h12, by rw [hm]; exact hW₁, fun j hj => by rw [hm]; exact hb₁ j hj,
    by rw [hm]; exact hf₁, (k₁.trans k₂).mono (by decide)⟩

/-- The load: `w`, the bases, `m` and `R² mod m` from `pre` (at `pp`, the
`2 w` words outside the working space), and `x9` 1 iff they pass the checks,
else 0. -/
theorem pdLoad_ok {s : State} {B : Addr} {Z k : Nat} {pp : Addr} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 9 ≤ k) (hk : k < 2 ^ 31)
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hN : word s.mem B (8 * sN) = pp)
    (hpr : ∀ i < 2 * ((k + 7) / 8), InRegions (s.rd ++ s.wr) (off pp (8 * i)) 8)
    (hps : ∀ j < 16 * ((k + 7) / 8), Z ≤ ofs B (pp + BitVec.ofNat 64 j)) :
    WP isa (seqs Precomputed.load) s fun t =>
      wv t.mem B (slot ((k + 7) / 8) aN) ((k + 7) / 8) = wv s.mem pp 0 ((k + 7) / 8) ∧
      wv t.mem B (slot ((k + 7) / 8) aR2) ((k + 7) / 8) = wv s.mem pp (8 * ((k + 7) / 8)) ((k + 7) / 8) ∧
      word t.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) ∧
      (∀ j < 8, word t.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j)) ∧
      t.gpr .x9 = BitVec.ofNat 64 (decide (wv t.mem B (slot ((k + 7) / 8) aR2) ((k + 7) / 8) <
          wv t.mem B (slot ((k + 7) / 8) aN) ((k + 7) / 8)) &&
        decide ((word t.mem B (slot ((k + 7) / 8) aN)).toNat % 2 = 1) &&
        decide (word t.mem B (slot ((k + 7) / 8) aN + 8 * ((k + 7) / 8 - 1)) ≠ 0)).toNat ∧
      Frm B (pdLoadRanges ((k + 7) / 8)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
  have h0' := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
  have hsN := slot_le (w := (k + 7) / 8) (show aN < 8 by decide)
  have hsR := slot_le (w := (k + 7) / 8) (show aR2 < 8 by decide)
  have hNR : slot ((k + 7) / 8) aN + 8 * ((k + 7) / 8 + 2) ≤ slot ((k + 7) / 8) aR2 := by
    unfold slot aN aR2; omega
  have h0N : slot ((k + 7) / 8) 0 ≤ slot ((k + 7) / 8) aN := by unfold slot; omega
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have hsl : ∀ r ∈ pdLoadRanges ((k + 7) / 8), r.1 + r.2 ≤ Z := fun r hr => Nat.le_trans (pdLoadRanges_le _ r hr) hZ
  -- A word of `pre` is outside the working space.
  have hpsep : ∀ e, e + 8 * ((k + 7) / 8) ≤ 16 * ((k + 7) / 8) → ∀ j < (k + 7) / 8, ∀ b < 8,
      Z ≤ ofs B (off pp (e + 8 * j) + BitVec.ofNat 64 b) := fun e he j hj b hb => by
    have := hps (e + 8 * j + b) (by omega)
    rwa [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  unfold Precomputed.load
  refine WP.seq (WP.mono (pdHead_ok hs h0 hZ (by omega) hK hN)
    fun t₁ ⟨h16, h17, h12, hW₁, hb₁, hf₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  have hf₁' : Frm B (pdLoadRanges ((k + 7) / 8)) s.mem t₁.mem := hf₁.mono (by simp [pdLoadRanges])
  have hi₁ := InScr.of_frm hf₁' hsl
  -- `m`.
  refine WP.seq (WP.mono (copyWords_ok (S := pp) (eS := 0) h16 h17 h12 (by omega) (by omega)
    (by omega) (fun j hj => by rw [k₁.rd, k₁.wr, Nat.zero_add]; exact hpr j (by omega))
    (fun j hj => by rw [k₁.wr]; exact hs.st (by omega))
    (fun j hj b hb => Or.inr (by have := hpsep 0 (by omega) j hj b hb; omega)))
    fun t₂ ⟨hv₂, _, ho₂, h16₂, _, k₂⟩ => ?_)
  have hm₂ : wv t₁.mem pp 0 ((k + 7) / 8) = wv s.mem pp 0 ((k + 7) / 8) :=
    wv_congr fun i hi => Mem.readW_congr fun b hb => hi₁ _ (hpsep 0 (by omega) i hi b (by omega))
  rw [hm₂] at hv₂
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.wr
  have h0₂ : t₂.gpr .x0 = B := (k12.gpr .x0 (by decide)).trans h0
  have hW₂ : word t₂.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) := by
    rw [ho₂.word (by omega) (by omega)]; exact hW₁
  have hb₂ : ∀ j < 8, word t₂.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j) := fun j hj => by
    rw [ho₂.word (d := 8 * sArr j) (by unfold sArr; omega) (by unfold sArr; omega)]; exact hb₁ j hj
  -- `R² mod m`'s base.
  refine WP.seq (WP.mono (WP.keep [.x17] (Q := fun t => t.gpr .x17 = off B (slot ((k + 7) / 8) aR2) ∧
      t.mem = t₂.mem) (by
    brun [h0₂, hdr_enc (show sArr aR2 < 32 by decide), hs₂.ld (d := 8 * sArr aR2) (by unfold sArr aR2; omega),
      hb₂ aR2 (by decide)]) (by decide) (by decide) (by decide +kernel))
    fun t₃ ⟨⟨h17₃, hm₃⟩, k₃⟩ => ?_)
  have k13 := k12.trans k₃
  -- `R² mod m`.
  refine WP.seq (WP.mono (copyWords_ok (S := pp) (eS := 8 * ((k + 7) / 8)) ((k₃.gpr .x16 (by decide)).trans
    (by rw [h16₂, Nat.zero_add])) h17₃ ((k₃.gpr .x12 (by decide)).trans ((k₂.gpr .x12 (by decide)).trans h12))
    (by omega) (by omega) (by omega)
    (fun j hj => by rw [k13.rd, k13.wr, show 8 * ((k + 7) / 8) + 8 * j = 8 * ((k + 7) / 8 + j) by omega]
                    exact hpr _ (by omega))
    (fun j hj => by rw [k13.wr]; exact hs.st (by omega))
    (fun j hj b hb => Or.inr (by have := hpsep (8 * ((k + 7) / 8)) (by omega) j hj b hb; omega)))
    fun t₄ ⟨hv₄, _, ho₄, _, _, k₄⟩ => ?_)
  have hm₄ : wv t₃.mem pp (8 * ((k + 7) / 8)) ((k + 7) / 8) = wv s.mem pp (8 * ((k + 7) / 8)) ((k + 7) / 8) := by
    rw [hm₃]
    exact wv_congr fun i hi => Mem.readW_congr fun b hb => (ho₂ _ (Or.inr (by
      have := hpsep (8 * ((k + 7) / 8)) (by omega) i hi b (by omega); omega))).trans (hi₁ _ (by
      have := hpsep (8 * ((k + 7) / 8)) (by omega) i hi b (by omega); omega))
  rw [hm₄] at hv₄
  have k14 := k13.trans k₄
  have hs₄ := hs.congr k14.wr
  have h0₄ : t₄.gpr .x0 = B := (k14.gpr .x0 (by decide)).trans h0
  have hN₄ : wv t₄.mem B (slot ((k + 7) / 8) aN) ((k + 7) / 8) = wv s.mem pp 0 ((k + 7) / 8) := by
    rw [ho₄.wv (by omega) (by omega), hm₃]; exact hv₂
  have hb₄ : ∀ j < 8, word t₄.mem B (8 * sArr j) = off B (slot ((k + 7) / 8) j) := fun j hj => by
    rw [ho₄.word (d := 8 * sArr j) (by unfold sArr; omega) (by unfold sArr; omega), hm₃]; exact hb₂ j hj
  have hW₄ : word t₄.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) := by
    rw [ho₄.word (by omega) (by omega), hm₃]; exact hW₂
  have h12₄ : t₄.gpr .x12 = BitVec.ofNat 64 ((k + 7) / 8) :=
    (k₄.gpr .x12 (by decide)).trans ((k₃.gpr .x12 (by decide)).trans ((k₂.gpr .x12 (by decide)).trans h12))
  -- The comparison's registers.
  refine WP.seq (WP.mono (WP.keep [.x3, .x7, .x14, .x16, .x17] (Q := fun t =>
      t.gpr .x16 = off B (slot ((k + 7) / 8) aR2) ∧ t.gpr .x17 = off B (slot ((k + 7) / 8) aN) ∧
      t.gpr .x7 = 0 ∧ t.gpr .x14 = BitVec.ofNat 64 ((k + 7) / 8) ∧ t.c = true ∧ t.mem = t₄.mem) (by
    brun [h0₄, hdr_enc (show sArr aR2 < 32 by decide), hdr_enc (show sArr aN < 32 by decide),
      hs₄.ld (d := 8 * sArr aR2) (by unfold sArr aR2; omega), hs₄.ld (d := 8 * sArr aN) (by unfold sArr aN; omega),
      hb₄ aR2 (by decide), hb₄ aN (by decide), h12₄]) (by decide) (by decide) (by decide +kernel))
    fun t₅ ⟨⟨h16₅, h17₅, h7₅, h14₅, hc₅, hm₅⟩, k₅⟩ => ?_)
  have hs₅ := hs₄.congr k₅.wr
  refine WP.seq (WP.mono (cmpLoop_ok hs₅ h16₅ h17₅ h14₅ hc₅ (by omega) (by omega) (by omega) (by omega))
    fun t₆ ⟨hc₆, hm₆, k₆⟩ => ?_)
  rw [hm₅] at hc₆
  have hs₆ := hs₅.congr k₆.wr
  have k16 := (k14.trans k₅).trans k₆
  rw [seqs_one]
  refine WP.mono (pdCheck_ok hs₆ ((k16.gpr .x0 (by decide)).trans h0) (by rw [hm₆, hm₅]; exact hb₄ aN (by decide))
    ((k₆.gpr .x12 (by decide)).trans ((k₅.gpr .x12 (by decide)).trans h12₄)) ((k₆.gpr .x7 (by decide)).trans h7₅)
    (by omega) (by omega) hZ hc₆) fun t ⟨h9, hm, k₇⟩ => ?_
  have hmm : t.mem = t₄.mem := by rw [hm, hm₆, hm₅]
  refine ⟨by rw [hmm]; exact hN₄, by rw [hmm]; exact hv₄, by rw [hmm]; exact hW₄,
    fun j hj => by rw [hmm]; exact hb₄ j hj, by rw [h9, Bool.not_not, hm₆, hm₅, hmm], ?_,
    (k16.trans k₇).mono (by decide)⟩
  rw [hmm]
  have f₂ : Frm B (pdLoadRanges ((k + 7) / 8)) t₁.mem t₂.mem :=
    Frm.of_outside (ho₂.mono (o' := slot ((k + 7) / 8) aN) (n' := 8 * ((k + 7) / 8 + 2)) (Nat.le_refl _) (by omega))
      (by simp [pdLoadRanges])
  have f₄ : Frm B (pdLoadRanges ((k + 7) / 8)) t₃.mem t₄.mem :=
    Frm.of_outside (ho₄.mono (o' := slot ((k + 7) / 8) aR2) (n' := 8 * ((k + 7) / 8 + 2)) (Nat.le_refl _) (by omega))
      (by simp [pdLoadRanges])
  rw [hm₃] at f₄
  exact (hf₁'.trans f₂).trans f₄

end VG.Proof.Bignum.AArch64
