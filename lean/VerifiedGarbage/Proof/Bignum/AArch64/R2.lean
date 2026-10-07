import VerifiedGarbage.Proof.Bignum.AArch64.Setup

/-!
# Multiword arithmetic on AArch64: the pieces of `R² mod m`

* `setWord o`: `[o] := x9 · 2^(64 i)` for `i` in `x13` (`setWord_ok`).
* `topBit`: `2^j` and `64 - j` for the top bit `j` of `x3` (`topBit_ok`).
* `doubles`: `[o] := 2^c [o] mod m`, counting the doublings in a header
  slot (`doubles_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep count_loop eval_zero eval_nonzero eq_zero_iff ne_zero_iff)

theorem setWord_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (h12 : s.gpr .x12 = BitVec.ofNat 64 w)
    (hw' : w < 2 ^ 31) {o : Nat} (ho : o < 8) {i : Nat} (hi : i < w) (h13 : s.gpr .x13 = BitVec.ofNat 64 i) :
    WP isa (setWord o) s fun t =>
      wv t.mem B (slot w o) w = (s.gpr .x9).toNat * 2 ^ (64 * i) ∧
      Outside B (slot w o) (8 * (w + 2)) s.mem t.mem ∧ Keep [.x7, .x8, .x14, .x16] s t := by
  have hn := hs.nowrap
  have sl : slot w o + 8 * (w + 2) ≤ Z := Nat.le_trans (slot_le ho) hZ
  have sa : sArr o < 32 := by unfold sArr; omega
  unfold setWord
  refine WP.seq (WP.mono (WP.keep [.x7, .x8] (Q := fun t => t.gpr .x8 = off B (slot w o) ∧ t.gpr .x7 = 0 ∧
      t.mem = s.mem)
    (by brun [h0, hdr_enc sa, hs.ld (show 8 * sArr o + 8 ≤ Z by have := hdr_lt_slot w 8 sa; omega),
      hH.harr o ho]) rfl rfl rfl)
    fun s₁ ⟨⟨h8, h7, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (zeroAcc_ok (hs.congr k₁.wr) h8 ((k₁.gpr .x12 (by decide)).trans h12) h7 hw' sl)
    fun s₂ ⟨hz, ho₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  have s₂8 : s₂.gpr .x8 = off B (slot w o) := (k₂.gpr .x8 (by decide)).trans h8
  have s₂i : s₂.gpr .x13 = BitVec.ofNat 64 i := (k12.gpr .x13 (by decide)).trans h13
  have s₂9 : s₂.gpr .x9 = s.gpr .x9 := k12.gpr .x9 (by decide)
  have hi8 : (BitVec.ofNat 64 i <<< 3 : BitVec 64) = BitVec.ofNat 64 (8 * i) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  refine WP.mono (WP.keep [.x16] (Q := fun t => t.mem = s₂.mem.writeW (off B (slot w o + 8 * i)) (s.gpr .x9))
    (by brun [s₂8, s₂i, hi8, off_add, (hs.congr k12.wr).st (show slot w o + 8 * i + 8 ≤ Z by omega), s₂9])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ⟨?_, ?_, (k12.trans k).mono (by decide)⟩
  · -- `[o]` is zero but word `i`.
    have hz' := (wv_eq_zero_iff _ _ _ _).mp hz
    rw [wv_single t.mem B (slot w o) w hi fun q hq hne => by
      rw [hm, (writeW_outside s₂.mem B _ (by omega)).word (by omega) (by omega)]
      exact hz' q (by omega), hm, word_writeW_self]
  · rw [hm]
    intro x hx
    rw [writeW_outside _ B _ (by omega) x (by omega)]
    exact ho₂ x hx |>.trans (by rw [hm₁])

/-! ## The top bit -/

theorem shr1_ofNat (n : Nat) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 1 = BitVec.ofNat 64 (n / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow, Nat.pow_one]

theorem ofNat_sub1_eq_zero {n : Nat} (hn : n < 2 ^ 64) (hn0 : 0 < n) :
    (BitVec.ofNat 64 n - BitVec.ofNat 64 1 == 0) = decide (n = 1) := by
  rw [eq_zero_iff, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  exact decide_eq_decide.mpr (by omega)

theorem topBit_ok {s : State} {T : Nat} (hT : s.gpr .x3 = BitVec.ofNat 64 T) (hT0 : 0 < T)
    (hT1 : T < 2 ^ 64) :
    WP isa topBit s fun t =>
      (t.gpr .x9 = BitVec.ofNat 64 (2 ^ T.log2) ∧ t.gpr .x13 = BitVec.ofNat 64 (64 - T.log2) ∧
      t.mem = s.mem) ∧ Keep [.x3, .x6, .x9, .x13] s t := by
  have hL : T.log2 < 64 := (Nat.log2_lt (by omega)).mpr hT1
  have hle := Nat.log2_self_le (n := T) (by omega)
  have hlt := Nat.lt_log2_self (n := T)
  unfold topBit
  refine WP.seq (WP.mono (WP.keep [.x6, .x9, .x13] (Q := fun t => t.gpr .x9 = BitVec.ofNat 64 (2 ^ 0) ∧
      t.gpr .x13 = BitVec.ofNat 64 (64 - 0) ∧ (t.gpr .x6 == 0) = decide (T = 1) ∧ t.mem = s.mem ∧
      t.gpr .x3 = BitVec.ofNat 64 (T / 2 ^ 0) ∧ t.gpr .x6 = BitVec.ofNat 64 T - BitVec.ofNat 64 1)
    (by brun [hT]; exact ⟨ofNat_sub1_eq_zero hT1 hT0, by rw [Nat.pow_zero, Nat.div_one]⟩) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h9, h13, hz, hm, s₁3, _⟩, k₁⟩ => ?_)
  by_cases h1 : T = 1
  · subst h1
    refine WP.ite true (by rw [eval_zero, hz]; rfl) (fun _ => WP.block_nil ⟨⟨?_, ?_, hm⟩, k₁.mono (by decide)⟩)
      (by simp)
    · rw [h9]; rfl
    · rw [h13]; rfl
  refine WP.ite false (by rw [eval_zero, hz, decide_eq_false h1]) (by simp) (fun _ => ?_)
  -- The loop: after `j` halvings, `x3 = T / 2^j`, `x9 = 2^j`, `x13 = 64 - j`.
  refine WP.loop (M := isa) (fun n t => ∃ j, n = T.log2 - j ∧ j < T.log2 ∧
      t.gpr .x3 = BitVec.ofNat 64 (T / 2 ^ j) ∧ t.gpr .x9 = BitVec.ofNat 64 (2 ^ j) ∧
      t.gpr .x13 = BitVec.ofNat 64 (64 - j) ∧ t.mem = s.mem ∧ Keep [.x3, .x6, .x9, .x13] s t) ?_ _ s₁
    ⟨0, rfl, by
      have : 2 ^ 1 ≤ T := by omega
      exact (Nat.le_log2 (by omega)).mpr this, s₁3, h9, h13, hm, k₁.mono (by decide)⟩
  rintro n t ⟨j, rfl, hj, hax, hdx', hcx', hm', k⟩
  have hTj : T / 2 ^ j < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hT1
  have hpj : 2 ^ j < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
  have hTj1 : 0 < T / 2 ^ (j + 1) := by
    have := (Nat.le_log2 (by omega)).mp (show j + 1 ≤ T.log2 by omega)
    exact Nat.div_pos this (Nat.pow_pos (by decide))
  refine WP.mono (WP.keep [.x3, .x6, .x9, .x13] (Q := fun t' => t'.gpr .x3 = BitVec.ofNat 64 (T / 2 ^ (j + 1)) ∧
      t'.gpr .x9 = BitVec.ofNat 64 (2 ^ (j + 1)) ∧ t'.gpr .x13 = BitVec.ofNat 64 (64 - (j + 1)) ∧
      (t'.gpr .x6 == 0) = decide (T / 2 ^ (j + 1) = 1) ∧ t'.mem = t.mem) (by
    brun [hax, hdx', hcx', shr1_ofNat _ hTj, div_pow_succ, ← BitVec.ofNat_add]
    refine ⟨by rw [Nat.pow_succ, Nat.mul_two], ?_, ?_⟩
    · exact (ofNat_sub_one' (by omega) (by omega)).trans (congrArg _ (by omega))
    · exact ofNat_sub1_eq_zero (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hT1) hTj1)
    (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨hax', hdx'', hcx'', hz', hm''⟩, k'⟩ => ?_
  -- `T / 2^(j+1) = 1` iff `j + 1` is the top bit.
  have key : T / 2 ^ (j + 1) = 1 ↔ j + 1 = T.log2 := by
    constructor
    · intro h
      have h1 : 2 ^ (j + 1) ≤ T := by
        have := Nat.div_mul_le_self T (2 ^ (j + 1)); rw [h, Nat.one_mul] at this; exact this
      have h2 : T < 2 ^ (j + 2) := by
        have := Nat.lt_mul_div_succ T (show 0 < 2 ^ (j + 1) by exact Nat.pow_pos (by decide))
        rw [h] at this; rw [Nat.pow_succ]; omega
      have := (Nat.le_log2 (by omega)).mpr h1
      have := (Nat.log2_lt (by omega)).mpr h2
      omega
    · intro h
      rw [← h] at hle hlt
      exact Nat.div_eq_of_lt_le (by rw [Nat.one_mul]; exact hle) (by rw [Nat.pow_succ] at hlt; omega)
  have hnz : isa.eval (.nonzero .x .x6) t' = some (!decide (T / 2 ^ (j + 1) = 1)) := by
    rw [eval_nonzero, ← hz']; rfl
  by_cases he : j + 1 = T.log2
  · refine .inl ⟨by rw [hnz, decide_eq_true (key.mpr he)]; rfl, ⟨?_, ?_, hm''.trans hm'⟩,
      (k.trans k').mono (by decide)⟩
    · rw [hdx'', he]
    · rw [hcx'', he]
  · refine .inr ⟨by rw [hnz, decide_eq_false ((not_congr key).mpr he)]; rfl, T.log2 - (j + 1), by omega, j + 1,
      rfl, by omega, hax', hdx'', hcx'', hm''.trans hm', (k.trans k').mono (by decide)⟩

/-! ## Repeated doubling -/

/-- After `j` of `c` doublings of `O` modulo `N` from `s`, counted in slot
`sl`. -/
structure DblsInv (s : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (mo acc tmp o sl c O N j : Nat)
    (t : State) : Prop where
  scr : Scr t B Z
  x0 : t.gpr .x0 = B
  hdr : Hdr t.mem B w minv
  cnt : word t.mem B (8 * sl) = BitVec.ofNat 64 (c - j)
  ov : wv t.mem B (slot w o) w = 2 ^ j * O % N
  nv : wv t.mem B (slot w mo) w = N
  frm : Frm B [(slot w acc, 8 * (w + 2)), (slot w tmp, 8 * (w + 2)), (slot w o, 8 * (w + 2)), (8 * sl, 8)]
    s.mem t.mem
  keep : Keep mmRegs s t

/-- `doubles`' count of `double`s. -/
abbrev dblCount (sl : Nat) : List Instr := [ldh .x13 sl, .subImm .x .x13 .x13 1, sth .x13 sl]

/-- One doubling of `doubles`, and its count. -/
theorem dblIter_ok {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w)
    (hw' : w < 2 ^ 31) {mo acc tmp o sl : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    (d1 : acc ≠ mo) (d2 : acc ≠ tmp) (d3 : acc ≠ o) (d6 : tmp ≠ mo) (d7 : tmp ≠ o) (d8 : o ≠ mo)
    (hsl : 16 ≤ sl) (hsl' : sl < 32) {c O N j : Nat} (hc' : c < 2 ^ 31) (hN0 : 0 < N) (hj : j < c)
    (hI : DblsInv s B Z w minv mo acc tmp o sl c O N j t) :
    WP isa (.seq (double mo acc tmp o) (.block (dblCount sl))) t fun t' =>
      DblsInv s B Z w minv mo acc tmp o sl c O N (j + 1) t' ∧ ((t'.gpr .x13).toNat ≠ 0 ↔ j + 1 ≠ c) := by
  have hn := hI.scr.nowrap
  have sl8 : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have sp : ∀ {j k}, j ≠ k → slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j :=
    fun h => slot_sep h
  have hhs : ∀ j, 8 * sl + 8 ≤ slot w j := fun j => hdr_lt_slot w j hsl'
  refine WP.seq (WP.mono (double_ok hI.scr hI.x0 hI.hdr hZ hw hw' hmo hacc htmp ho d1 d2 d3 d6 d7 (by
      rw [hI.ov, hI.nv]; exact Nat.mod_lt _ hN0)) fun t₁ ⟨hv₁, ha₁, k₁'⟩ => ?_)
  have hst₁ := hI.scr.congr k₁'.wr
  have h0₁ : t₁.gpr .x0 = B := (k₁'.gpr .x0 (by decide)).trans hI.x0
  have hH₁ := ha₁.hdr hI.hdr
  have hcnt₁ : word t₁.mem B (8 * sl) = BitVec.ofNat 64 (c - j) := by
    rw [ha₁.word_eq (fun j' hj' => Or.inl (by simp at hj'; rcases hj' with rfl | rfl | rfl <;> exact hhs _))
      (by omega), hI.cnt]
  have hld : InRegions (t₁.rd ++ t₁.wr) (off B (8 * sl)) 8 := hst₁.ld (by have := hhs 8; omega)
  refine WP.mono (WP.keep [.x13] (Q := fun t' => t'.mem = t₁.mem.writeW (off B (8 * sl))
      (BitVec.ofNat 64 (c - (j + 1))) ∧ t'.gpr .x13 = BitVec.ofNat 64 (c - (j + 1))) (by
    brun [h0₁, hdr_enc hsl', hld, hst₁.st (show 8 * sl + 8 ≤ Z by have := hhs 8; omega), hcnt₁,
      ofNat_sub_one' (show 1 ≤ c - j by omega) (by omega)]
    exact ⟨by congr 2, by congr 1⟩) rfl rfl rfl) fun t' ⟨⟨hm', h13'⟩, k'⟩ =>
      ⟨?_, by rw [h13', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega⟩
  have o' : Outside B (8 * sl) 8 t₁.mem t'.mem := by rw [hm']; exact writeW_outside _ _ _ (by omega)
  refine ⟨hst₁.congr k'.wr, (k'.gpr .x0 (by decide)).trans h0₁, by rw [hm']; exact Hdr.store hH₁ hsl hsl' _,
    by rw [hm', word_writeW_self], ?_, ?_, ?_, ((hI.keep.trans k₁').trans k').mono (by decide)⟩
  · rw [o'.wv (by have := hhs o; omega) (by have := sl8 o ho; omega), hv₁, hI.ov, hI.nv, Nat.mul_mod,
      Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc, ← Nat.pow_succ']
  · rw [o'.wv (by have := hhs mo; omega) (by have := sl8 mo hmo; omega),
      ha₁.wv_eq (fun j' hj' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
        rcases hj' with rfl | rfl | rfl
        · have := sp d1; omega
        · have := sp d6; omega
        · have := sp d8; omega) (by have := sl8 mo hmo; omega), hI.nv]
  · exact (hI.frm.trans (Frm.of_arrays ha₁ (by simp))).trans (Frm.of_outside o' (by simp))

/-- `doubles`' start: the count `c` into slot `sl`. -/
theorem dblStart_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {mo acc tmp o sl : Nat}
    (hmo : mo < 8) (ho : o < 8) (hsl : 16 ≤ sl) (hsl' : sl < 32) {c : Nat}
    (h13 : s.gpr .x13 = BitVec.ofNat 64 c) (hO : wv s.mem B (slot w o) w < wv s.mem B (slot w mo) w) :
    WP isa (.block [sth .x13 sl]) s (DblsInv s B Z w minv mo acc tmp o sl c
      (wv s.mem B (slot w o) w) (wv s.mem B (slot w mo) w) 0) := by
  have hn := hs.nowrap
  have sl8 : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have hhs : ∀ j, 8 * sl + 8 ≤ slot w j := fun j => hdr_lt_slot w j hsl'
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off B (8 * sl)) (s.gpr .x13))
    (by brun [h0, hdr_enc hsl', hs.st (show 8 * sl + 8 ≤ Z by have := hhs 8; omega)]) rfl rfl rfl)
    fun s₁ ⟨hm₁, k₁⟩ => ?_
  have o₁ : Outside B (8 * sl) 8 s.mem s₁.mem := by rw [hm₁]; exact writeW_outside _ _ _ (by omega)
  exact ⟨hs.congr k₁.wr, (k₁.gpr .x0 (by decide)).trans h0, by rw [hm₁]; exact Hdr.store hH hsl hsl' _,
    by rw [hm₁, word_writeW_self, h13, Nat.sub_zero],
    by rw [o₁.wv (by have := hhs o; omega) (by have := sl8 o ho; omega), Nat.pow_zero, Nat.one_mul,
      Nat.mod_eq_of_lt hO],
    o₁.wv (by have := hhs mo; omega) (by have := sl8 mo hmo; omega),
    Frm.of_outside o₁ (by simp), k₁.mono (by decide)⟩

/-- `doubles`: `[o] := 2^c [o] mod m`, for the count `c ≥ 1` in `x13`. -/
theorem doubles_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {mo acc tmp o sl : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    (d1 : acc ≠ mo) (d2 : acc ≠ tmp) (d3 : acc ≠ o) (d6 : tmp ≠ mo) (d7 : tmp ≠ o) (d8 : o ≠ mo)
    (hsl : 16 ≤ sl) (hsl' : sl < 32) {c : Nat} (hc : 1 ≤ c) (hc' : c < 2 ^ 31)
    (h13 : s.gpr .x13 = BitVec.ofNat 64 c)
    (hO : wv s.mem B (slot w o) w < wv s.mem B (slot w mo) w) :
    WP isa (doubles mo acc tmp o sl) s fun t =>
      wv t.mem B (slot w o) w = 2 ^ c * wv s.mem B (slot w o) w % wv s.mem B (slot w mo) w ∧
      Frm B [(slot w acc, 8 * (w + 2)), (slot w tmp, 8 * (w + 2)), (slot w o, 8 * (w + 2)), (8 * sl, 8)]
        s.mem t.mem ∧ Hdr t.mem B w minv ∧ Keep mmRegs s t := by
  unfold doubles
  refine WP.seq (WP.mono (dblStart_ok (acc := acc) (tmp := tmp) hs h0 hH hZ hmo ho hsl hsl' h13 hO)
    fun s₁ h₁ => ?_)
  exact WP.mono (count_loop (n := c) (by omega) _ (fun j hj t hI => dblIter_ok hZ hw hw' hmo hacc htmp ho
    d1 d2 d3 d6 d7 d8 hsl hsl' hc' (by omega) hj hI) h₁) fun t hI => ⟨hI.ov, hI.frm, hI.hdr, hI.keep⟩

end VG.Proof.Bignum.AArch64
