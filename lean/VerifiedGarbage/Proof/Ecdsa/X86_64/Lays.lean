import VerifiedGarbage.Proof.Ecdsa.X86_64.SlotOps

/-!
# ECDSA on x86-64: where the ladder's and the powers' slots are

The slots of `c.ladderCfg`, `c.powP` and `c.powN` are numbered slots `c.sl i`
for distinct `i`, so they are apart as `ladder_ok` and `pow_ok` need
(`ladLay`, `powLayP`, `powLayN`): each fact is one about the numbers `i`,
which `decide` checks.
-/

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-- `x` and `y`, `k` and `k'` bytes long, are apart. -/
abbrev Apart (x k y k' : Nat) : Prop := x + k ≤ y ∨ y + k' ≤ x

theorem sl_mem_map (hn : 0 < c.n) {i : Nat} {l : List Nat} : c.sl i ∈ l.map c.sl ↔ i ∈ l := by
  constructor
  · intro h
    obtain ⟨j, hj, e⟩ := List.mem_map.mp h
    exact sl_inj c hn e ▸ hj
  · exact List.mem_map_of_mem

theorem map_sl_disj (hn : 0 < c.n) {l₁ l₂ : List Nat} (h : ∀ i ∈ l₁, i ∉ l₂) :
    ∀ x ∈ l₁.map c.sl, x ∉ l₂.map c.sl := by
  intro x hx hx'
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact h i hi ((sl_mem_map hn).mp hx')

theorem map_sl_nodup (hn : 0 < c.n) {l : List Nat} (h : l.Nodup) : (l.map c.sl).Nodup :=
  List.Pairwise.map c.sl (fun _ _ hab e => hab (sl_inj c hn e)) h

/-- Numbered slots, apart from the modulus's and the temporary area. -/
theorem lay_map (hc : BaseCfgOk c) {M : Mod} (hmo : M.mo = c.sl MP) (htmp : M.tmp = c.sl TMP)
    (hMn : M.n = c.n) {l : List Nat} (hl : ∀ i ∈ l, i < 45 ∧ i ≠ MP ∧ i ≠ TMP) :
    Lay M size (· ∈ l.map c.sl) := by
  have hn := hc.n0
  refine ⟨fun x hx => ?_, fun x y hx hy hxy => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn]; exact sl_le c hc.n10 (hl i hi).1
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
    rw [hMn]; exact sl_apart c fun h => hxy (h ▸ rfl)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn, hmo]; exact sl_apart c (hl i hi).2.1
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn, htmp]; exact sl_apart c (hl i hi).2.2

/-- A numbered slot is below the tables, but the temporary area, which for
nine words is between the second and the third, and for six past them all. -/
theorem sl_below_bits (c : Cfg) {i : Nat} (hi : i < 45) (j t : Nat)
    (hT : i ≠ TMP ∨ 2 ≤ j ∧ c.n ≠ 6 := by sl_or) :
    c.sl i + 8 * c.n ≤ bitsAt c.n j + t := by
  rw [bitsAt_eq, sl_eq']
  by_cases h : i = TMP ∧ c.n = 9
  · have hj := (hT.resolve_left fun e => e h.1).1
    have hix : ix c i = 55 := by unfold ix; rw [ite_eq_left h.2, ite_eq_left h.1]
    rw [hix, h.2]
    have := Nat.mul_le_mul_left (64 * 9 + 8) hj
    omega
  · have hix : ix c i = i := by
      by_cases ht : i = TMP
      · have h6 : c.n ≠ 6 := (hT.resolve_left fun e => e ht).2
        have h9 : c.n ≠ 9 := fun e => h ⟨ht, e⟩
        exact ix_of_ne c (.inr fun e => e.elim h9 h6)
      · exact ix_of_ne c (.inl ⟨ht, by omega, by omega⟩)
    rw [hix]
    have := Nat.mul_le_mul_left (8 * c.n) hi
    rw [Nat.mul_succ] at this
    omega

/-- For six words the temporary area is in slot `83`'s place. -/
theorem sl_tmp6 (c : Cfg) (h6 : c.n = 6) : c.sl TMP = 64 + 8 * c.n * 83 := by
  rw [sl_eq', ix_tmp6 c h6]

/-- A numbered slot is apart from an area past the first two tables, which
for six words ends below the temporary area. -/
theorem sl_apart_hi (c : Cfg) {i : Nat} (hi : i < 45) {a L : Nat} (hlo : bitsAt c.n 2 ≤ a)
    (hhi : c.n = 6 → a + L ≤ c.sl TMP) : c.sl i + 8 * c.n ≤ a ∨ a + L ≤ c.sl i := by
  by_cases h : i = TMP ∧ c.n = 6
  · obtain ⟨rfl, h6⟩ := h
    exact .inr (hhi h6)
  · refine .inl ?_
    have := sl_below_bits c hi 2 0 (by
      by_cases ht : i = TMP
      · exact .inr ⟨by decide, fun e => h ⟨ht, e⟩⟩
      · exact .inl ht)
    omega

/-- The temporary area is apart from the first four tables but the second (the bits of `p - 2`)
for nine words. -/
theorem tmp_apart_bits (c : Cfg) {j : Nat} (hj : j ≠ 1 ∨ c.n ≠ 9) (hj4 : j < 4) (t : Nat) (ht : t ≤ 64 * c.n + 8) :
    c.sl TMP + 8 * c.n ≤ bitsAt c.n j ∨ bitsAt c.n j + t ≤ c.sl TMP := by
  rw [bitsAt_eq, sl_eq']
  by_cases h9 : c.n = 9
  · have hj := hj.resolve_right fun e => e h9
    rw [ix_tmp c h9]
    rw [h9] at ht ⊢
    rcases Nat.lt_or_ge j 1 with h0 | h2
    · right; obtain rfl : j = 0 := by omega
      omega
    · left; have := Nat.mul_le_mul_left (64 * 9 + 8) (show 2 ≤ j by omega); omega
  · by_cases h6 : c.n = 6
    · rw [ix_tmp6 c h6]; right; rw [h6] at ht ⊢
      have := Nat.mul_le_mul_left (64 * 6 + 8) (show j ≤ 3 by omega); omega
    · rw [ix_of_ne c (.inr fun e => e.elim h9 h6)]; left; simp only [TMP]
      have := Nat.mul_le_mul_left (64 * c.n + 8) (Nat.zero_le j)
      omega

/-- A numbered slot is apart from the first `t` bytes of table `j`: the
temporary area too, unless the table is the second, for nine words. -/
theorem sl_apart_bits (c : Cfg) {i : Nat} (hi : i < 45) {j : Nat} (hj : i ≠ TMP ∨ j ≠ 1 ∨ c.n ≠ 9) (t : Nat)
    (ht : t ≤ 64 * c.n + 8) (hj4 : j < 4 := by omega) :
    c.sl i + 8 * c.n ≤ bitsAt c.n j ∨ bitsAt c.n j + t ≤ c.sl i := by
  by_cases hT : i = TMP
  · subst hT; exact tmp_apart_bits c (hj.resolve_left fun h => h rfl) hj4 t ht
  · exact .inl (by simpa only [Nat.add_zero] using sl_below_bits c hi j 0 (.inl hT))

/-- A numbered slot is apart from the word past the table of `k`'s bits. -/
theorem sl_apart_pad (c : Cfg) {i : Nat} (hi : i < 45) :
    c.sl i + 8 * c.n ≤ bitsAt c.n 0 + 64 * c.n ∨ bitsAt c.n 0 + 64 * c.n + 8 ≤ c.sl i := by
  rcases sl_apart_bits c hi (j := 0) (.inr (.inl (by decide))) (64 * c.n + 8) (by omega) with h | h
  · exact .inl (by omega)
  · exact .inr (by omega)

theorem rcbApart_of (hn : 0 < c.n) {S : RcbSlots} {p q o : Pt} {lw lr : List Nat}
    (hw : rcbW S o = lw.map c.sl) (hr : rcbR S p q = lr.map c.sl) (hnd : lw.Nodup)
    (hd : ∀ i ∈ lr, i ∉ lw) : RcbApart S p q o :=
  ⟨hw ▸ map_sl_nodup hn hnd, by rw [hw, hr]; exact map_sl_disj hn hd⟩

theorem ladLay (hc : BaseCfgOk c) : LadLay c.ladderCfg size := by
  have hn := hc.n0
  have h7 := hc.n10
  refine ⟨?_, rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, DX, DY, DZ])
      (lr := [AP, B3P, RX, RY, RZ, RX, RY, RZ]) rfl rfl (by decide) (by decide),
    rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, TX, TY, TZ])
      (lr := [AP, B3P, DX, DY, DZ, GX, GY, ONEP]) rfl rfl (by decide) (by decide), ?_,
    ⟨fun h => by have := sl_inj c hn (i := RX) (j := RY) h; exact absurd this (by decide),
      fun h => by have := sl_inj c hn (i := RX) (j := RZ) h; exact absurd this (by decide),
      fun h => by have := sl_inj c hn (i := RY) (j := RZ) h; exact absurd this (by decide)⟩, ?_,
    ⟨show 1 ≤ 64 * c.n by omega, show 64 * c.n < 2 ^ 16 by omega⟩, bitsAt_le c h7 (by decide), ?_⟩
  · exact lay_map hc rfl rfl rfl (l := [AP, B3P, GX, GY, ONEP, RX, RY, RZ, T0, T1, T2, T3, T4, T5,
      DX, DY, DZ, TX, TY, TZ]) (by decide)
  · exact map_sl_disj hn (l₁ := [AP, B3P, GX, GY, ONEP])
      (l₂ := [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ])
      (by decide)
  · exact map_sl_disj hn (l₁ := [RX, RY, RZ]) (l₂ := [DX, DY, DZ, TX, TY, TZ]) (by decide)
  · intro w hw
    simp only [ladW, List.mem_append, List.mem_map, List.mem_singleton] at hw
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · have hy' : y ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX,
          TY, TZ].map c.sl := hy
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy'
      have hl : ∀ i ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX,
          TY, TZ], i < 45 ∧ i ≠ TMP := by decide
      exact Or.inr (sl_below_bits c (hl i hi).1 0 0 (.inl (hl i hi).2))
    · show bitsAt c.n 0 + 64 * c.n ≤ c.sl TMP ∨ c.sl TMP + 8 * c.n ≤ bitsAt c.n 0
      have := tmp_apart_bits c (j := 0) (.inl (by decide)) (by decide) (64 * c.n) (by omega); omega

theorem powLay_of (hc : BaseCfgOk c) {jm : Nat} (hjm : jm ∉ [ACC, PT, TMP])
    (minv : BitVec 64) {red : Red} {adx sparse : Bool}
    {base one j : Nat} (hj : j < 3) (hb : base ∉ [ACC, PT, TMP]) (hb45 : base < 45) (ho : one ≠ ACC)
    (ho45 : one < 45) {nb : Nat} (hnb : 1 ≤ nb ∧ nb ≤ 64 * c.n) (hjT : j ≠ 1 ∨ c.n ≠ 9) :
    PowLay ⟨⟨c.n, c.sl jm, c.sl TMP, minv, red, false, adx, sparse, false⟩, c.sl ACC, c.sl PT, c.sl base, c.sl one, bitsAt c.n j,
      nb⟩ size := by
  have hn := hc.n0
  have h7 := hc.n10
  have hw : ∀ i, i ∉ [ACC, PT, TMP] →
      ∀ w ∈ powW ⟨⟨c.n, c.sl jm, c.sl TMP, minv, red, false, adx, sparse, false⟩, c.sl ACC, c.sl PT, c.sl base, c.sl one,
        bitsAt c.n j, nb⟩, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
    intro i hi w hw
    simp only [powW, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    rcases hw with rfl | rfl | rfl
    · exact sl_apart c hi.1
    · exact sl_apart c hi.2.1
    · exact sl_apart c hi.2.2
  refine ⟨sl_le c h7 (by decide), sl_le c h7 (by decide), sl_le c h7 hb45, sl_le c h7 ho45,
    Nat.le_trans (Nat.add_le_add_left hnb.2 _) (bitsAt_le c h7 hj), ⟨hnb.1, show nb < 2 ^ 16 by omega⟩,
    sl_apart c (by decide), sl_apart c (by decide), sl_apart c (by decide), sl_apart c (Ne.symm ho),
    hw base hb, ?_,
    hw jm hjm⟩
  intro w hw'
  simp only [powW, List.mem_cons, List.not_mem_nil, or_false] at hw'
  rcases hw' with rfl | rfl | rfl
  · exact Or.inr (sl_below_bits c (by decide) j 0)
  · exact Or.inr (sl_below_bits c (by decide) j 0)
  · show bitsAt c.n j + nb ≤ c.sl TMP ∨ c.sl TMP + 8 * c.n ≤ bitsAt c.n j
    have := tmp_apart_bits c hjT (by omega) (64 * c.n) (by omega); omega

/-- The power modulo `p`, which reads the bits of `p - 2` where the
temporary area of nine words is. -/
theorem powLayP (hc : BaseCfgOk c) (h9 : c.n ≠ 9) : PowLay c.powP size :=
  powLay_of hc (jm := MP) (by decide) _ (j := 1) (by decide) (base := RZ) (by decide) (by decide)
    (one := ONEP) (by decide) (by decide) ⟨by have := hc.n0; omega, Nat.le_refl _⟩ (.inr h9)

/-- `e < 2^(bitLen e k)`, `bitLen e k ≤ k`, and `1 ≤ bitLen e k` for `1 ≤ e < 2^k`. -/
theorem bitLen_ok (e : Nat) : ∀ k, e < 2 ^ k → e < 2 ^ bitLen e k ∧ bitLen e k ≤ k ∧ (1 ≤ e → 1 ≤ bitLen e k)
  | 0, h => ⟨h, Nat.le_refl _, fun h1 => by simp at h; omega⟩
  | k + 1, h => by
    rw [bitLen]
    split
    · rename_i hk
      obtain ⟨a, b, c⟩ := bitLen_ok e k hk
      exact ⟨a, by omega, c⟩
    · exact ⟨h, Nat.le_refl _, fun _ => by omega⟩

/-- The power mod `n`'s bits: `n - 2 < 2^nbits`, `1 ≤ nbits ≤ 64 n`. -/
theorem nbitsN_ok (hc : BaseCfgOk c) :
    1 ≤ bitLen (c.C.n - 2) (64 * c.n) ∧ bitLen (c.C.n - 2) (64 * c.n) ≤ 64 * c.n ∧
      c.C.n - 2 < 2 ^ bitLen (c.C.n - 2) (64 * c.n) := by
  have hlt : c.C.n - 2 < 2 ^ (64 * c.n) := by have := hc.n_lt; omega
  obtain ⟨a, b, d⟩ := bitLen_ok (c.C.n - 2) (64 * c.n) hlt
  exact ⟨d (by have := hc.n_ge; omega), b, a⟩

theorem powLayN (hc : BaseCfgOk c) : PowLay c.powN size :=
  powLay_of hc (jm := MN) (by decide) _ (j := 2) (by decide) (base := KM) (by decide) (by decide)
    (one := ONEN) (by decide) (by decide) ⟨(nbitsN_ok hc).1, (nbitsN_ok hc).2.1⟩ (.inl (by decide))

end VG.Proof.Ecdsa.X86_64
