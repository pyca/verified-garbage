module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout

/-!
# ECDSA on PPC64LE: where the inlined ladder's slots are

For coordinates of more than 6 words the ladder inlines the complete
addition (`ladder_ok`), whose slots are the numbered slots `c.sl i` of
`c.ladderCfg` for distinct `i`, with the ladder's `G` at `gx`, `gy` and
`ONEP`, so they are apart as it needs (`ladLayI`), as on 32-bit ARM
(`Proof/Ecdsa/Arm/Lays.lean`): each fact is one about the numbers `i`, which
`decide` checks. What the ladder writes (`ladWp`) is the slots `ladIx`, the
functions' own working space and, for coordinates of at most 6 words, the
point functions' slots (`ptW`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE VG.Proof.Weierstrass.PPC64LE.Point

variable {c : Cfg}

theorem sl_inj (c : Cfg) (hn : 0 < c.n) {i j : Nat} (h : c.sl i = c.sl j) : i = j := by
  rw [sl_eq, sl_eq] at h
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 8 * c.n) (by omega)

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

/-- Numbered slots, apart from the modulus's and the temporary area, below
the functions' own working space. -/
theorem lay_map (hc : CfgOk c) {M : Mod} (hmo : M.mo = c.sl MP) (htmp : M.tmp = c.sl TMP)
    (hMn : M.n = c.n) {l : List Nat} (hl : ∀ i ∈ l, i < 45 ∧ i ≠ MP ∧ i ≠ TMP) :
    Lay M (own M.n) (· ∈ l.map c.sl) := by
  refine ⟨fun x hx => ?_, fun x y hx hy hxy => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn]; exact sl_below_own c hc.n10 (hl i hi).1
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
    rw [hMn]; exact sl_apart c fun h => hxy (h ▸ rfl)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn, hmo]; exact sl_apart c (hl i hi).2.1
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn, htmp]; exact sl_apart c (hl i hi).2.2

theorem rcbApart_of (hn : 0 < c.n) {S : RcbSlots} {p q o : Pt} {lw lr : List Nat}
    (hw : rcbW S o = lw.map c.sl) (hr : rcbR S p q = lr.map c.sl) (hnd : lw.Nodup)
    (hd : ∀ i ∈ lr, i ∉ lw) : RcbApart S p q o :=
  ⟨hw ▸ map_sl_nodup hn hnd, by rw [hw, hr]; exact map_sl_disj hn hd⟩

/-- A numbered slot is below the point functions' slots. -/
theorem sl_below_pt (h3 : 3 ≤ c.n) (h6 : c.n ≤ 6) {i : Nat} (hi : i < 45) :
    c.sl i + 8 * c.n ≤ Impl.Weierstrass.Point.oAt c.n := by
  obtain ⟨h1, h2, he, hb3, ha, hq, hp, hoo, -, -⟩ := VG.Proof.Weierstrass.PPC64LE.Point.lay_nums h3 h6
  have := sl_lt c hi
  rw [sl_eq c 45] at this
  omega

/-- The ladder of `c`, from the point at `gx`, `gy`, `ONEP`. -/
abbrev ladderAt (c : Cfg) (gx gy : Nat) : LadderCfg := { c.ladderCfg with G := c.pt gx gy ONEP }

theorem nmem_of {x : Nat} {l l₂ : List Nat} (hx : x ∉ l) (hs : ∀ y ∈ l₂, y ∈ l) : x ∉ l₂ :=
  fun h => hx (hs x h)

theorem ne_of_nmem {x y : Nat} {l : List Nat} (hx : x ∉ l) (hy : y ∈ l) : x ≠ y :=
  fun h => hx (h ▸ hy)

/-- The slots the ladder writes, by number. -/
abbrev ladIx : List Nat :=
  [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP]

theorem ladSlots_eq (c : Cfg) (gx gy : Nat) : ladSlots (ladderAt c gx gy) = [AP, B3P, gx, gy, ONEP, RX, RY,
    RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TX, TY, TZ].map c.sl := rfl

/-- What the ladder writes. -/
theorem ladWp_eq (gx gy : Nat) : ladWp (ladderAt c gx gy) =
    slW c ladIx ++ [(own c.n, 64 * c.n)] ++ ptW c.n := rfl

/-- The inlined ladder's slots, for its `G` at slots `gx` and `gy` that it
does not write. -/
theorem ladLayI (hc : CfgOk c) {gx gy : Nat} (hgx : gx < 45) (hgy : gy < 45) (hgw : gx ∉ MP :: ladIx)
    (hgw' : gy ∉ MP :: ladIx) : LadLayI (ladderAt c gx gy) := by
  have hn := hc.n0
  have h7 := hc.n10
  have hsz : size = 8192 := rfl
  have ngx : ∀ {l : List Nat}, (∀ y ∈ l, y ∈ MP :: ladIx) → gx ∉ l := nmem_of hgw
  have ngy : ∀ {l : List Nat}, (∀ y ∈ l, y ∈ MP :: ladIx) → gy ∉ l := nmem_of hgw'
  refine ⟨⟨?_, rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, DX, DY, DZ])
      (lr := [AP, B3P, RX, RY, RZ, RX, RY, RZ]) rfl rfl (by decide) (by decide),
    rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, TX, TY, TZ])
      (lr := [AP, B3P, DX, DY, DZ, gx, gy, ONEP]) rfl rfl (by decide) ?_,
    map_sl_disj hn (l₁ := [AP, B3P, gx, gy, ONEP])
      (l₂ := [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ]) ?_,
    ⟨fun h => absurd (sl_inj c hn h) (by decide), fun h => absurd (sl_inj c hn h) (by decide),
      fun h => absurd (sl_inj c hn h) (by decide)⟩,
    map_sl_disj hn (l₁ := [RX, RY, RZ]) (l₂ := [DX, DY, DZ, TX, TY, TZ]) (by decide),
    ⟨show 1 ≤ 8 * c.C.len by have := hc.len8; omega,
      show 8 * c.C.len < 2 ^ 16 by have := hc.len_hi; omega⟩,
    (by have := bitsAt_le c h7 (j := 0) (by decide); have := hc.len_hi;
        change bitsAt c.n 0 + 8 * c.C.len ≤ 8192; omega), ?_⟩, ?_, ?_, ?_⟩
  · rw [ladSlots_eq]
    refine lay_map hc rfl rfl rfl ?_
    simp only [List.forall_mem_cons]
    repeat' apply And.intro
    all_goals try (apply ne_of_nmem (l := MP :: ladIx) hgw; decide)
    all_goals try (apply ne_of_nmem (l := MP :: ladIx) hgw'; decide)
    all_goals first | decide | with_reducible assumption
  · simp only [List.forall_mem_cons]
    repeat' apply And.intro
    all_goals try (apply ngx; decide)
    all_goals try (apply ngy; decide)
    all_goals decide
  · simp only [List.forall_mem_cons]
    repeat' apply And.intro
    all_goals try (apply ngx; decide)
    all_goals try (apply ngy; decide)
    all_goals decide
  · intro w hw
    simp only [ladW, List.mem_append, List.mem_map, List.mem_singleton] at hw
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · have hy' : y ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX,
          TY, TZ].map c.sl := hy
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy'
      have hl : ∀ i ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX,
          TY, TZ], i < 45 := by decide
      exact Or.inr (sl_below_bits c h7 (hl i hi) 0 0)
    · exact Or.inr (sl_below_bits c h7 (i := TMP) (by decide) 0 0)
  · rw [ladSlots_eq]
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    exact sl_al c i
  · show 4096 ≤ bitsAt c.n 0; rw [bitsAt_eq]; omega
  · show 8 * c.C.len < 2 ^ 15
    have := hc.len_hi; omega

/-- A slot the ladder does not write apart from what it writes. -/
theorem apart_ladWp (h3 : 3 ≤ c.n) (h7 : c.n < 10) {gx gy i : Nat} (hi : i < 45) (hr : i ∉ ladIx) :
    ∀ w ∈ ladWp (ladderAt c gx gy), c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  rw [ladWp_eq]
  refine apart_append (apart_append (apart_slW hr) (apart_own h7 hi)) ?_
  intro w hw
  simp only [ptW] at hw
  split at hw
  · rw [List.mem_singleton.mp hw]
    exact Or.inl (sl_below_pt h3 ‹_› hi)
  · simp at hw

theorem fixedOk_ladWp (h3 : 3 ≤ c.n) (h7 : c.n < 10) (gx gy : Nat) : FixedOk c (ladWp (ladderAt c gx gy)) := by
  rw [ladWp_eq]
  refine ((fixedOk_slW (l := ladIx) (by decide)).append (fixedOk_own h7)).append ?_
  intro w hw
  simp only [ptW] at hw
  split at hw
  · rw [List.mem_singleton.mp hw]
    exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_pt h3 ‹_› (i := 12) (by decide)))
  · simp at hw

theorem ladWp_le (h3 : 3 ≤ c.n) (h7 : c.n < 10) (gx gy : Nat) :
    ∀ w ∈ ladWp (ladderAt c gx gy), w.1 + w.2 ≤ size := by
  rw [ladWp_eq]
  have hsz : size = 8192 := rfl
  intro w hw
  simp only [List.mem_append, ptW] at hw
  rcases hw with (hw | hw) | hw
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have := sl_le c h7 (i := i) ((by decide : ∀ i ∈ ladIx, i < 45) i hi)
    dsimp only; omega
  · rw [List.mem_singleton.mp hw]; have := own_eq c.n; dsimp only; omega
  · split at hw
    · rw [List.mem_singleton.mp hw]
      obtain ⟨h1, h2, he, hb3, ha, hq, hp, hoo, -, -⟩ := VG.Proof.Weierstrass.PPC64LE.Point.lay_nums h3 ‹_›
      dsimp only; omega
    · simp at hw

theorem tbl_apart_ladWp (h3 : 3 ≤ c.n) (h7 : c.n < 10) (gx gy j t : Nat) :
    ∀ w ∈ ladWp (ladderAt c gx gy), bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  rw [ladWp_eq]
  intro w hw
  simp only [List.mem_append, ptW] at hw
  rcases hw with (hw | hw) | hw
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have := sl_below_bits c h7 (i := i) ((by decide : ∀ i ∈ ladIx, i < 45) i hi) j t
    exact Or.inr this
  · rw [List.mem_singleton.mp hw]
    have := own_below_bits c h7 j
    exact Or.inr (by dsimp only; omega)
  · split at hw
    · rw [List.mem_singleton.mp hw]
      obtain ⟨h1, h2, he, hb3, ha, hq, hp, hoo, -, -⟩ := VG.Proof.Weierstrass.PPC64LE.Point.lay_nums h3 ‹_›
      have hb := bitsAt_eq c j
      exact Or.inr (by dsimp only; omega)
    · simp at hw

end VG.Proof.Ecdsa.PPC64LE
