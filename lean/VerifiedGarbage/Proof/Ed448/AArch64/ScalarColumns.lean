import VerifiedGarbage.Proof.Ed448.AArch64.ScalarOperands

/-!
# Ed448 scalar multiply-add on AArch64: product scanning

A term (`term_ok`): `x_i · y_j`, loaded from the working space, added to a
three-word accumulator; a column's terms (`terms_ok`), by induction on them;
and the sixteen columns (`columns_ok`), by induction on the columns, each
storing its low word at `ACC` and passing the rest of its accumulator on, in
`x5–x7` rotated. The columns of `r + k s` sum to it (`mulCols_sum`).
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x word off Outside ofs contains_sc writeW_outside
  word_writeW_self)

/-- The working space at `base`, in `x2`, with zero in `x26`. -/
structure Wk (s : State) (base : Addr) : Prop where
  x2 : s.gpr .x2 = base
  wr : (⟨base, 8192⟩ : Region) ∈ s.wr
  z : s.gpr .x26 = 0

theorem Wk.of_keeps {rs : List Reg} {s t : State} {base : Addr} (h : Wk s base) (k : Keeps rs s t)
    (h2 : .x2 ∉ rs) (h26 : .x26 ∉ rs) : Wk t base :=
  ⟨(k.gpr _ h2).trans h.x2, k.wr ▸ h.wr, (k.gpr _ h26).trans h.z⟩

/-- The `i`-th left and `j`-th right operand. -/
abbrev xw (m : Mem) (base : Addr) (i : Nat) : Nat := (word m base (XK + 8 * i)).toNat
abbrev yw (m : Mem) (base : Addr) (j : Nat) : Nat := (word m base (YS + 8 * j)).toNat

theorem umulh_eq (a b : BitVec 64) :
    (a * b).toNat + 2 ^ 64 * (BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)).toNat =
      a.toNat * b.toNat := mul_halves a b

/-- `term`: `a₀ a₁ a₂ += x_i · y_j`. -/
theorem term_ok {s : State} {base : Addr} {a0 a1 a2 : Reg} (hs : Wk s base)
    (hd : [a0, a1, a2, .x12, .x13, .x14, .x15, .x26, .x2].Nodup) {i j : Nat} (hi : i < 16)
    (hj : j < 9) (hb : rv s [a0, a1, a2] + xw s.mem base i * yw s.mem base j < 2 ^ 192) :
    WP isa (.block (term a0 a1 a2 i j)) s fun t =>
      rv t [a0, a1, a2] = rv s [a0, a1, a2] + xw s.mem base i * yw s.mem base j ∧
      Keeps [.x12, .x13, .x14, .x15, a0, a1, a2] s t := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h0a, h0b, h0c, h0d, h0z, h0x⟩, ⟨h12, h1a, h1b, h1c, h1d, h1z, h1x⟩,
    ⟨h2a, h2b, h2c, h2d, h2z, h2x⟩, -⟩ := hd
  have l1 : InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (XK + 8 * i)) 8 := by
    rw [hs.x2]; exact ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [XK]; omega)⟩
  have l2 : InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (YS + 8 * j)) 8 := by
    rw [hs.x2]; exact ⟨_, List.mem_append_right _ hs.wr, contains_sc (by simp only [YS]; omega)⟩
  apply WP.of_runBlock
  simp only [term, Z, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, addr, State.load,
    Size.bytes, show (XK + 8 * i) % 8 = 0 by simp only [XK]; omega,
    show XK + 8 * i < 4096 * 8 by simp only [XK]; omega,
    show (YS + 8 * j) % 8 = 0 by simp only [YS]; omega,
    show YS + 8 * j < 4096 * 8 by simp only [YS]; omega, and_self, l1, l2,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.c_addWithCarry, BitVec.setWidth_eq, Ne.symm h01, Ne.symm h02, Ne.symm h12,
    h0a, h0b, h0c, h0d, h1a, h1b, h1c, h1d, h2a, h2b, h2c, h2d,
    Ne.symm h0d, Ne.symm h0z, Ne.symm h1z, hs.z,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [rv, RegUpd.gpr_write, RegUpd.gpr_addWithCarry, BitVec.setWidth_eq, h01, h02, h12,
      Ne.symm h01, Ne.symm h02, Ne.symm h12, ite_true, ite_false, Nat.mul_zero, Nat.add_zero]
    have ex : xw s.mem base i = (s.mem.read (s.gpr .x2 + BitVec.ofNat 64 (XK + 8 * i)) 8).toNat := by
      simp only [xw, word, off, Mem.readW, hs.x2, BitVec.setWidth_eq]
    have ey : yw s.mem base j = (s.mem.read (s.gpr .x2 + BitVec.ofNat 64 (YS + 8 * j)) 8).toNat := by
      simp only [yw, word, off, Mem.readW, hs.x2, BitVec.setWidth_eq]
    rw [ex, ey] at hb ⊢
    simp only [rv, Nat.mul_zero, Nat.add_zero] at hb
    generalize s.mem.read (s.gpr .x2 + BitVec.ofNat 64 (XK + 8 * i)) 8 = x at hb ⊢
    generalize s.mem.read (s.gpr .x2 + BitVec.ofNat 64 (YS + 8 * j)) 8 = y at hb ⊢
    have hp := umulh_eq x y
    generalize x * y = lo at hp ⊢
    generalize BitVec.ofNat 64 (x.toNat * y.toNat / 2 ^ 64) = hi at hp ⊢
    have v0 := addWithCarry_val (s.gpr a0) lo false
    generalize decide (2 ^ 64 ≤ (s.gpr a0).toNat + lo.toNat + false.toNat) = c0 at v0 ⊢
    have v1 := addWithCarry_val (s.gpr a1) hi c0
    generalize decide (2 ^ 64 ≤ (s.gpr a1).toNat + hi.toNat + c0.toNat) = c1 at v1 ⊢
    have v2 : (s.gpr a2 + 0 + BitVec.ofNat 64 c1.toNat).toNat = ((s.gpr a2).toNat + c1.toNat) % 2 ^ 64 := by
      rw [show s.gpr a2 + 0 = s.gpr a2 from BitVec.add_zero _, BitVec.toNat_add, BitVec.toNat_ofNat]
      have := Bool.toNat_le c1
      rw [Nat.mod_eq_of_lt (a := c1.toNat) (by omega)]
    rw [v2]
    have := (s.gpr a0).isLt; have := (s.gpr a1).isLt; have := (s.gpr a2).isLt
    have := Bool.toNat_le c0; have := Bool.toNat_le c1
    generalize (s.gpr a0 + lo + BitVec.ofNat 64 false.toNat).toNat = A0 at v0 ⊢
    simp only [Bool.toNat_false, Nat.add_zero] at v0
    generalize (s.gpr a1 + hi + BitVec.ofNat 64 c0.toNat).toNat = A1 at v1 ⊢
    generalize x.toNat * y.toNat = P at hp hb ⊢
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]

/-- The sum of a column's terms. -/
def colSum (xv yv : Nat → Nat) (ts : List (Nat × Nat)) : Nat := (ts.map fun t => xv t.1 * yv t.2).sum

theorem colSum_cons (xv yv : Nat → Nat) (t : Nat × Nat) (ts : List (Nat × Nat)) :
    colSum xv yv (t :: ts) = xv t.1 * yv t.2 + colSum xv yv ts := by
  simp [colSum]

/-- A column's terms, by induction on them. -/
theorem terms_ok {base : Addr} {a0 a1 a2 : Reg}
    (hd : [a0, a1, a2, .x12, .x13, .x14, .x15, .x26, .x2].Nodup) :
    ∀ (ts : List (Nat × Nat)) (s : State), Wk s base → (∀ t ∈ ts, t.1 < 16 ∧ t.2 < 9) →
      rv s [a0, a1, a2] + colSum (xw s.mem base) (yw s.mem base) ts < 2 ^ 192 →
      WP isa (.block (ts.flatMap fun t => term a0 a1 a2 t.1 t.2)) s fun s' =>
        rv s' [a0, a1, a2] = rv s [a0, a1, a2] + colSum (xw s.mem base) (yw s.mem base) ts ∧
        Keeps [.x12, .x13, .x14, .x15, a0, a1, a2] s s'
  | [], s, _, _, _ => WP.block_nil ⟨by simp [colSum], Keeps.refl _ _⟩
  | t :: ts, s, hs, hc, hb => by
    rw [List.flatMap_cons, WP.block_append_iff]
    rw [colSum_cons] at hb
    have hct := hc t List.mem_cons_self
    refine WP.mono (term_ok hs hd hct.1 hct.2 (by omega)) fun s1 ⟨e1, k1⟩ => ?_
    have hn := hd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨⟨-, -, -, -, -, -, h0z, h0x⟩, ⟨-, -, -, -, -, h1z, h1x⟩, ⟨-, -, -, -, h2z, h2x⟩, -⟩ := hn
    have hs1 : Wk s1 base := hs.of_keeps k1
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨by decide, by decide, by decide, by decide, Ne.symm h0x, Ne.symm h1x, Ne.symm h2x⟩)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨by decide, by decide, by decide, by decide, Ne.symm h0z, Ne.symm h1z, Ne.symm h2z⟩)
    have m1 : s1.mem = s.mem := k1.mem
    refine WP.mono (terms_ok hd ts s1 hs1 (fun t' ht' => hc t' (List.mem_cons_of_mem _ ht'))
      (by rw [e1, m1]; omega)) fun s2 ⟨e2, k2⟩ => ⟨?_, k1.trans k2⟩
    rw [e2, e1, colSum_cons, m1]
    omega

/-- The registers a product's columns change. -/
def colX : List Reg := [.x5, .x6, .x7, .x12, .x13, .x14, .x15]

/-- The accumulator of column `k`. -/
def acc (k : Nat) : List Reg := [accR k 0, accR k 1, accR k 2]

theorem accR_mod (k n : Nat) : accR k n = [Reg.x5, .x6, .x7].getD ((k + n) % 3) .x5 := rfl

theorem acc_succ (k : Nat) : acc (k + 1) = [accR k 1, accR k 2, accR k 0] := by
  simp only [acc, accR_mod]
  refine List.cons_eq_cons.mpr ⟨by rw [Nat.add_right_comm], List.cons_eq_cons.mpr
    ⟨by rw [Nat.add_assoc], List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩
  rw [show k + 1 + 2 = k + 3 by omega, Nat.add_mod_right, Nat.add_zero]

theorem acc_cases (k : Nat) :
    acc k = [.x5, .x6, .x7] ∨ acc k = [.x6, .x7, .x5] ∨ acc k = [.x7, .x5, .x6] := by
  simp only [acc, accR_mod]
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h <;>
  simp only [Nat.add_mod k, h] <;> simp

theorem acc_nodup (k : Nat) :
    [accR k 0, accR k 1, accR k 2, .x12, .x13, .x14, .x15, .x26, .x2].Nodup := by
  have := acc_cases k
  simp only [acc, List.cons.injEq, and_true] at this
  rcases this with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> rw [h0, h1, h2] <;> decide

theorem acc_colX (k : Nat) : ∀ r ∈ [Reg.x12, .x13, .x14, .x15, accR k 0, accR k 1, accR k 2],
    r ∈ colX := by
  have := acc_cases k
  simp only [acc, List.cons.injEq, and_true] at this
  rcases this with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> rw [h0, h1, h2] <;> decide

theorem accR_colX (k n : Nat) (hn : n < 3) : accR k n ∈ colX := by
  have := acc_colX k
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl <;> exact this _ (by simp)

/-- A column: its terms, its low word stored at `ACC + 8k`, and the rest of
the accumulator passed on. -/
theorem column_ok {s : State} {base : Addr} (hs : Wk s base) (k : Nat) (hk : k < 16)
    (hc : ∀ t ∈ mulCol k, t.1 < 16 ∧ t.2 < 9)
    (hb : rv s (acc k) + colSum (xw s.mem base) (yw s.mem base) (mulCol k) < 2 ^ 192) :
    WP isa (.block (column k)) s fun s' =>
      (word s'.mem base (ACC + 8 * k)).toNat + 2 ^ 64 * rv s' (acc (k + 1)) =
        rv s (acc k) + colSum (xw s.mem base) (yw s.mem base) (mulCol k) ∧
      (∀ r, r ∉ colX → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Outside base (ACC + 8 * k) 8 s.mem s'.mem := by
  have hsub := acc_colX k
  rw [column, WP.block_append_iff]
  refine WP.mono (terms_ok (acc_nodup k) (mulCol k) s hs hc hb) fun s1 ⟨e1, k1⟩ => ?_
  have hs1 : Wk s1 base := hs.of_keeps k1 (fun h => by have := hsub _ h; simp [colX] at this)
    (fun h => by have := hsub _ h; simp [colX] at this)
  have hw : InRegions s1.wr (s1.gpr .x2 + BitVec.ofNat 64 (ACC + 8 * k)) 8 := by
    rw [hs1.x2]; exact ⟨_, hs1.wr, contains_sc (by simp only [ACC]; omega)⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_str_x ⟨by simp only [ACC]; omega, by simp only [ACC]; omega⟩ hw, ?_⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits from by decide,
    ite_true, Option.some.injEq, exists_eq_left']
  have hn := acc_nodup k
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  obtain ⟨⟨h01, h02, -⟩, ⟨h12, -⟩, -⟩ := hn
  refine ⟨?_, fun r hr => ?_, k1.rd, k1.wr, k1.sp, ?_⟩
  · rw [acc_succ]
    simp only [rv, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ _ (Ne.symm h01),
      RegUpd.gpr_write_of_ne _ _ _ (Ne.symm h02), RegUpd.mem_write, hs1.x2, word_writeW_self]
    simp only [acc, rv] at e1 ⊢
    rw [show (BitVec.setWidth 64 (BitVec.setWidth Size.x.bits (0 : BitVec 16) <<< (16 * 0))).toNat = 0
      from rfl]
    omega
  · have hr0 : r ≠ accR k 0 := fun e => hr (e ▸ accR_colX k 0 (by decide))
    rw [RegUpd.gpr_write_of_ne _ _ _ hr0]
    exact k1.gpr r (fun h => hr (hsub _ h))
  · simp only [RegUpd.mem_write, hs1.x2]
    rw [← k1.mem]; exact writeW_outside _ _ _ (by simp only [ACC]; omega)

theorem mv_succ_last (m : Mem) (base : Addr) :
    ∀ (o n : Nat), mv m base o (n + 1) = mv m base o n + 2 ^ (64 * n) * (word m base (o + 8 * n)).toNat
  | o, 0 => by simp [mv]
  | o, n + 1 => by
    rw [mv, mv_succ_last m base (o + 8) n, mv, pow64_succ,
      show o + 8 + 8 * n = o + 8 * (n + 1) by omega]
    generalize 2 ^ (64 * n) = Q
    grind

/-- The columns' values: `Σ_{m<n} 2^(64m) colSum (mulCol (k + m))`, in Horner
form, whose only power is `2⁶⁴`. -/
def colsVal (xv yv : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | k, n + 1 => colSum xv yv (mulCol k) + 2 ^ 64 * colsVal xv yv (k + 1) n

theorem colsVal_succ_last (xv yv : Nat → Nat) :
    ∀ k n, colsVal xv yv k (n + 1) = colsVal xv yv k n + 2 ^ (64 * n) * colSum xv yv (mulCol (k + n))
  | k, 0 => by simp [colsVal]
  | k, n + 1 => by
    rw [colsVal, colsVal_succ_last xv yv (k + 1) n, colsVal, pow64_succ,
      show k + 1 + n = k + (n + 1) by omega]
    generalize 2 ^ (64 * n) = Q
    grind

theorem colSum_le (xv yv : Nat → Nat) :
    ∀ ts : List (Nat × Nat), (∀ t ∈ ts, xv t.1 < 2 ^ 64 ∧ yv t.2 < 2 ^ 64) →
      colSum xv yv ts ≤ ts.length * ((2 ^ 64 - 1) * (2 ^ 64 - 1))
  | [], _ => by simp [colSum]
  | t :: ts, h => by
    rw [colSum_cons, List.length_cons, Nat.succ_mul]
    have h1 := h t List.mem_cons_self
    have hp : xv t.1 * yv t.2 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
    have := colSum_le xv yv ts fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    omega

theorem colSum_congr (xv yv xv' yv' : Nat → Nat) (ts : List (Nat × Nat))
    (h : ∀ t ∈ ts, xv t.1 = xv' t.1 ∧ yv t.2 = yv' t.2) :
    colSum xv yv ts = colSum xv' yv' ts := by
  simp only [colSum]
  exact congrArg List.sum (List.map_congr_left fun t ht => by rw [(h t ht).1, (h t ht).2])

theorem mulCol_hc : ∀ k < 16, ∀ t ∈ mulCol k, t.1 < 16 ∧ t.2 < 9 := by decide
theorem mulCol_len : ∀ k < 16, (mulCol k).length ≤ 9 := by decide

theorem colX_x2 : Reg.x2 ∉ colX := by decide
theorem colX_x26 : Reg.x26 ∉ colX := by decide

/-- The first `n` columns of the product. -/
theorem columns_ok {s₀ : State} {base : Addr} (hs : Wk s₀ base) (h0 : rv s₀ (acc 0) = 0) :
    ∀ n ≤ 16, WP isa (.block ((List.range n).flatMap column)) s₀ fun s =>
      (∀ r, r ∉ colX → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧
      Outside base ACC (8 * n) s₀.mem s.mem ∧
      mv s.mem base ACC n + 2 ^ (64 * n) * rv s (acc n) =
        colsVal (xw s₀.mem base) (yw s₀.mem base) 0 n ∧
      rv s (acc n) < 2 ^ 128
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _,
      by simp [mv, colsVal, h0], by rw [h0]; decide⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (columns_ok hs h0 n (by omega)) fun s ⟨g, rd, wr, sp, o, e, b⟩ => ?_
    have hsS : Wk s base := ⟨(g _ colX_x2).trans hs.x2, wr ▸ hs.wr, (g _ colX_x26).trans hs.z⟩
    have hcn := mulCol_hc n (by omega)
    have same : ∀ t ∈ mulCol n, xw s.mem base t.1 = xw s₀.mem base t.1 ∧
        yw s.mem base t.2 = yw s₀.mem base t.2 := fun t ht => by
      have := hcn t ht
      exact ⟨by rw [xw, o.word (by simp only [XK, ACC]; omega) (by simp only [XK]; omega)],
        by rw [yw, o.word (by simp only [YS, ACC]; omega) (by simp only [YS]; omega)]⟩
    have cs := colSum_congr _ _ _ _ (mulCol n) same
    have cb := colSum_le (xw s.mem base) (yw s.mem base) (mulCol n)
      fun t _ => ⟨(word s.mem base _).isLt, (word s.mem base _).isLt⟩
    have hwn := Nat.mul_le_mul_right ((2 ^ 64 - 1) * (2 ^ 64 - 1)) (mulCol_len n (by omega))
    rw [List.flatMap_singleton]
    refine WP.mono (column_ok hsS n (by omega) hcn (by omega))
      fun s' ⟨e', g', rd', wr', sp', o'⟩ => ?_
    refine ⟨fun r hr => (g' r hr).trans (g r hr), rd'.trans rd, wr'.trans wr, sp'.trans sp,
      (o.mono (Nat.le_refl _) (by omega)).trans (o'.mono (by omega) (by omega)), ?_, ?_⟩
    · rw [mv_succ_last, Outside.mv_eq o' n ACC (by omega) (by simp only [ACC]; omega),
        colsVal_succ_last, Nat.zero_add, pow64_succ, ← cs]
      generalize 2 ^ (64 * n) = Q at e ⊢
      calc mv s.mem base ACC n + Q * (word s'.mem base (ACC + 8 * n)).toNat +
            2 ^ 64 * Q * rv s' (acc (n + 1))
          = mv s.mem base ACC n + Q * ((word s'.mem base (ACC + 8 * n)).toNat +
              2 ^ 64 * rv s' (acc (n + 1))) := by grind
        _ = mv s.mem base ACC n + Q * rv s (acc n) + Q * colSum (xw s.mem base)
              (yw s.mem base) (mulCol n) := by rw [e']; grind
        _ = _ := by rw [e]
    · omega

/-- Eight words' value, in Horner form. -/
def val8 (f : Nat → Nat) : Nat :=
  f 0 + 2 ^ 64 * (f 1 + 2 ^ 64 * (f 2 + 2 ^ 64 * (f 3 + 2 ^ 64 * (f 4 + 2 ^ 64 * (f 5 +
    2 ^ 64 * (f 6 + 2 ^ 64 * f 7))))))

theorem range8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl

/-- The columns of `r + k s`: with `k` the left operands `0–7`, `r` the
left operands `8–15`, `s` the right operands `0–7` and one the right
operand 8. -/
theorem mulCols_sum (xv yv : Nat → Nat) (h1 : yv 8 = 1) :
    colsVal xv yv 0 16 = val8 xv * val8 yv + val8 (fun i => xv (8 + i)) := by
  simp only [colsVal, colSum, mulCol, range8, List.filter_cons, List.filter_nil, Nat.reduceSub,
    Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceAdd, and_self, and_true, and_false,
    decide_true, decide_false, ite_true, ite_false, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_nil, List.sum_cons, List.sum_nil, val8, h1, Nat.mul_one,
    Nat.add_zero, Nat.zero_le, Nat.le_refl, Bool.false_eq_true]
  generalize 2 ^ 64 = B
  grind

theorem mv8_val (m : Mem) (base : Addr) (o : Nat) :
    mv m base o 8 = val8 fun i => (word m base (o + 8 * i)).toNat := by
  simp only [mv8, val8, Nat.mul_zero, Nat.add_zero, Nat.reduceMul]

theorem pow_mono {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) h

theorem sq_add_le (n : Nat) : 2 ^ n * 2 ^ n + 2 ^ n ≤ 2 ^ (2 * n + 1) := by
  have : 2 ^ n ≤ 2 ^ (n + n) := Nat.pow_le_pow_right (by omega) (by omega)
  rw [Nat.pow_succ, Nat.mul_two, Nat.two_mul, Nat.pow_add]
  rw [Nat.pow_add] at this
  omega

/-- `columns`: `r + k s` into the sixteen words at `ACC`, from `k`, `r`, `s`
(each below `2^456`) and one at `XK`, `XK + 64`, `YS` and `YS + 64`. -/
theorem product_ok {s : State} {base : Addr} (hb : s.gpr .x2 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hone : word s.mem base (YS + 64) = 1)
    (hk : mv s.mem base XK 8 < 2 ^ 456) (hr : mv s.mem base (XK + 64) 8 < 2 ^ 456)
    (hs : mv s.mem base YS 8 < 2 ^ 456) :
    WP isa (.block columns) s fun t =>
      mv t.mem base ACC 16 = mv s.mem base (XK + 64) 8 + mv s.mem base XK 8 * mv s.mem base YS 8 ∧
      (∀ r, r ∉ .x26 :: colX → t.gpr r = s.gpr r) ∧ t.gpr .x26 = 0 ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp ∧ Outside base ACC 128 s.mem t.mem := by
  rw [columns, WP.block_append_iff]
  apply WP.mono (Q := fun (a : State) => Wk a base ∧ rv a (acc 0) = 0 ∧ a.mem = s.mem ∧
    (∀ r, r ∉ [Reg.x26, .x5, .x6, .x7] → a.gpr r = s.gpr r) ∧ a.rd = s.rd ∧ a.wr = s.wr ∧ a.sp = s.sp)
  · apply WP.of_runBlock
    simp only [Z, runBlock_cons, runStep_some, runBlock_nil, exec,
      show 16 * 0 < Size.x.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨⟨?_, hw, rfl⟩, rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]; exact hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  intro a ⟨ha, h0, ma, ga, rda, wra, spa⟩
  refine WP.mono (columns_ok ha h0 16 (Nat.le_refl _)) fun t ⟨gt, rdt, wrt, spt, ot, et, bt⟩ => ?_
  have hsum := mulCols_sum (xw a.mem base) (yw a.mem base) (by rw [yw, ma, Nat.mul_comm, hone]; rfl)
  have ex : val8 (xw a.mem base) = mv s.mem base XK 8 := by rw [mv8_val, ma]
  have ey : val8 (yw a.mem base) = mv s.mem base YS 8 := by rw [mv8_val, ma]
  have er : val8 (fun i => xw a.mem base (8 + i)) = mv s.mem base (XK + 64) 8 := by
    rw [mv8_val, ma]
    exact congrArg val8 (funext fun i => by rw [xw, show XK + 8 * (8 + i) = XK + 64 + 8 * i by omega])
  rw [hsum, ex, ey, er] at et
  refine ⟨?_, fun r hr => ?_, (gt _ colX_x26).trans ha.z, rdt.trans rda, wrt.trans wra,
    spt.trans spa, by rw [← ma]; exact ot⟩
  · generalize hP : (2 : Nat) ^ (64 * 16) = P at et
    have hb : (2 : Nat) ^ 456 * 2 ^ 456 + 2 ^ 456 ≤ P :=
      Nat.le_trans (Nat.le_trans (sq_add_le 456) (pow_mono (a := 2 * 456 + 1) (b := 64 * 16) (by decide))) (Nat.le_of_eq hP)
    generalize (2 : Nat) ^ 456 = Q at hk hs hr hb
    have hp := Nat.mul_lt_mul'' hk hs
    have hA : rv t (acc 16) = 0 := by
      rcases Nat.eq_zero_or_pos (rv t (acc 16)) with h | h
      · exact h
      · have := Nat.mul_le_mul_left P h
        generalize P * rv t (acc 16) = A at et this
        generalize mv s.mem base XK 8 * mv s.mem base YS 8 = M at hp et
        omega
    rw [hA, Nat.mul_zero, Nat.add_zero] at et
    rw [et, Nat.add_comm]
  · simp only [List.mem_cons, not_or] at hr
    have h5 : r ≠ .x5 := by rintro rfl; exact hr.2 (by decide)
    have h6 : r ≠ .x6 := by rintro rfl; exact hr.2 (by decide)
    have h7 : r ≠ .x7 := by rintro rfl; exact hr.2 (by decide)
    have hr' : r ∉ [Reg.x26, .x5, .x6, .x7] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hr.1, h5, h6, h7⟩
    rw [gt r hr.2, ga r hr']

/-- `8n` bytes at `base + o` are `n` words. -/
theorem decode_mv (m : Mem) (base : Addr) :
    ∀ (n o : Nat), Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m (off base o) (8 * n)) = mv m base o n
  | 0, _ => rfl
  | n + 1, o => by
    have e := words_step m (off base o) (8 * (n + 1)) 0 (by omega)
    simp only [Nat.mul_zero, Nat.sub_zero, Nat.zero_add, Nat.mul_one, BitVec.add_zero] at e
    rw [e, show 8 * (n + 1) - 8 = 8 * n by omega, show off base o + BitVec.ofNat 64 8 = off base (o + 8)
      from Offset.add_add base o 8, decode_mv m base n (o + 8), mv]

end VG.Proof.Ed448.AArch64
