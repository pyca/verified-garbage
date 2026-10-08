import VerifiedGarbage.Proof.X448.X86.Columns

/-!
# X448 on x86 (32-bit): addition and subtraction

`vg_gf448_r16_add` and `vg_gf448_r16_sub`'s arithmetic (`addFn`, `subFn`):
`esi` and `ebp` point at the operands `a` and `b`, whose limbs are added (or
subtracted, with twice the prime added first, so that no limb subtraction
borrows) into `TMP`, then normalized into the element at `o`.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

/-- The operand pointers of the pointwise operations. -/
structure Ptrs (s : State) (a b : Nat) : Prop where
  a : s.gpr .esi = s.gpr .edi + BitVec.ofNat 32 a
  b : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 b

theorem Ptrs.keep {s t : State} {a b : Nat} (h : Ptrs s a b) {rs : List Reg} (hk : Keeps rs s t)
    (hr : ∀ r ∈ [Reg.esi, .ebp, .edi], r ∉ rs) : Ptrs t a b :=
  ⟨by rw [hk.1 _ (hr _ (by simp)), hk.1 _ (hr _ (by simp))]; exact h.a,
    by rw [hk.1 _ (hr _ (by simp)), hk.1 _ (hr _ (by simp))]; exact h.b⟩

/-- The operand pointers `esi = ws + a` and `ebp = ws + b`. -/
theorem ptrs_ok {s : State} {base : Addr} {n o a b : Nat} (hc : FnCtx s base n o a) (hn : 3 < n)
    (hvb : arg s 3 = BitVec.ofNat 32 b) :
    WP isa (.block (argPtr .esi 2 ++ argPtr .ebp 3)) s fun t =>
      Ptrs t a b ∧ t.mem = s.mem ∧ Keeps [.esi, .ebp] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (argPtr_ok hc.args (by have := hc.n3; omega) (by decide) hc.argA) fun t ⟨tp, tm, tk⟩ => ?_
  obtain ⟨ta, targ⟩ := hc.args.keep (tk.1 _ (by decide)) tk.2.1 tk.2.2 (by rw [tm]; exact Outside.refl _ _ _ _)
  refine WP.mono (argPtr_ok ta hn (by decide) (by rw [targ 3 hn]; exact hvb)) fun u ⟨up, um, uk⟩ =>
    ⟨⟨?_, up⟩, um.trans tm, (tk.mono (by decide)).trans (uk.mono (by decide))⟩
  rw [uk.1 _ (by decide), uk.1 _ (by decide)]; exact tp

theorem addStep_ok {s : State} {base : Addr} (hs : Scr s base) {a b i : Nat} (hp : Ptrs s a b)
    (ha : Slot a) (hb : Slot b) (hi : i < 28) :
    WP isa (.block [.mov .eax (.mem (at_ .esi (4 * i))), .alu .add .eax (.mem (at_ .ebp (4 * i))),
      st .eax (TMP + 4 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 4 * i))
        (BitVec.ofNat 32 (limbs s.mem base a i + limbs s.mem base b i)) ∧ Keeps [.eax] s t := by
  have ha' : a + 112 ≤ 3584 := ha
  have hb' : b + 112 ≤ 3584 := hb
  refine wp_load (hs.ea_ptr (k := 4 * i) hp.a (by omega)) (hs.read (by omega)) fun t ht => ?_
  have ts := hs.of_upd ht (by decide)
  have tb : t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 b := by
    rw [ht.other .ebp (by decide), ht.other .edi (by decide)]; exact hp.b
  have ea := ts.ea_ptr (k := 4 * i) tb (by omega)
  have rd : readSrc t (.mem (at_ .ebp (4 * i))) = some (word t.mem base (b + 4 * i)) := by
    simp only [readSrc, ea, State.load32,
      ts.read (d := b + 4 * i) (n := 4) (by omega), ite_true]
  refine wp_alu (Or.inl rfl) rd fun u hu _ => ?_
  refine store_ok (ts.of_upd hu (by decide)) (by simp only [TMP]; omega) fun v hv => WP.block_nil ⟨?_, ?_⟩
  · rw [hv.mem, hu.mem, ht.mem, hu.gpr]
    change s.mem.writeW _ (t.gpr .eax + word t.mem base (b + 4 * i)) = _
    rw [ht.gpr, ht.mem]
    apply congrArg (s.mem.writeW _)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  · exact (ht.rest (by decide)).trans ((hu.rest (by decide)).trans (hv.rest _))

theorem subK_nat (i : Nat) : (subK i).toNat = bias i := by
  by_cases h : i = 14 <;> simp only [subK, bias, h, ite_true, ite_false] <;> decide

theorem subStep_ok {s : State} {base : Addr} (hs : Scr s base) {a b i : Nat} (hp : Ptrs s a b)
    (ha : Slot a) (hb : Slot b) (hi : i < 28)
    (ab : limbs s.mem base a i < radix) (bb : limbs s.mem base b i < radix) :
    WP isa (.block [.mov .eax (.mem (at_ .esi (4 * i))), .alu .add .eax (.imm (subK i)),
      .alu .sub .eax (.mem (at_ .ebp (4 * i))), st .eax (TMP + 4 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 4 * i))
        (BitVec.ofNat 32 (difference (limbs s.mem base a) (limbs s.mem base b) i)) ∧ Keeps [.eax] s t := by
  have ha' : a + 112 ≤ 3584 := ha
  have hb' : b + 112 ≤ 3584 := hb
  refine wp_load (hs.ea_ptr (k := 4 * i) hp.a (by omega)) (hs.read (by omega)) fun t ht => ?_
  refine wp_alu (Or.inl rfl) rfl fun u hu _ => ?_
  have us := (hs.of_upd ht (by decide)).of_upd hu (by decide)
  have ub : u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 b := by
    rw [hu.other .ebp (by decide), hu.other .edi (by decide), ht.other .ebp (by decide),
      ht.other .edi (by decide)]; exact hp.b
  have ea := us.ea_ptr (k := 4 * i) ub (by omega)
  have rd : readSrc u (.mem (at_ .ebp (4 * i))) = some (word u.mem base (b + 4 * i)) := by
    simp only [readSrc, ea, State.load32,
      us.read (d := b + 4 * i) (n := 4) (by omega), ite_true]
  refine wp_alu (Or.inr (Or.inl rfl)) rd fun v hv _ => ?_
  refine store_ok (us.of_upd hv (by decide)) (by simp only [TMP]; omega) fun w hw => WP.block_nil ⟨?_, ?_⟩
  · rw [hw.mem, hv.mem, hu.mem, ht.mem, hv.gpr]
    change s.mem.writeW _ (u.gpr .eax - word u.mem base (b + 4 * i)) = _
    rw [hu.gpr, hu.mem, ht.mem]
    change s.mem.writeW _ (t.gpr .eax + subK i - _) = _
    rw [ht.gpr]
    apply congrArg (s.mem.writeW _)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_add, subK_nat, BitVec.toNat_ofNat]
    change (2 ^ 32 - limbs s.mem base b i + (limbs s.mem base a i + bias i) % 2 ^ 32) % 2 ^ 32 =
      (limbs s.mem base a i + bias i - limbs s.mem base b i) % 2 ^ 32
    have h := bias_bound i
    simp only [radix] at ab bb h
    omega
  · exact (ht.rest (by decide)).trans ((hu.rest (by decide)).trans ((hv.rest (by decide)).trans (hw.rest _)))

/-- The result of a pointwise operation, normalized, as the field functions
state it. -/
abbrev FnPost (base : Addr) (o : Nat) (s t : State) : Prop :=
  Keeps (.esi :: clob) s t ∧ FieldMem base o s.mem t.mem WORK ∧ Bounded t.mem base o

theorem addBody_ok {s : State} {base : Addr} {o a b : Nat} (hc : FnCtx s base 4 o a)
    (hvb : arg s 3 = BitVec.ofNat 32 b) (hb : Slot b) (ab : Bounded s.mem base a)
    (bb : Bounded s.mem base b) :
    WP isa (.block (argPtr .esi 2 ++ argPtr .ebp 3 ++ addCols ++ normalize)) s fun t =>
      FnPost base o s t ∧ F t.mem base o = F s.mem base a + F s.mem base b := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (ptrs_ok hc (by decide) hvb) fun t ⟨tp, tm, tk⟩ => ?_
  have tc := hc.keep tk (by decide) (by decide) (by rw [tm]; exact Outside.refl _ _ _ _)
  let f := fun i => limbs t.mem base a i + limbs t.mem base b i
  have fb : ∀ i < 28, f i ≤ 2 ^ 32 - radix := by
    intro i hi
    have h1 := ab i hi
    have h2 := bb i hi
    change limbs t.mem base a i + limbs t.mem base b i ≤ _
    rw [tm]
    simp only [radix] at h1 h2 ⊢
    omega
  refine WP.mono (columns_normalize tc fb (WP.mono (columns_ok tc.scr (by decide : .edi ∉ [Reg.eax]) fb ?_)
    fun u ⟨uf, um, uk⟩ => ⟨uf, um, uk.mono (by decide)⟩))
    fun u ⟨op, ub, uv⟩ => ⟨⟨(tk.mono (by decide)).trans (op.1.mono (by decide)), by
      rw [← tm]; exact op.2, ub⟩, toFe_add ?_⟩
  · intro i hi u us um uk
    refine WP.mono (addStep_ok us (tp.keep uk (by decide)) tc.slotA hb hi) fun v ⟨vm, vk⟩ => ⟨?_, vk⟩
    rw [input_limb um tc.slotA hi, input_limb um hb hi] at vm
    exact vm
  · rw [uv, valN_add, tm]

theorem subBody_ok {s : State} {base : Addr} {o a b : Nat} (hc : FnCtx s base 4 o a)
    (hvb : arg s 3 = BitVec.ofNat 32 b) (hb : Slot b) (ab : Bounded s.mem base a)
    (bb : Bounded s.mem base b) :
    WP isa (.block (argPtr .esi 2 ++ argPtr .ebp 3 ++ subCols ++ normalize)) s fun t =>
      FnPost base o s t ∧ F t.mem base o = F s.mem base a - F s.mem base b := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (ptrs_ok hc (by decide) hvb) fun t ⟨tp, tm, tk⟩ => ?_
  have tc := hc.keep tk (by decide) (by decide) (by rw [tm]; exact Outside.refl _ _ _ _)
  rw [← tm] at ab bb
  let f := difference (limbs t.mem base a) (limbs t.mem base b)
  have fb : ∀ i < 28, f i ≤ 2 ^ 32 - radix := fun i hi => Nat.le_of_lt (difference_bound ab i hi)
  refine WP.mono (columns_normalize tc fb (WP.mono (columns_ok tc.scr (by decide : .edi ∉ [Reg.eax]) fb ?_)
    fun u ⟨uf, um, uk⟩ => ⟨uf, um, uk.mono (by decide)⟩))
    fun u ⟨op, ub, uv⟩ => ⟨⟨(tk.mono (by decide)).trans (op.1.mono (by decide)), by
      rw [← tm]; exact op.2, ub⟩, toFe_sub ?_⟩
  · intro i hi u us um uk
    have ea := input_limb um tc.slotA hi
    have eb := input_limb um hb hi
    refine WP.mono (subStep_ok us (tp.keep uk (by decide)) tc.slotA hb hi (ea ▸ ab i hi) (eb ▸ bb i hi))
      fun v ⟨vm, vk⟩ => ⟨?_, vk⟩
    simp only [difference, ea, eb] at vm
    exact vm
  · rw [← tm, Nat.add_mod, uv, ← Nat.add_mod, difference_val bb, Nat.add_mul_mod_self_right]

end VG.Proof.X448.X86
