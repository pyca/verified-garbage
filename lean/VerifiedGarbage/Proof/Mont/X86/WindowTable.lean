module

public import VerifiedGarbage.Proof.Mont.X86.WindowSelect
public import VerifiedGarbage.Proof.Mont.X86.WindowCopy
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
public import VerifiedGarbage.Proof.Mont.X86.ContextMul
public import VerifiedGarbage.Proof.Mont.X86.ContextMath
public import VerifiedGarbage.Proof.Dsa.Arithmetic

/-! # The window table: the base's powers `0` to `15`, in Montgomery form -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86

/-- The table past the context, within the working space. -/
structure WinLay (n tab size : Nat) : Prop where
  ctx : contextBytes n ≤ tab
  fit : tab + 128 * n ≤ size

/-- What the table's construction may change. -/
def tableRanges (n tab : Nat) : List (Nat × Nat) :=
  [(slot n 7, 8 * n), (slot n 1, 8 * n), (slot n 2, 16 * n + 4), (tab, 128 * n)]

theorem WinLay.tableLay {n m size tab i : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (W : WinLay n tab size) (hi : i < 9) :
    TableLay n tab (slot n i) size := by
  have n0 := h.modulus.n0
  change 0 < n at n0
  have b := slot_bound (n := n) hi
  have hd := slot_header n i
  have c := W.ctx
  have f := W.fit
  have hc : contextBytes n ≥ 64 := slot_header n 9
  unfold stride at b
  exact ⟨n0, f, by omega, .inl (by omega), by omega, by omega⟩

/-- An entry is apart from every range below the table. -/
theorem table_keep {n tab j : Nat} {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem}
    (O : Outs base rs m m') (hr : ∀ r ∈ rs, r.1 + r.2 ≤ tab) (hfit : tab + 128 * n ≤ 2 ^ 64)
    (hj : j < 16) :
    wordsVal m' base (entry n tab j) n = wordsVal m base (entry n tab j) n := by
  have h1 : 8 * n * j + 8 * n ≤ 128 * n := by
    have := Nat.mul_le_mul_left (8 * n) (show j + 1 ≤ 16 by omega)
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  exact O.val32 (fun r hr' => .inr (by have := hr r hr'; unfold entry; omega))
    (by unfold entry; omega)

theorem op_ranges_le {n o : Nat} (ho : o < 9) :
    ∀ r ∈ [(slot n o, 8 * (contextMod n).n), ((contextMod n).tmp, 8 * (contextMod n).n),
      (slot n 2, accLen (contextMod n))], r.1 + r.2 ≤ contextBytes n := by
  have bo := slot_bound (n := n) ho
  have b1 := slot_bound (n := n) (i := 1) (by decide)
  have b2 := slot_bound (n := n) (i := 2) (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  unfold stride at bo b1 b2
  rcases hr with rfl | rfl | rfl <;> simp only [contextMod, accLen, words] <;> omega

/-- A product within the context keeps the table. -/
theorem op_table_keep {n m size tab o j : Nat} {base : Addr} {s t : State}
    (h : Context n m base size s) (W : WinLay n tab size)
    (K : OpKeep (contextMod n) base (slot n 2) (slot n o) s t) (ho : o < 9) (hj : j < 16) :
    wordsVal t.mem base (entry n tab j) n = wordsVal s.mem base (entry n tab j) n :=
  table_keep K.mem (fun r hr => by have := op_ranges_le ho r hr; have := W.ctx; omega)
    (by have := W.fit; have := h.scr.nowrap; omega) hj

/-- A copy into an entry keeps the context and the other entries. -/
theorem copy_entry_ok {n m size tab src j : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (W : WinLay n tab size) (hsrc : src < 9) (hj : j < 16) :
    WP isa (copyWords n (slot n src) (entry n tab j)) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base (entry n tab j) n = wordsVal s.mem base (slot n src) n ∧
      Outs base (tableRanges n tab) s.mem t.mem ∧
      (∀ i < 16, i ≠ j → wordsVal t.mem base (entry n tab i) n = wordsVal s.mem base (entry n tab i) n) ∧
      (∀ i < 9, wordsVal t.mem base (slot n i) n = wordsVal s.mem base (slot n i) n) ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have L := W.tableLay h hsrc
  obtain ⟨eb, esep, etab, etop⟩ := L.entry hj
  have hn := h.scr.nowrap
  have h0 := slot_bound (n := n) (i := 0) (by decide)
  have hd := slot_header n 0
  unfold stride at h0
  have c := W.ctx
  have bs := slot_bound (n := n) hsrc
  unfold stride at bs
  refine WP.mono (copyWords_ok h.scr L.n0 L.dst_le eb (.inr (.inr (by omega)))) fun t ⟨V, O, K⟩ => ?_
  refine ⟨h.outside_keep K (by decide) (by decide) O (.inl (by omega)) (by omega), V,
    Outs.of_outside (O.mono (o' := tab) (n' := 128 * n) etab etop) (by simp [tableRanges]), ?_, ?_, K⟩
  rotate_left
  · intro i hi
    have bi := slot_bound (n := n) hi
    unfold stride at bi
    exact O.wordsVal (.inl (by omega)) (by omega)
  intro i hi hij
  obtain ⟨eb', _, etab', etop'⟩ := L.entry hi
  have sep : entry n tab i + 8 * n ≤ entry n tab j ∨ entry n tab j + 8 * n ≤ entry n tab i := by
    unfold entry
    rcases Nat.lt_or_gt_of_ne hij with lt | lt
    · have := Nat.mul_le_mul_left (8 * n) (show i + 1 ≤ j by omega)
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
    · have := Nat.mul_le_mul_left (8 * n) (show j + 1 ≤ i by omega)
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
  exact O.wordsVal sep (by omega)


/-- A number in the context outside the table construction's ranges. -/
theorem tableRanges_val32 {n tab i k : Nat} {base : Addr} {m m' : Mem}
    (O : Outs base (tableRanges n tab) m m') (hi : i < 9) (hk : k ≤ 2 * n)
    (hi1 : i ≠ 1) (hi2 : i ≠ 2) (hi7 : i ≠ 7) (hc : contextBytes n ≤ tab)
    (hn : contextBytes n ≤ 2 ^ 64) :
    val32 m' base (slot n i) k = val32 m base (slot n i) k := by
  have h1 := slot_sep (n := n) hi1
  have h2 := slot_sep (n := n) hi2
  have h7 := slot_sep (n := n) hi7
  have bd := slot_bound (n := n) hi
  simp only [stride] at *
  apply O.val32
  · intro r hr
    simp only [tableRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> omega
  · omega

theorem tableRanges_val {n tab i : Nat} {base : Addr} {m m' : Mem}
    (O : Outs base (tableRanges n tab) m m') (hi : i < 9)
    (hi1 : i ≠ 1) (hi2 : i ≠ 2) (hi7 : i ≠ 7) (hc : contextBytes n ≤ tab)
    (hn : contextBytes n ≤ 2 ^ 64) :
    wordsVal m' base (slot n i) n = wordsVal m base (slot n i) n := by
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  exact tableRanges_val32 O hi (Nat.le_refl _) hi1 hi2 hi7 hc hn

theorem tableRanges_op {n tab o : Nat} {base : Addr} {s t : State}
    (K : OpKeep (contextMod n) base (slot n 2) (slot n o) s t) (ho : o = 7) :
    Outs base (tableRanges n tab) s.mem t.mem := by
  subst ho
  refine K.mem.mono ?_
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp [tableRanges, contextMod, accLen, words] <;> omega

/-- One entry more: slot 7 times the base, into slot 7 and the entry at `esi`. -/
theorem tableStep_ok {n m size tab b i : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (W : WinLay n tab size) (hi : i < 14)
    (he : ∀ j < i + 2, wordsVal s.mem base (entry n tab j) n = b ^ j * 2 ^ (64 * n) % m)
    (h7 : wordsVal s.mem base (slot n 7) n = b ^ (i + 1) * 2 ^ (64 * n) % m)
    (hb : wordsVal s.mem base (slot n 5) n = b * 2 ^ (64 * n) % m)
    (hesi : s.gpr .esi = s.gpr .edi + BitVec.ofNat 32 (entry n tab (i + 2))) :
    WP isa (tableStep n tab) s fun t =>
      Context n m base size t ∧
      (∀ j < i + 3, wordsVal t.mem base (entry n tab j) n = b ^ j * 2 ^ (64 * n) % m) ∧
      wordsVal t.mem base (slot n 7) n = b ^ (i + 2) * 2 ^ (64 * n) % m ∧
      wordsVal t.mem base (slot n 5) n = b * 2 ^ (64 * n) % m ∧
      Outs base (tableRanges n tab) s.mem t.mem ∧ Keeps powerClob s t ∧
      t.gpr .esi = t.gpr .edi + BitVec.ofNat 32 (entry n tab (i + 3)) ∧
      t.zf = some (decide (i + 3 = 16)) := by
  have hm0 : 0 < m := by have := h.gt_one; omega
  have cn : contextBytes n ≤ 2 ^ 64 := by have := h.size_le; have := h.scr.nowrap; omega
  have n0 := h.modulus.n0
  change 0 < n at n0
  have fit := W.fit
  have ctx := W.ctx
  have nw := h.scr.nowrap
  have sz := h.scr.size_lt
  have b7 := slot_bound (n := n) (i := 7) (by decide)
  have h07 := slot_le (n := n) (i := 0) (j := 7) (by decide)
  have h7h := slot_header n 7
  unfold stride at b7 h07
  have L := W.tableLay h (i := 7) (by decide)
  obtain ⟨eb, esep, etab, etop⟩ := L.entry (j := i + 2) (by omega)
  unfold tableStep
  refine WP.seq (WP.mono (context_mul_ok h (o := 7) (a := 7) (b := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hb]; exact Nat.mod_lt _ hm0)) fun s₁ ⟨c₁, K₁, lt₁, V₁⟩ => ?_)
  have S₁ : wordsVal s₁.mem base (slot n 7) n = b ^ (i + 2) * 2 ^ (64 * n) % m := by
    have v := VG.Proof.Dsa.mont_product h.coprime (a := b ^ (i + 1)) (b := b)
      (by rw [h7, Nat.mod_mod]) (by rw [hb, Nat.mod_mod]) V₁
    rwa [Nat.mod_eq_of_lt lt₁, ← Nat.pow_succ] at v
  have esi₁ : s₁.gpr .esi = s₁.gpr .edi + BitVec.ofNat 32 (entry n tab (i + 2)) := by
    rw [K₁.gpr _ (by decide), K₁.gpr _ (by decide), hesi]
  have B₁ : wordsVal s₁.mem base (slot n 5) n = b * 2 ^ (64 * n) % m := by
    rw [context_slot_val h (by decide) (by decide) (by decide) (by decide) K₁, hb]
  refine WP.seq (WP.mono (copyOut_ok c₁.scr (k := 2 * n) (src := slot n 7) (dst := entry n tab (i + 2))
    (by omega) (by omega) (by omega) (.inr (by omega)) esi₁) fun s₂ ⟨V₂, O₂, E₂, K₂⟩ => ?_)
  rw [show 4 * (2 * n) = 8 * n by omega] at O₂ E₂
  have c₂ := c₁.outside_keep K₂ (by decide) (by decide) O₂ (.inl (by omega)) (by omega)
  have next : entry n tab (i + 2) + 8 * n = entry n tab (i + 3) := by
    have e : 8 * n * (i + 3) = 8 * n * (i + 2) + 8 * n := by
      rw [show i + 3 = (i + 2) + 1 by omega, Nat.mul_add, Nat.mul_one]
    unfold entry; omega
  refine wp_movS rfl fun s₃ u₃ _ => ?_
  refine wp_addS rfl fun s₄ u₄ _ => ?_
  refine wp_cmpS rfl fun t ft zt => WP.block_nil ?_
  have mt : t.mem = s₂.mem := by rw [ft.mem, u₄.mem, u₃.mem]
  have kt : Keeps [.edx] s₂ t := (u₃.keeps.widen u₄.keeps).trans (ft.keeps _)
  have ct : Context n m base size t := ⟨c₂.scr.of_keeps kt (by decide), c₂.size_le,
    mt ▸ c₂.modulus, c₂.gt_one, mt ▸ c₂.inverse⟩
  have slot_keep (j : Nat) (hj : j < 9) :
      wordsVal s₂.mem base (slot n j) n = wordsVal s₁.mem base (slot n j) n := by
    have bj := slot_bound (n := n) hj
    unfold stride at bj
    exact O₂.wordsVal (.inl (by omega)) (by omega)
  refine ⟨ct, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [mt]
    by_cases e : j = i + 2
    · subst e
      rw [wordsVal_eq_val32, V₂, ← wordsVal_eq_val32, S₁]
    · obtain ⟨eb', esep', etab', etop'⟩ := L.entry (j := j) (by omega)
      have sep : entry n tab j + 8 * n ≤ entry n tab (i + 2) ∨ entry n tab (i + 2) + 8 * n ≤ entry n tab j := by
        unfold entry
        rcases Nat.lt_or_gt_of_ne e with lt | lt
        · have := Nat.mul_le_mul_left (8 * n) (show j + 1 ≤ i + 2 by omega)
          rw [Nat.mul_add, Nat.mul_one] at this; omega
        · have := Nat.mul_le_mul_left (8 * n) (show i + 2 + 1 ≤ j by omega)
          rw [Nat.mul_add, Nat.mul_one] at this; omega
      rw [O₂.wordsVal sep (by omega), op_table_keep h W K₁ (by decide) (by omega), he j (by omega)]
  · rw [mt, slot_keep 7 (by decide), S₁]
  · rw [mt, slot_keep 5 (by decide), B₁]
  · exact ((tableRanges_op K₁ rfl).trans (Outs.of_outside (O₂.mono (o' := tab) (n' := 128 * n) etab etop)
      (by simp [tableRanges]))).trans (mt ▸ Outs.refl _ _ _)
  · exact ((OpKeep.keeps K₁).mono (by decide)).trans ((K₂.mono (by decide)).trans (kt.mono (by decide)))
  · have esi₄ : s₄.gpr .esi = s₂.gpr .edi + BitVec.ofNat 32 (entry n tab (i + 3)) := by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), E₂, next]
    rw [ft.gpr, esi₄, u₄.other _ (by decide), u₃.other _ (by decide)]
  · have esi₄ : s₄.gpr .esi = s₂.gpr .edi + BitVec.ofNat 32 (entry n tab (i + 3)) := by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), E₂, next]
    have edx₄ : s₄.gpr .edx = s₂.gpr .edi + BitVec.ofNat 32 (entry n tab 16) := by
      rw [u₄.gpr, u₃.gpr]
    rw [zt, esi₄, edx₄, ptr_cmp _ (by unfold entry at *; omega) (by unfold entry at *; omega)]
    congr 2
    apply propext
    unfold entry
    constructor
    · intro e
      have := Nat.eq_of_mul_eq_mul_left (show 0 < 8 * n by omega) (show 8 * n * (i + 3) = 8 * n * 16 by omega)
      omega
    · intro e; rw [e]

/-- Entries `2` to `15`. -/
theorem tablePowers_ok {n m size tab b : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (W : WinLay n tab size)
    (hb : wordsVal s.mem base (slot n 5) n = b * 2 ^ (64 * n) % m)
    (he : ∀ j < 2, wordsVal s.mem base (entry n tab j) n = b ^ j * 2 ^ (64 * n) % m)
    (h7 : wordsVal s.mem base (slot n 7) n = b ^ 1 * 2 ^ (64 * n) % m) :
    WP isa (tablePowers n tab) s fun t =>
      Context n m base size t ∧
      (∀ j < 16, wordsVal t.mem base (entry n tab j) n = b ^ j * 2 ^ (64 * n) % m) ∧
      Outs base (tableRanges n tab) s.mem t.mem ∧ Keeps powerClob s t := by
  have fit := W.fit
  have nw := h.scr.nowrap
  have sz := h.scr.size_lt
  unfold tablePowers
  refine WP.seq (wp_movS rfl fun s₁ u₁ _ => wp_addS rfl fun s₂ u₂ _ => WP.block_nil ?_)
  have k₂ : Keeps [.esi] s s₂ := u₁.keeps.widen u₂.keeps
  have mem₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have c₂ : Context n m base size s₂ := ⟨h.scr.of_keeps k₂ (by decide), h.size_le,
    mem₂ ▸ h.modulus, h.gt_one, mem₂ ▸ h.inverse⟩
  have esi₂ : s₂.gpr .esi = s₂.gpr .edi + BitVec.ofNat 32 (entry n tab 2) := by
    rw [u₂.gpr, u₂.other _ (by decide), u₁.gpr, u₁.other _ (by decide)]
  let Inv (i : Nat) (t : State) : Prop :=
    Context n m base size t ∧
    (∀ j < i + 2, wordsVal t.mem base (entry n tab j) n = b ^ j * 2 ^ (64 * n) % m) ∧
    wordsVal t.mem base (slot n 7) n = b ^ (i + 1) * 2 ^ (64 * n) % m ∧
    wordsVal t.mem base (slot n 5) n = b * 2 ^ (64 * n) % m ∧
    Outs base (tableRanges n tab) s.mem t.mem ∧ Keeps powerClob s t ∧
    t.gpr .esi = t.gpr .edi + BitVec.ofNat 32 (entry n tab (i + 2))
  have init : Inv 0 s₂ := ⟨c₂, by simpa only [mem₂] using he, by rw [mem₂]; exact h7,
    by rw [mem₂]; exact hb, mem₂ ▸ Outs.refl _ _ _, k₂.mono (by decide), esi₂⟩
  refine WP.loop (M := isa) (fun c t => ∃ i, c = 14 - i ∧ i < 14 ∧ Inv i t) ?_ 14 s₂ ⟨0, rfl, by decide, init⟩
  rintro c t ⟨i, rfl, hi, ct, E, S7, S5, O, K, P⟩
  refine WP.mono (tableStep_ok ct W hi E S7 S5 P) fun u ⟨cu, Eu, S7u, S5u, Ou, Ku, Pu, zu⟩ => ?_
  by_cases last : i + 1 = 14
  · refine .inl ⟨?_, cu, fun j hj => Eu j (by omega), O.trans Ou, K.trans Ku⟩
    simp only [eval, zu, show i + 3 = 16 by omega, decide_true, Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, 14 - (i + 1), by omega, i + 1, rfl, by omega, cu, Eu, S7u, S5u, O.trans Ou,
      K.trans Ku, Pu⟩
    simp only [eval, zu, show i + 3 ≠ 16 by omega, decide_false, Option.map_some, Bool.not_false]

/-- The table of the base's powers `0` to `15`, from one (slot 6) and the base
(slot 5) in Montgomery form. -/
theorem buildTable_ok {n m size tab b : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (W : WinLay n tab size)
    (hy : wordsVal s.mem base (slot n 6) n = 2 ^ (64 * n) % m)
    (hb : wordsVal s.mem base (slot n 5) n = b * 2 ^ (64 * n) % m) :
    WP isa (buildTable n tab) s fun t =>
      Context n m base size t ∧
      (∀ j < 16, wordsVal t.mem base (entry n tab j) n = b ^ j * 2 ^ (64 * n) % m) ∧
      Outs base (tableRanges n tab) s.mem t.mem ∧ Keeps powerClob s t := by
  have cn : contextBytes n ≤ 2 ^ 64 := by have := h.size_le; have := h.scr.nowrap; omega
  unfold buildTable
  refine WP.seq (WP.mono (copy_entry_ok h W (src := 6) (j := 0) (by decide) (by decide))
    fun s₁ ⟨c₁, V₁, O₁, _, S₁, K₁⟩ => ?_)
  refine WP.seq (WP.mono (copy_entry_ok c₁ W (src := 5) (j := 1) (by decide) (by decide))
    fun s₂ ⟨c₂, V₂, O₂, E₂, S₂, K₂⟩ => ?_)
  have L := W.tableLay c₂ (i := 7) (by decide)
  have b5 := slot_bound (n := n) (i := 5) (by decide)
  have s57 := slot_le (n := n) (i := 5) (j := 7) (by decide)
  have h0 := slot_le (n := n) (i := 0) (j := 7) (by decide)
  have b7 := slot_bound (n := n) (i := 7) (by decide)
  have hd := slot_header n 7
  have hn := h.scr.nowrap
  have ctx := W.ctx
  have sz := h.size_le
  unfold stride at b5 s57 h0 b7
  refine WP.seq (WP.mono (copyWords_ok c₂.scr L.n0 (by omega) L.dst_le (.inr (.inr (by omega))))
    fun s₃ ⟨V₃, O₃, K₃⟩ => ?_)
  have c₃ := c₂.outside_keep K₃ (by decide) (by decide) O₃ (.inl (by omega)) (by omega)
  have keep₃ (j : Nat) (hj : j < 16) :
      wordsVal s₃.mem base (entry n tab j) n = wordsVal s₂.mem base (entry n tab j) n :=
    table_keep (Outs.of_outside O₃ (rs := [(slot n 7, 8 * n)]) (by simp))
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; omega)
      (by have := W.fit; omega) hj
  have one : (2 : Nat) ^ (64 * n) % m = b ^ 0 * 2 ^ (64 * n) % m := by rw [Nat.pow_zero, Nat.one_mul]
  have B₃ : wordsVal s₃.mem base (slot n 5) n = b * 2 ^ (64 * n) % m := by
    rw [O₃.wordsVal (.inl (by omega)) (by omega), S₂ 5 (by decide), S₁ 5 (by decide), hb]
  refine WP.mono (tablePowers_ok c₃ W B₃ ?_ (by rw [V₃, S₂ 5 (by decide), S₁ 5 (by decide), hb, Nat.pow_one]))
    fun t ⟨ct, Et, Ot, Kt⟩ => ?_
  · intro j hj
    rw [keep₃ j (by omega)]
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · rw [E₂ 0 (by decide) (by decide), V₁, hy, one]
    · rw [V₂, S₁ 5 (by decide), hb, Nat.pow_one]
  refine ⟨ct, Et, ?_, ?_⟩
  · exact ((O₁.trans O₂).trans (Outs.of_outside O₃ (by simp [tableRanges]))).trans Ot
  · exact (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans Kt

end VG.Proof.Mont.X86.Dynamic
