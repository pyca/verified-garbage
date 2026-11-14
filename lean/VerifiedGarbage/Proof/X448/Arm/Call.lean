module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.X448.Arm.Field
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.X448.Arm.MulLoop
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.Arm.Mem
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X448.Arm.Carry
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.X448.Arm.Init
import VerifiedGarbage.Proof.X448.Arm.Normalize
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X448.Arm.Columns
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `X448.Arm.Fn`, which only this module used -/

section

/-!
# X448 on ARMv7: the field functions

`fn hasB op` (`Impl/X448/Arm.lean`), from `ws`, `o`, `a` and `b` in
`r0`–`r3` (`Entry`): the registers it restores are saved at `SAVE`
(`strs_ok`), `r6` takes the mask and `r9`, `lr` and `r12` the pointers to
`[o]`, `[a]` and `[b]` (`entry_ok`); then the operation, and the registers
are loaded back (`ldrs_ok`). `fn_ok` is what the function does: it keeps the
callee-saved registers and `r0`, and changes the memory only at `[o]` and in
its own working space (`FieldMem`), where the operation's result is.
-/

@[expose] public section

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_ldr wp_str wp_movw wp_dp op2_reg)

/-- The working space at `r0`, without the mask. -/
structure Base (s : State) (base : Addr) : Prop where
  r0 : State.addr (s.gpr .r0) = base
  wr : (⟨base, 8192⟩ : Region) ∈ s.wr
  nowrap : (s.gpr .r0).toNat + 8192 ≤ 2 ^ 32

theorem Base.of_rest {rs : List Reg} {s s' : State} {base : Addr} (hs : Base s base)
    (h : Rest rs s s') (h0 : .r0 ∉ rs) : Base s' base :=
  ⟨by rw [h.gpr _ h0]; exact hs.r0, h.wr ▸ hs.wr, by rw [h.gpr _ h0]; exact hs.nowrap⟩

theorem Base.ea {s : State} {base : Addr} (hs : Base s base) {d : Nat} (hd : d < 8192) :
    State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off base d := by
  rw [VG.Arm.addr_add (by have := hs.nowrap; omega_arith), hs.r0]

/-- The registers the functions restore, and where they are saved. -/
def saves : List (Reg × Nat) :=
  [(.r4, SAVE), (.r5, SAVE + 4), (.r6, SAVE + 8), (.r7, SAVE + 12), (.r9, SAVE + 16), (.lr, SAVE + 20)]

theorem saveFn_eq : saveFn = saves.map fun p => st p.1 p.2 := by decide

theorem restoreFn_eq : restoreFn = saves.map fun p => ld p.1 p.2 := by decide

theorem saves_bound : ∀ p ∈ saves, SAVE ≤ p.2 ∧ p.2 + 4 ≤ SAVE + 24 := by decide

/-- Stores of registers at offsets of the working space, apart from each other. -/
theorem strs_ok {s : State} {base : Addr} (hs : Base s base) :
    ∀ (l : List (Reg × Nat)), (∀ p ∈ l, p.2 + 4 ≤ 4096) →
    l.Pairwise (fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2) →
    WP isa (.block (l.map fun p => st p.1 p.2)) s fun s' =>
      Rest [] s s' ∧ (∀ x, (∀ p ∈ l, ofs base x < p.2 ∨ p.2 + 4 ≤ ofs base x) → s'.mem x = s.mem x) ∧
      ∀ p ∈ l, word s'.mem base p.2 = s.gpr p.1
  | [], _, _ => WP.block_nil ⟨Rest.refl _ _, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩
  | p :: l, hl, hp => by
    have h0 := hl p List.mem_cons_self
    rw [List.pairwise_cons] at hp
    rw [List.map_cons]
    refine wp_str (by omega_arith) (hs.ea (by omega_arith)) ⟨_, hs.wr, contains_sc (by omega_arith)⟩ fun s₁ m₁ => ?_
    have hs₁ := hs.of_rest (m₁.rest []) (by decide)
    refine WP.mono (strs_ok hs₁ l (fun q h => hl q (List.mem_cons_of_mem _ h)) hp.2) fun s' ⟨K, O, V⟩ => ?_
    have O₁ : Outside base p.2 4 s.mem s₁.mem := by rw [m₁.mem]; exact writeW_outside _ _ _ (by omega_arith)
    refine ⟨(m₁.rest _).trans K, fun x hx => ?_, fun q hq => ?_⟩
    · rw [O x fun q hq => hx q (List.mem_cons_of_mem _ hq), O₁ x (hx p List.mem_cons_self)]
    · rcases List.mem_cons.mp hq with rfl | hq
      · have e : word s'.mem base q.2 = word s₁.mem base q.2 := Mem.readW_congr fun i hi =>
          O _ fun r hr => by
            rw [ofs_off base (by omega_arith)]; have := hp.1 r hr; omega_arith
        rw [e, m₁.mem, word, Mem.readW_writeW_self32]
      · rw [V q hq, m₁.gpr]

/-- Loads of registers (not `r0`) from offsets of the working space. -/
theorem ldrs_ok {s : State} {base : Addr} (hs : Base s base) :
    ∀ (l : List (Reg × Nat)), (∀ p ∈ l, p.2 + 4 ≤ 4096) → (l.map Prod.fst).Nodup → (∀ p ∈ l, p.1 ≠ .r0) →
    WP isa (.block (l.map fun p => ld p.1 p.2)) s fun s' =>
      s'.mem = s.mem ∧ Rest (l.map Prod.fst) s s' ∧ ∀ p ∈ l, s'.gpr p.1 = word s.mem base p.2
  | [], _, _, _ => WP.block_nil ⟨rfl, Rest.refl _ _, fun _ h => absurd h List.not_mem_nil⟩
  | p :: l, hl, hnd, h0 => by
    have hp0 := hl p List.mem_cons_self
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.map_cons]
    refine wp_ldr (by omega_arith) (hs.ea (by omega_arith)) (List.mem_append_right _ hs.wr |> fun h =>
      ⟨_, h, contains_sc (by omega_arith)⟩) fun s₁ u₁ => ?_
    have hs₁ := hs.of_rest (u₁.rest (ws := [p.1]) (by simp)) (by simpa using (h0 p List.mem_cons_self).symm)
    refine WP.mono (ldrs_ok hs₁ l (fun q h => hl q (List.mem_cons_of_mem _ h)) hnd.2
      (fun q h => h0 q (List.mem_cons_of_mem _ h))) fun s' ⟨M, K, V⟩ => ?_
    refine ⟨by rw [M, u₁.mem], ((u₁.rest (by simp)).trans (K.mono fun r hr => by simp [hr])), fun q hq => ?_⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [K.gpr _ hnd.1, u₁.gpr]
    · rw [V q hq, u₁.mem]

/-- The arguments on entry: the working space and the offsets. -/
structure Entry (hasB : Bool) (s : State) (base : Addr) (o a b : Nat) : Prop where
  base : Base s base
  o : (s.gpr .r1).toNat = o
  a : (s.gpr .r2).toNat = a
  b : hasB = true → (s.gpr .r3).toNat = b

theorem ptr_of {s : State} {r : Reg} {x : Nat} {v : BitVec 32} (hr : s.gpr r = s.gpr .r0 + v)
    (hv : v.toNat = x) : s.gpr r = s.gpr .r0 + BitVec.ofNat 32 x := by
  rw [hr, ← hv, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- What the entry leaves. -/
structure Entered (hasB : Bool) (s : State) (base : Addr) (o a b : Nat) (s₁ : State) : Prop where
  scr : Scr s₁ base
  po : Ptr s₁ .r9 o
  pa : Ptr s₁ .lr a
  pb : hasB = true → Ptr s₁ .r12 b
  rest : Rest [.r6, .r9, .lr, .r12] s s₁
  saved : ∀ p ∈ saves, word s₁.mem base p.2 = s.gpr p.1
  mem : ∀ x, (ofs base x < SAVE ∨ SAVE + 24 ≤ ofs base x) → s₁.mem x = s.mem x

theorem entry_ok {hasB : Bool} {s : State} {base : Addr} {o a b : Nat} (h : Entry hasB s base o a b) :
    WP isa (.block (entryFn hasB)) s (Entered hasB s base o a b) := by
  rw [entryFn, saveFn_eq, List.append_assoc, WP.block_append_iff]
  refine WP.mono (strs_ok h.base saves (fun p hp => by have := saves_bound p hp; simp only [SAVE] at this; omega_arith)
    (by decide)) fun s₁ ⟨K₁, O₁, V₁⟩ => ?_
  have hb₁ := h.base.of_rest K₁ (by decide)
  refine wp_movw fun s₂ u₂ => wp_dp (op2_reg _ _) fun s₃ u₃ => wp_dp (op2_reg _ _) fun s₄ u₄ => ?_
  have K₄ : Rest [.r6, .r9, .lr] s s₄ :=
    (K₁.mono (by simp)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans (u₄.rest (by decide))))
  have m₄ : s₄.mem = s₁.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
  have g0 : s₄.gpr .r0 = s.gpr .r0 := K₄.gpr _ (by decide)
  have hb₄ := h.base.of_rest K₄ (by decide)
  have g6 : s₄.gpr .r6 = 65535 := by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]; rfl
  have po : Ptr s₄ .r9 o := by
    refine ptr_of (v := s.gpr .r1) ?_ h.o
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₂.other _ (by decide), K₁.gpr _ (by simp),
      K₁.gpr _ (by simp), g0]
    rfl
  have pa : Ptr s₄ .lr a := by
    refine ptr_of (v := s.gpr .r2) ?_ h.a
    rw [u₄.gpr, u₃.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₂.other _ (by decide), K₁.gpr _ (by simp), K₁.gpr _ (by simp), g0]
    rfl
  have ent : ∀ s', Rest [.r12] s₄ s' → s'.mem = s₁.mem → (hasB = true → Ptr s' .r12 b) →
      Entered hasB s base o a b s' := fun s' K' M' pb =>
    { scr := ⟨by rw [K'.gpr _ (by decide)]; exact hb₄.r0, by rw [K'.gpr _ (by decide)]; exact g6,
        K'.wr ▸ hb₄.wr, by rw [K'.gpr _ (by decide)]; exact hb₄.nowrap⟩
      po := by rw [Ptr, K'.gpr _ (by decide), K'.gpr _ (by decide)]; exact po
      pa := by rw [Ptr, K'.gpr _ (by decide), K'.gpr _ (by decide)]; exact pa
      pb := pb
      rest := (K₄.mono (by simp)).trans (K'.mono (by simp))
      saved := fun p hp => by rw [M']; exact V₁ p hp
      mem := fun x hx => by
        rw [M']
        refine O₁ x fun p hp => ?_
        have := saves_bound p hp
        omega_arith }
  cases hasB with
  | false => exact WP.block_nil (ent s₄ (Rest.refl _ _) m₄ (fun h => absurd h (by decide)))
  | true =>
    refine wp_dp (op2_reg _ _) fun s₅ u₅ => WP.block_nil (ent s₅ (u₅.rest (by decide)) (by rw [u₅.mem, m₄])
      fun _ => ptr_of (v := s.gpr .r3) ?_ (h.b rfl))
    rw [u₅.gpr, u₅.other Reg.r0 (by decide), u₄.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₂.other _ (by decide), K₁.gpr _ (by simp),
      K₁.gpr _ (by simp)]
    rfl

theorem OpMem.word {base : Addr} {o : Nat} {m m' : Mem} (h : OpMem base o m m') {d : Nat}
    (hs : SAVE ≤ d) (ho : o + 112 ≤ d) (hd : d + 4 ≤ 8192) : word m' base d = word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off base (by omega_arith)]; omega_arith)
    (Or.inr (by rw [ofs_off base (by omega_arith)]; omega_arith))).symm).symm

/-- A function: the entry, the operation `op` (which, from the entry's state,
writes `[o]` related to `[a]` and `[b]` by `r`), and the registers restored. -/
theorem fn_ok {hasB : Bool} {op : Prog isa} {r : Nat → Nat → Nat → Prop} {s : State} {base : Addr}
    {o a b : Nat} (h : Entry hasB s base o a b) (ho : Slot o) (ha : Slot a) (hb : Slot b)
    (ab : Bounded s.mem base a) (bb : Bounded s.mem base b)
    (hop : ∀ s₁, Scr s₁ base → Ptr s₁ .r9 o → Ptr s₁ .lr a → (hasB = true → Ptr s₁ .r12 b) →
      Bounded s₁.mem base a → Bounded s₁.mem base b →
      WP isa op s₁ fun t => Keeps (.lr :: fclob) s₁ t ∧ OpMem base o s₁.mem t.mem ∧
        Bounded t.mem base o ∧ r (fe t.mem base o) (fe s₁.mem base a) (fe s₁.mem base b)) :
    WP isa (fn hasB op) s fun t => (∀ q ∈ preserved, t.gpr q = s.gpr q) ∧ t.gpr .r0 = s.gpr .r0 ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ FieldMem base o s.mem t.mem ∧ Bounded t.mem base o ∧
      r (fe t.mem base o) (fe s.mem base a) (fe s.mem base b) := by
  have ho' : o + 112 ≤ 3584 := ho
  have ha' : a + 112 ≤ 3584 := ha
  have hb' : b + 112 ≤ 3584 := hb
  rw [fn, WP.seq_iff]
  refine WP.mono (entry_ok h) fun s₁ E => ?_
  have O₁ : Outside base SAVE 24 s.mem s₁.mem := E.mem
  have ea : ∀ {d : Nat}, d + 112 ≤ 3584 → ∀ i < 28, limbs s₁.mem base d i = limbs s.mem base d i :=
    fun hd _ hi => O₁.limbs (Or.inl (by simp only [SAVE]; omega_arith)) (by omega_arith) hi
  have fa : ∀ {d : Nat}, d + 112 ≤ 3584 → fe s₁.mem base d = fe s.mem base d :=
    fun hd => valN_congr fun _ hi => ea hd _ hi
  rw [WP.seq_iff]
  refine WP.mono (hop s₁ E.scr E.po E.pa E.pb (fun i hi => by rw [ea ha' i hi]; exact ab i hi)
    (fun i hi => by rw [ea hb' i hi]; exact bb i hi)) fun s₂ ⟨K₂, M₂, B₂, R₂⟩ => ?_
  have hb₂ : Base s₂ base :=
    let hs₂ := E.scr.of_keeps K₂ (by decide)
    ⟨hs₂.r0, hs₂.wr, hs₂.nowrap⟩
  rw [restoreFn_eq]
  refine WP.mono (ldrs_ok hb₂ saves (fun p hp => by have := saves_bound p hp; simp only [SAVE] at this; omega_arith)
    (by decide) (by decide)) fun s₃ ⟨M₃, K₃, V₃⟩ => ?_
  have sv : ∀ p ∈ saves, s₃.gpr p.1 = s.gpr p.1 := fun p hp => by
    have := saves_bound p hp
    rw [V₃ p hp, M₂.word this.1 (by simp only [SAVE] at this ⊢; omega_arith) (by simp only [SAVE] at this; omega_arith),
      E.saved p hp]
  have kept : ∀ q, q ∉ [.r4, .r5, .r6, .r7, .r9, .lr, .r12, .r1, .r2, .r3] → s₃.gpr q = s.gpr q :=
    fun q hq => by
      rw [K₃.gpr _ (by simp only [saves, List.map]; simp_all), K₂.1 _ (by simp only [fclob]; simp_all),
        E.rest.gpr _ (by simp_all)]
  refine ⟨fun q hq => ?_, kept _ (by decide), by rw [K₃.rd, K₂.2.1, E.rest.rd],
    by rw [K₃.wr, K₂.2.2, E.rest.wr], ?_, fun i hi => by rw [M₃]; exact B₂ i hi, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sv (.r4, SAVE) (by decide)
    · exact sv (.r5, SAVE + 4) (by decide)
    · exact sv (.r6, SAVE + 8) (by decide)
    · exact sv (.r7, SAVE + 12) (by decide)
    · exact kept _ (by decide)
    · exact sv (.r9, SAVE + 16) (by decide)
    · exact kept _ (by decide)
    · exact kept _ (by decide)
    · exact sv (.lr, SAVE + 20) (by decide)
  · rw [M₃]
    exact (FieldMem.work O₁ (by decide) (by decide)).trans M₂.field
  · rw [M₃, fa ha', fa hb'] at *
    exact R₂

end VG.Proof.X448.Arm

end

end

/-! ### `X448.Arm.Mul`, which only this module used -/

section

/-! ### `X448.Arm.Reduce`, which only this module used -/

section

/-!
# X448 on ARMv7: reducing product limbs

The upper half folds using `2^448 = 2^224 + 1` modulo the field prime.
-/

@[expose] public section

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.X25519.Arm (wp_dp op2_reg)

theorem loadAdd_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 4 ≤ 4096) :
    WP isa (.block [ld .r2 d, .dp .add .r3 .r3 (.reg .r2)]) s fun t =>
      t.gpr .r3 = s.gpr .r3 + word s.mem base d ∧ t.mem = s.mem ∧ Keeps [.r3, .r2] s t := by
  refine load_ok hs hd fun t ht => wp_dp (op2_reg _ _) fun u hu => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [hu.gpr]
    change t.gpr .r3 + t.gpr .r2 = _
    rw [ht.other .r3 (by decide), ht.gpr]
  · exact hu.mem.trans ht.mem
  · exact rest_keeps ((ht.rest (by decide)).trans (hu.rest (by decide)))

/-- A bounded sum of words, accumulated into `r3`. -/
def addWords (ds : List Nat) : List Instr :=
  ds.flatMap fun d => [ld .r2 d, .dp .add .r3 .r3 (.reg .r2)]

theorem addWords_ok {s : State} {base : Addr} (hs : Scr s base) {ds : List Nat}
    (hd : ∀ d ∈ ds, d + 4 ≤ 4096) :
    WP isa (.block (addWords ds)) s fun t =>
      t.gpr .r3 = s.gpr .r3 + (ds.map fun d => word s.mem base d).sum ∧
      t.mem = s.mem ∧ Keeps [.r3, .r2] s t := by
  induction ds generalizing s with
  | nil => exact WP.block_nil ⟨(BitVec.add_zero _).symm, rfl, Keeps.refl _ _⟩
  | cons d ds ih =>
    change WP isa (.block (([ld .r2 d, .dp .add .r3 .r3 (.reg .r2)] : List Instr) ++ addWords ds)) s _
    rw [WP.block_append_iff]
    refine WP.mono (loadAdd_ok hs (hd d List.mem_cons_self)) fun t ⟨tv, tm, tk⟩ => ?_
    refine WP.mono (ih (hs.of_keeps tk (by decide)) (fun d h => hd d (List.mem_cons_of_mem _ h)))
      fun u ⟨uv, um, uk⟩ => ⟨?_, um.trans tm, tk.trans uk⟩
    rw [uv, tv, tm]
    simp only [List.map_cons, List.sum_cons, BitVec.add_assoc]

/-- The extra offsets folded into product limb `k`. -/
def colOffsets (k : Nat) : List Nat :=
  [ACC + 4 * (k + 28)] ++
    if k < 14 then [ACC + 4 * (k + 42)] else [ACC + 4 * (k + 14), ACC + 4 * (k + 28)]

theorem colOffsets_bound {k : Nat} (hk : k < 28) : ∀ d ∈ colOffsets k, d + 4 ≤ 4096 := by
  intro d hd
  simp only [colOffsets, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | hd
  · simp only [ACC]; omega_using [hk]
  · split at hd <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    · subst d; simp only [ACC]; omega_using [hk]
    · rcases hd with rfl | rfl <;> simp only [ACC] <;> omega_using [hk]

theorem reduceCol_code (k : Nat) : reduceCol k =
    [ld .r3 (ACC + 4 * k)] ++ addWords (colOffsets k) ++ [st .r3 (TMP + 4 * k)] := by
  unfold reduceCol colOffsets
  split <;> rfl

theorem reduceCol_ok {s : State} {base : Addr} (hs : Scr s base) {k : Nat} (hk : k < 28)
    {f : Nat → Nat} (hf : ∀ i < 56, limbs s.mem base ACC i = f i)
    (hb : ∀ i < 56, f i < radix) :
    WP isa (.block (reduceCol k)) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 4 * k)) (BitVec.ofNat 32 (reduced f k)) ∧
      Keeps [.r3, .r2] s t := by
  rw [reduceCol_code, List.append_assoc]
  refine load_ok hs (by simp only [ACC]; omega_using [hk]) fun t ht => ?_
  change WP isa (.block (addWords (colOffsets k) ++ ([st .r3 (TMP + 4 * k)] : List Instr))) t _
  rw [WP.block_append_iff]
  refine WP.mono (addWords_ok (hs.of_upd ht (by decide) (by decide)) (colOffsets_bound hk))
    fun u ⟨uv, um, uk⟩ => ?_
  have us := (hs.of_upd ht (by decide) (by decide)).of_keeps uk (by decide)
  refine store_ok us (by simp only [TMP]; omega_using [hk]) fun v hv => WP.block_nil ⟨?_, ?_⟩
  · rw [hv.mem, um, ht.mem, uv, ht.gpr, ht.mem]
    apply congrArg (s.mem.writeW _)
    apply BitVec.eq_of_toNat_eq
    have f0 := hf k (by omega_using [hk])
    have f1 := hf (k + 28) (by omega_using [hk])
    have b0 := hb k (by omega_using [hk])
    have b1 := hb (k + 28) (by omega_using [hk])
    by_cases h : k < 14
    · have f2 := hf (k + 42) (by omega_using [h])
      have b2 := hb (k + 42) (by omega_using [h])
      simp only [colOffsets, h, ite_true, List.cons_append, List.nil_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, reduced, h, ite_true]
      change (limbs s.mem base ACC k + (limbs s.mem base ACC (k + 28) +
        (limbs s.mem base ACC (k + 42)) % 2 ^ 32) % 2 ^ 32) % 2 ^ 32 = _
      rw [f0, f1, f2]
      simp only [radix] at b0 b1 b2
      omega_using []
    · have f2 := hf (k + 14) (by omega_using [hk])
      have b2 := hb (k + 14) (by omega_using [hk])
      simp only [colOffsets, h, ite_false, List.cons_append, List.nil_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, reduced, h, ite_false]
      change (limbs s.mem base ACC k + (limbs s.mem base ACC (k + 28) +
        (limbs s.mem base ACC (k + 14) + (limbs s.mem base ACC (k + 28)) % 2 ^ 32) % 2 ^ 32) % 2 ^ 32) % 2 ^ 32 = _
      rw [f0, f1, f2]
      simp only [radix] at b0 b1 b2
      omega_using []
  · exact (rest_keeps (ht.rest (by decide))).trans (uk.trans (rest_keeps (hv.rest _)))

/-- Fold all fifty-six product limbs into twenty-eight, ready for carries. -/
theorem reduce_ok {s : State} {base : Addr} (hs : Scr s base) {f : Nat → Nat}
    (hf : ∀ i < 56, limbs s.mem base ACC i = f i) (hb : ∀ i < 56, f i < radix) :
    WP isa (.block ((List.range 28).flatMap reduceCol)) s fun t =>
      (∀ i < 28, limbs t.mem base TMP i = reduced f i) ∧
      Outside base TMP 112 s.mem t.mem ∧ Keeps [.r3, .r2] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base TMP i = reduced f i) ∧
    Outside base TMP 112 s.mem t.mem ∧ Keeps [.r3, .r2] s t
  have step : ∀ n t, n < 28 → inv n t → WP isa (.block (reduceCol n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have ft : ∀ i < 56, limbs t.mem base ACC i = f i := by
      intro i hi
      change (word t.mem base (ACC + 4 * i)).toNat = _
      rw [tm.word (Or.inl (by simp only [ACC, TMP]; omega_using [hi])) (by simp only [ACC]; omega_using [hi])]
      exact hf i hi
    refine WP.mono (reduceCol_ok (hs.of_keeps tk (by decide)) hn ft hb) fun u ⟨um, uk⟩ => ?_
    have out : Outside base (TMP + 4 * n) 4 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by simp only [TMP]; omega_using [hn])
    refine ⟨?_, tm.trans (out.mono (by omega_using []) (by omega_using [hn])), tk.trans uk⟩
    intro i hi
    change (word u.mem base (TMP + 4 * i)).toNat = _
    rw [um, word_write t.mem base (by simp only [TMP]; omega_using [hn]) (by simp only [TMP]; omega_using [hn, hi])]
    by_cases h : i = n
    · rw [ite_eq_left h, h, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (reduced_bound hb n hn) (by decide))]
    · rw [ite_eq_right h]; exact tf i (by omega_using [hi, h])
  exact wp_range_flatMap (M := isa) (N := 28) inv step 28 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.Arm

end

end


/-!
# X448 on ARMv7: field multiplication

The row loop produces the 56 limbs of the product, which are folded and
normalized modulo the prime.
-/

@[expose] public section

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16

theorem frame_outside {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Frame [⟨off base o, n⟩] m m') (hn : o + n ≤ 8192) : Outside base o n m m' := by
  intro x hx
  refine h x fun r hr hc => ?_
  rw [List.mem_singleton.mp hr] at hc
  change (x - off base o).toNat + 1 ≤ n at hc
  simp only [off] at hc
  have hi := (Offset.lt_iff x base (d := o) (n := n) (by omega_using [hn])).mp (by omega_using [hc])
  simp only [ofs] at hx
  omega_using [hx, hi]

/-- `[r9] = [lr] [r12]`, for `r9`, `lr` and `r12` at `o`, `a` and `b`. -/
theorem mul_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (hpo : Ptr s .r9 o) (hpa : Ptr s .lr a) (hpb : Ptr s .r12 b)
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa Impl.X448.Arm.mul s fun t =>
      Keeps (.lr :: fclob) s t ∧ OpMem base o s.mem t.mem ∧ Bounded t.mem base o ∧
        fe t.mem base o % Spec.X448.P = fe s.mem base a * fe s.mem base b % Spec.X448.P := by
  let ptr := s.gpr .r0
  have pe : State.addr ptr = base := hs.r0
  have ctx : RowCtx ptr s := ⟨rfl, by change (s.gpr .r0).toNat + 4096 ≤ 2 ^ 32; have := hs.nowrap; omega_using [this],
    by rw [pe]; exact hs.wr⟩
  rw [Impl.X448.Arm.mul, WP.seq_iff]
  refine WP.mono (mulPreF_ok (x := a) (y := b) ctx hs.mask hpa hpb) fun t ht => ?_
  rw [WP.seq_iff]
  refine WP.mono (mulLoopF_ok ha hb (by rw [pe]; exact ab) (by rw [pe]; exact bb) ht) fun u hu => ?_
  have uk : Keeps (.lr :: fclob) s u := rest_keeps hu.rest
  have us := hs.of_keeps uk (by decide)
  let f := limbs u.mem base ACC
  have fb : ∀ i < 56, f i < radix := by
    intro i hi
    have := hu.lt i hi
    rw [pe] at this
    exact this
  have fv : valN f 56 = fe s.mem base a * fe s.mem base b := by
    have := hu.val
    rw [pe] at this
    exact this
  have um : Outside base ACC 224 s.mem u.mem := by
    have hf := hu.frame
    rw [pe] at hf
    exact frame_outside hf (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok us (fun _ _ => rfl) fb) fun v ⟨vf, vm, vk⟩ => ?_
  have vs := us.of_keeps vk (by decide)
  have vp : Ptr v .r9 o := (hpo.of_keeps uk (by decide) (by decide)).of_keeps vk (by decide) (by decide)
  refine WP.mono (normalize_ok vs vp ho vf (reduced_bound fb)) fun w ⟨wf, wm, wk⟩ => ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact uk.trans ((vk.mono (by decide)).trans (wk.mono (by decide)))
  · exact (OpMem.work um (by decide) (by decide)).trans ((OpMem.work vm (by decide) (by decide)).trans wm)
  · intro i hi
    rw [wf i hi]
    exact digit_lt _ _
  · rw [show fe w.mem base o = valN (normalized (reduced f)) 28 from valN_congr wf,
      normalized_mod (reduced_bound fb), reduced_mod, fv]

end VG.Proof.X448.Arm

end

end

/-! ### `X448.Arm.Small`, which only this module used -/

section

/-!
# X448 on ARMv7: multiplication by a24

The 16-bit limbs keep multiplication by 39081 within a 32-bit word.
-/

@[expose] public section

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.X25519.Arm (wp_mul wp_movw)

theorem smallStep_ok {s : State} {base : Addr} (hs : Scr s base) {a i : Nat}
    (hpa : Ptr s .lr a) (ha : Slot a) (hi : i < 28) (hc : (s.gpr .r5).toNat = 39081) :
    WP isa (.block [.ldr .r3 .lr (4 * i), .mul .r3 .r3 .r5, st .r3 (TMP + 4 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 4 * i)) (BitVec.ofNat 32 (39081 * limbs s.mem base a i)) ∧
      Keeps [.r3, .r2] s t := by
  have ha' : a + 112 ≤ 3584 := ha
  refine loadP_ok hs hpa (by omega_using [hi]) (by omega_using [hi, ha']) fun t ht => ?_
  have ts := hs.of_upd ht (by decide) (by decide)
  refine wp_mul fun u hu => ?_
  have us := ts.of_upd hu (by decide) (by decide)
  refine store_ok us (by simp only [TMP]; omega_using [hi]) fun v hv => WP.block_nil ⟨?_, ?_⟩
  · rw [hv.mem, hu.mem, ht.mem, hu.gpr, ht.gpr, ht.other .r5 (by decide)]
    apply congrArg (s.mem.writeW _)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, hc, Nat.mul_comm _ 39081, BitVec.toNat_ofNat]
  · exact rest_keeps ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans (hv.rest _)))

theorem smallInit_ok (s : State) :
    WP isa (.block [.movw .r5 39081]) s fun t =>
      (t.gpr .r5).toNat = 39081 ∧ t.mem = s.mem ∧ Keeps [.r5] s t := by
  refine wp_movw fun t ht => WP.block_nil ⟨?_, ht.mem, rest_keeps (ht.rest (by decide))⟩
  rw [ht.gpr]
  rfl

theorem mulSmall_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (hpo : Ptr s .r9 o) (hpa : Ptr s .lr a) (ho : Slot o) (ha : Slot a) (ab : Bounded s.mem base a) :
    WP isa (.block mulSmall) s fun t =>
      Keeps fclob s t ∧ OpMem base o s.mem t.mem ∧ Bounded t.mem base o ∧
        fe t.mem base o % Spec.X448.P = 39081 * fe s.mem base a % Spec.X448.P := by
  let f := fun i => 39081 * limbs s.mem base a i
  have fb : ∀ i < 28, f i ≤ 2 ^ 32 - radix := by
    intro i hi
    have h := Nat.mul_le_mul_left 39081 (Nat.le_of_lt (ab i hi))
    have hr : 39081 * radix ≤ 2 ^ 32 - radix := by decide
    exact Nat.le_trans h hr
  refine WP.mono (columns_normalize hs hpo ho fb ?_) fun t ⟨tk, tm, tb, tv⟩ => ⟨tk, tm, tb, ?_⟩
  · rw [WP.block_append_iff]
    refine WP.mono (smallInit_ok s) fun t ⟨tc, tm, tk⟩ => ?_
    have ts := hs.of_keeps tk (by decide)
    refine WP.mono (columns_ok ts (by decide : Reg.r0 ∉ [Reg.r3, Reg.r2] ∧ Reg.r6 ∉ [Reg.r3, Reg.r2]) fb ?_) fun u ⟨uf, um, uk⟩ => ?_
    · intro i hi u us um uk
      have uc : (u.gpr .r5).toNat = 39081 := by rw [uk.1 _ (by decide), tc]
      refine WP.mono (smallStep_ok us ((hpa.of_keeps tk (by decide) (by decide)).of_keeps uk
        (by decide) (by decide)) ha hi uc) fun v ⟨vm, vk⟩ => ⟨?_, vk⟩
      rw [input_limb um ha hi, tm] at vm
      exact vm
    · refine ⟨uf, ?_, (tk.mono ?_).trans (uk.mono ?_)⟩
      · rw [← tm]; exact um
      · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> decide
  · rw [tv, valN_scale]

end VG.Proof.X448.Arm

end

end

/-! ### `X448.Arm.AddSub`, which only this module used -/

section

/-!
# X448 on ARMv7: addition and subtraction

Twice the prime is added before subtraction, so no limb subtraction borrows.
-/

@[expose] public section

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.X25519.Arm (wp_dp wp_movw op2_reg op2_imm)

theorem addStep_ok {s : State} {base : Addr} (hs : Scr s base) {a b i : Nat}
    (hpa : Ptr s .lr a) (hpb : Ptr s .r12 b) (ha : Slot a) (hb : Slot b) (hi : i < 28) :
    WP isa (.block [.ldr .r3 .lr (4 * i), .ldr .r2 .r12 (4 * i),
      .dp .add .r3 .r3 (.reg .r2), st .r3 (TMP + 4 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 4 * i))
        (BitVec.ofNat 32 (limbs s.mem base a i + limbs s.mem base b i)) ∧ Keeps fclob s t := by
  have ha' : a + 112 ≤ 3584 := ha
  have hb' : b + 112 ≤ 3584 := hb
  refine loadP_ok hs hpa (by omega_using [hi]) (by omega_using [hi, ha']) fun t ht => ?_
  have ts := hs.of_upd ht (by decide) (by decide)
  refine loadP_ok ts (hpb.of_upd ht (by decide) (by decide)) (by omega_using [hi]) (by omega_using [hi, hb']) fun u hu => ?_
  have us := ts.of_upd hu (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun v hv => ?_
  have vs := us.of_upd hv (by decide) (by decide)
  refine store_ok vs (by simp only [TMP]; omega_using [hi]) fun w hw => WP.block_nil ⟨?_, ?_⟩
  · rw [hw.mem, hv.mem, hu.mem, ht.mem, hv.gpr]
    change s.mem.writeW _ (u.gpr .r3 + u.gpr .r2) = _
    rw [hu.other .r3 (by decide), ht.gpr, hu.gpr, ht.mem]
    apply congrArg (s.mem.writeW _)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  · exact rest_keeps ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans
      ((hv.rest (by decide)).trans (hw.rest _))))

theorem subK_nat (i : Nat) : ((subK i).setWidth 32 + (65536 : BitVec 32)).toNat = bias i := by
  by_cases h : i = 14 <;> simp only [subK, bias, h, ite_true, ite_false] <;> decide

theorem subStep_ok {s : State} {base : Addr} (hs : Scr s base) {a b i : Nat}
    (hpa : Ptr s .lr a) (hpb : Ptr s .r12 b) (ha : Slot a) (hb : Slot b) (hi : i < 28)
    (ab : limbs s.mem base a i < radix) (bb : limbs s.mem base b i < radix) :
    WP isa (.block [.ldr .r3 .lr (4 * i), .movw .r2 (subK i), .dp .add .r2 .r2 (.imm 65536),
      .dp .add .r3 .r3 (.reg .r2), .ldr .r2 .r12 (4 * i), .dp .sub .r3 .r3 (.reg .r2),
      st .r3 (TMP + 4 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 4 * i))
        (BitVec.ofNat 32 (difference (limbs s.mem base a) (limbs s.mem base b) i)) ∧ Keeps fclob s t := by
  have ha' : a + 112 ≤ 3584 := ha
  have hb' : b + 112 ≤ 3584 := hb
  refine loadP_ok hs hpa (by omega) (by omega) fun s1 h1 => ?_
  have hs1 := hs.of_upd h1 (by decide) (by decide)
  refine wp_movw fun s2 h2 => ?_
  have hs2 := hs1.of_upd h2 (by decide) (by decide)
  refine wp_dp (op2_imm (by decide)) fun s3 h3 => ?_
  have hs3 := hs2.of_upd h3 (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun s4 h4 => ?_
  have hs4 := hs3.of_upd h4 (by decide) (by decide)
  have hpb4 : Ptr s4 .r12 b := (((hpb.of_upd h1 (by decide) (by decide)).of_upd h2 (by decide)
    (by decide)).of_upd h3 (by decide) (by decide)).of_upd h4 (by decide) (by decide)
  refine loadP_ok hs4 hpb4 (by omega) (by omega) fun s5 h5 => ?_
  have hs5 := hs4.of_upd h5 (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun s6 h6 => ?_
  have hs6 := hs5.of_upd h6 (by decide) (by decide)
  refine store_ok hs6 (by simp only [TMP]; omega) fun s7 h7 => WP.block_nil ⟨?_, ?_⟩
  · rw [h7.mem, h6.mem, h5.mem, h4.mem, h3.mem, h2.mem, h1.mem, h6.gpr]
    change s.mem.writeW _ (s5.gpr .r3 - s5.gpr .r2) = _
    rw [h5.other .r3 (by decide), h4.gpr, h5.gpr, h4.mem, h3.mem, h2.mem, h1.mem]
    change s.mem.writeW _ (s3.gpr .r3 + s3.gpr .r2 - word s.mem base (b + 4 * i)) = _
    rw [h3.other .r3 (by decide), h2.other .r3 (by decide), h1.gpr, h3.gpr]
    change s.mem.writeW _ (word s.mem base (a + 4 * i) + (s2.gpr .r2 + 65536) - _) = _
    rw [h2.gpr]
    apply congrArg (s.mem.writeW _)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_add, subK_nat, BitVec.toNat_ofNat]
    change (2 ^ 32 - limbs s.mem base b i + (limbs s.mem base a i + bias i) % 2 ^ 32) % 2 ^ 32 =
      (limbs s.mem base a i + bias i - limbs s.mem base b i) % 2 ^ 32
    have h := bias_bound i
    simp only [radix] at ab bb h
    omega
  · exact rest_keeps ((h1.rest (by decide)).trans ((h2.rest (by decide)).trans
      ((h3.rest (by decide)).trans ((h4.rest (by decide)).trans ((h5.rest (by decide)).trans
      ((h6.rest (by decide)).trans (h7.rest _)))))))

theorem add_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (hpo : Ptr s .r9 o) (hpa : Ptr s .lr a) (hpb : Ptr s .r12 b)
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (.block Impl.X448.Arm.add) s fun t =>
      Keeps fclob s t ∧ OpMem base o s.mem t.mem ∧ Bounded t.mem base o ∧
        fe t.mem base o % Spec.X448.P = (fe s.mem base a + fe s.mem base b) % Spec.X448.P := by
  let f := fun i => limbs s.mem base a i + limbs s.mem base b i
  have fb : ∀ i < 28, f i ≤ 2 ^ 32 - radix := by
    intro i hi
    have h1 := ab i hi
    have h2 := bb i hi
    change limbs s.mem base a i + limbs s.mem base b i ≤ _
    simp only [radix] at h1 h2 ⊢
    omega_using [h1, h2]
  refine WP.mono (columns_normalize hs hpo ho fb (columns_ok hs (by decide : .r0 ∉ fclob ∧ .r6 ∉ fclob) fb ?_))
    fun t ⟨tk, tm, tb, tv⟩ => ⟨tk, tm, tb, ?_⟩
  · intro i hi t ts tm tk
    refine WP.mono (addStep_ok ts (hpa.of_keeps tk (by decide) (by decide))
      (hpb.of_keeps tk (by decide) (by decide)) ha hb hi) fun u ⟨um, uk⟩ => ⟨?_, uk⟩
    rw [input_limb tm ha hi, input_limb tm hb hi] at um
    exact um
  · rw [tv, valN_add]

theorem sub_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (hpo : Ptr s .r9 o) (hpa : Ptr s .lr a) (hpb : Ptr s .r12 b)
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (.block Impl.X448.Arm.sub) s fun t =>
      Keeps fclob s t ∧ OpMem base o s.mem t.mem ∧ Bounded t.mem base o ∧
        (fe t.mem base o + fe s.mem base b) % Spec.X448.P = fe s.mem base a % Spec.X448.P := by
  let f := difference (limbs s.mem base a) (limbs s.mem base b)
  have fb : ∀ i < 28, f i ≤ 2 ^ 32 - radix := fun i hi => Nat.le_of_lt (difference_bound ab i hi)
  refine WP.mono (columns_normalize hs hpo ho fb (columns_ok hs (by decide : .r0 ∉ fclob ∧ .r6 ∉ fclob) fb ?_))
    fun t ⟨tk, tm, tb, tv⟩ => ⟨tk, tm, tb, ?_⟩
  · intro i hi t ts tm tk
    have ea := input_limb tm ha hi
    have eb := input_limb tm hb hi
    refine WP.mono (subStep_ok ts (hpa.of_keeps tk (by decide) (by decide))
      (hpb.of_keeps tk (by decide) (by decide)) ha hb hi (ea ▸ ab i hi) (eb ▸ bb i hi))
      fun u ⟨um, uk⟩ => ⟨?_, uk⟩
    simp only [difference, ea, eb] at um
    exact um
  · rw [Nat.add_mod, tv, ← Nat.add_mod, difference_val bb, Nat.add_mul_mod_self_right]

end VG.Proof.X448.Arm

end

end


/-!
# X448 on ARMv7: calls of the field functions

`mulFn_ok`, `addFn_ok`, `subFn_ok` and `mulA24Fn_ok` are what the field
functions do (`fn_ok` with their operations). A field operation of the
callers is a call (`Op.code`): the offsets are moved into `r1`–`r3` and
the function is called on the working space at `r0` (`callFn_ok`,
`mulA24Call_ok`); the call changes only the registers `clob` and the memory
`FieldMem` allows (`Op`), as the operations did when they were inlined.
-/

@[expose] public section

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.X25519.Arm (Rest Upd wp_movw)

/-- What a function does, from its entry, for the relation `r` of the result
and the operands. -/
abbrev FnPost (s : State) (base : Addr) (o a b : Nat) (r : Nat → Nat → Nat → Prop) (t : State) : Prop :=
  (∀ q ∈ preserved, t.gpr q = s.gpr q) ∧ t.gpr .r0 = s.gpr .r0 ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    FieldMem base o s.mem t.mem ∧ Bounded t.mem base o ∧ r (fe t.mem base o) (fe s.mem base a) (fe s.mem base b)

abbrev mulRel (x y z : Nat) : Prop := x % Spec.X448.P = y * z % Spec.X448.P
abbrev addRel (x y z : Nat) : Prop := x % Spec.X448.P = (y + z) % Spec.X448.P
abbrev subRel (x y z : Nat) : Prop := (x + z) % Spec.X448.P = y % Spec.X448.P
abbrev a24Rel (x y _ : Nat) : Prop := x % Spec.X448.P = 39081 * y % Spec.X448.P

theorem mulFn_ok {s : State} {base : Addr} {o a b : Nat} (h : Entry true s base o a b)
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa mulFn s (FnPost s base o a b mulRel) :=
  fn_ok h ho ha hb ab bb fun _ hs po pa pb a₁ b₁ => mul_ok hs po pa (pb rfl) ho ha hb a₁ b₁

theorem addFn_ok {s : State} {base : Addr} {o a b : Nat} (h : Entry true s base o a b)
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa addFn s (FnPost s base o a b addRel) :=
  fn_ok h ho ha hb ab bb fun _ hs po pa pb a₁ b₁ => WP.mono (add_ok hs po pa (pb rfl) ho ha hb a₁ b₁)
    fun _ ⟨k, m, bo, v⟩ => ⟨k.mono fun _ h => List.mem_cons_of_mem _ h, m, bo, v⟩

theorem subFn_ok {s : State} {base : Addr} {o a b : Nat} (h : Entry true s base o a b)
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa subFn s (FnPost s base o a b subRel) :=
  fn_ok h ho ha hb ab bb fun _ hs po pa pb a₁ b₁ => WP.mono (sub_ok hs po pa (pb rfl) ho ha hb a₁ b₁)
    fun _ ⟨k, m, bo, v⟩ => ⟨k.mono fun _ h => List.mem_cons_of_mem _ h, m, bo, v⟩

theorem mulA24Fn_ok {s : State} {base : Addr} {o a : Nat} (h : Entry false s base o a a)
    (ho : Slot o) (ha : Slot a) (ab : Bounded s.mem base a) :
    WP isa mulA24Fn s (FnPost s base o a a a24Rel) :=
  fn_ok h ho ha ha ab ab fun _ hs po pa _ a₁ _ => WP.mono (mulSmall_ok hs po pa ho ha a₁)
    fun _ ⟨k, m, bo, v⟩ => ⟨k.mono fun _ h => List.mem_cons_of_mem _ h, m, bo, v⟩

/-- The working space a call narrows the regions to. -/
abbrev wsRegion (base : Addr) : Region := ⟨base, 8192⟩

theorem movw_toNat {x : Nat} (h : x < 65536) : ((BitVec.ofNat 16 x).setWidth 32).toNat = x := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_arith

/-- A call of `body` after the arguments are set (`r1`–`r3` changed, `pre`
holding on the entry), as a field operation. -/
theorem call_ok {f : String} {body : Prog isa} (hn : body.noCalls = true) {s : State} {base : Addr}
    (hs : Scr s base) {o a b : Nat} {hasB : Bool} {r : Nat → Nat → Nat → Prop}
    (hbody : ∀ t, Entry hasB t base o a b → Bounded t.mem base a → Bounded t.mem base b →
      WP isa body t (FnPost t base o a b r))
    {s₃ : State} (k₃ : Rest [.r1, .r2, .r3] s s₃) (m₃ : s₃.mem = s.mem)
    (h1 : (s₃.gpr .r1).toNat = o) (h2 : (s₃.gpr .r2).toNat = a) (h3 : hasB = true → (s₃.gpr .r3).toNat = b)
    (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (.call f body) s₃ fun t => Op base o s t ∧ Bounded t.mem base o ∧
      r (fe t.mem base o) (fe s.mem base a) (fe s.mem base b) := by
  have hs₃ : Scr s₃ base := hs.of_keeps ⟨k₃.gpr, k₃.rd, k₃.wr⟩ (by decide)
  have g : ∀ q, q ∉ VG.Arm.linkRegs → (s₃.callEntry.withRegions [] [wsRegion base]).gpr q = s₃.gpr q :=
    fun q hq => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  refine WP.call (k := ⟨fun t => t.rd = [] ∧ t.wr = [wsRegion base] ∧ Entry hasB t base o a b ∧
      Bounded t.mem base a ∧ Bounded t.mem base b,
      fun t t' => t'.gpr .r0 = t.gpr .r0 ∧ FieldMem base o t.mem t'.mem ∧ Bounded t'.mem base o ∧
        r (fe t'.mem base o) (fe t.mem base a) (fe t.mem base b), fun _ _ => True⟩)
    (fun t ⟨_, _, he, ha', hb'⟩ => by
      obtain ⟨tr, t', hx, P, R0, _, _, M, B, V⟩ := hbody t he ha' hb'
      exact ⟨tr, t', hx, ⟨P, Exec.sp hx⟩, R0, M, B, V⟩)
    (rd := []) (wr := [wsRegion base])
    ⟨rfl, rfl, ⟨⟨by rw [g _ (by decide)]; exact hs₃.r0, List.mem_singleton_self _,
        by rw [g _ (by decide)]; exact hs₃.nowrap⟩,
      by rw [g _ (by decide)]; exact h1, by rw [g _ (by decide)]; exact h2,
      fun hb => by rw [g _ (by decide)]; exact h3 hb⟩,
      by rw [State.withRegions_mem, State.callEntry_mem, m₃]; exact ab,
      by rw [State.withRegions_mem, State.callEntry_mem, m₃]; exact bb⟩
    (Covers.right (Covers.of_mem fun _ hr => by rw [List.mem_singleton.mp hr]; exact hs₃.wr))
    (Covers.of_mem fun _ hr => by rw [List.mem_singleton.mp hr]; exact hs₃.wr)
    ?_ hn
  intro t rd wr _ _ P _ ⟨R0, M, B, V⟩
  simp only [State.withRegions_mem, State.callEntry_mem, m₃, State.withRegions_gpr] at R0 M B V
  rw [State.callEntry_gpr _ (by decide)] at R0
  refine ⟨⟨⟨fun q hq => ?_, by rw [rd, k₃.rd], by rw [wr, k₃.wr]⟩, M⟩, B, V⟩
  simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  obtain ⟨n1, n2, n3, n4, n5, n7, n12, nlr⟩ := hq
  by_cases h0 : q = .r0
  · subst h0; rw [R0, k₃.gpr _ (by decide)]
  · have hp : q ∈ preserved := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false]
      cases q <;> simp_all
    rw [P q hp nlr, k₃.gpr _ (by simp [n1, n2, n3])]

theorem callFn_ok {f : String} {body : Prog isa} (hn : body.noCalls = true) {s : State} {base : Addr}
    (hs : Scr s base) {o a b : Nat} {r : Nat → Nat → Nat → Prop}
    (hbody : ∀ t, Entry true t base o a b → Bounded t.mem base a → Bounded t.mem base b →
      WP isa body t (FnPost t base o a b r))
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (callFn f body o a b) s fun t => Op base o s t ∧ Bounded t.mem base o ∧
      r (fe t.mem base o) (fe s.mem base a) (fe s.mem base b) := by
  have ho' : o + 112 ≤ 3584 := ho
  have ha' : a + 112 ≤ 3584 := ha
  have hb' : b + 112 ≤ 3584 := hb
  rw [callFn, WP.seq_iff]
  refine wp_movw fun s₁ u₁ => wp_movw fun s₂ u₂ => wp_movw fun s₃ u₃ => WP.block_nil ?_
  exact call_ok hn hs hbody ((u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (u₃.rest (by decide))))
    (by rw [u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, movw_toNat (by omega_arith)])
    (by rw [u₃.other _ (by decide), u₂.gpr, movw_toNat (by omega_arith)])
    (fun _ => by rw [u₃.gpr, movw_toNat (by omega_arith)]) ab bb

theorem mulA24Call_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : Slot o) (ha : Slot a) (ab : Bounded s.mem base a) :
    WP isa (mulA24Call o a) s fun t => Op base o s t ∧ Bounded t.mem base o ∧
      a24Rel (fe t.mem base o) (fe s.mem base a) (fe s.mem base a) := by
  have ho' : o + 112 ≤ 3584 := ho
  have ha' : a + 112 ≤ 3584 := ha
  rw [mulA24Call, WP.seq_iff]
  refine wp_movw fun s₁ u₁ => wp_movw fun s₂ u₂ => WP.block_nil ?_
  exact call_ok (by decide +kernel) hs (hasB := false) (b := a)
    (fun t he ha' _ => mulA24Fn_ok he ho ha ha')
    ((u₁.rest (by decide)).trans (u₂.rest (by decide))) (by rw [u₂.mem, u₁.mem])
    (by rw [u₂.other _ (by decide), u₁.gpr, movw_toNat (by omega_arith)])
    (by rw [u₂.gpr, movw_toNat (by omega_arith)]) (fun h => absurd h (by decide)) ab ab

/-- `[o] = [a] [b]`, by a call of `vg_gf448_r16_mul`. -/
theorem mulCall_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (Op.code (.mul o a b)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a * F s.mem base b :=
  WP.mono (callFn_ok (by decide +kernel) hs (fun _ he ha' hb' => mulFn_ok he ho ha hb ha' hb') ho ha hb ab bb)
    fun _ ⟨op, bo, v⟩ => ⟨op, bo, toFe_mul v⟩

/-- `[o] = [a] + [b]`, by a call of `vg_gf448_r16_add`. -/
theorem addCall_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (Op.code (.add o a b)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a + F s.mem base b :=
  WP.mono (callFn_ok (by decide +kernel) hs (fun _ he ha' hb' => addFn_ok he ho ha hb ha' hb') ho ha hb ab bb)
    fun _ ⟨op, bo, v⟩ => ⟨op, bo, toFe_add v⟩

/-- `[o] = [a] - [b]`, by a call of `vg_gf448_r16_sub`. -/
theorem subCall_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (Op.code (.sub o a b)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a - F s.mem base b :=
  WP.mono (callFn_ok (by decide +kernel) hs (fun _ he ha' hb' => subFn_ok he ho ha hb ha' hb') ho ha hb ab bb)
    fun _ ⟨op, bo, v⟩ => ⟨op, bo, toFe_sub v⟩

/-- `[o] = a24 [a]`, by a call of `vg_gf448_r16_mul_a24`. -/
theorem a24Call_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : Slot o) (ha : Slot a) (ab : Bounded s.mem base a) :
    WP isa (Op.code (.mulSmall o a)) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = Spec.X448.a24 * F s.mem base a :=
  WP.mono (mulA24Call_ok hs ho ha ab) fun _ ⟨op, bo, v⟩ => ⟨op, bo, toFe_a24 v⟩

end VG.Proof.X448.Arm
