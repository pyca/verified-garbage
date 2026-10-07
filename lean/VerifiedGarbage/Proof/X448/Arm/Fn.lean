import VerifiedGarbage.Proof.X448.Arm.Mul
import VerifiedGarbage.Proof.X448.Arm.AddSub
import VerifiedGarbage.Proof.X448.Arm.Small
import VerifiedGarbage.TCB.Arm.Target

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
  rw [VG.Arm.addr_add (by have := hs.nowrap; omega), hs.r0]

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
    refine wp_str (by omega) (hs.ea (by omega)) ⟨_, hs.wr, contains_sc (by omega)⟩ fun s₁ m₁ => ?_
    have hs₁ := hs.of_rest (m₁.rest []) (by decide)
    refine WP.mono (strs_ok hs₁ l (fun q h => hl q (List.mem_cons_of_mem _ h)) hp.2) fun s' ⟨K, O, V⟩ => ?_
    have O₁ : Outside base p.2 4 s.mem s₁.mem := by rw [m₁.mem]; exact writeW_outside _ _ _ (by omega)
    refine ⟨(m₁.rest _).trans K, fun x hx => ?_, fun q hq => ?_⟩
    · rw [O x fun q hq => hx q (List.mem_cons_of_mem _ hq), O₁ x (hx p List.mem_cons_self)]
    · rcases List.mem_cons.mp hq with rfl | hq
      · have e : word s'.mem base q.2 = word s₁.mem base q.2 := Mem.readW_congr fun i hi =>
          O _ fun r hr => by
            rw [ofs_off base (by omega)]; have := hp.1 r hr; omega
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
    refine wp_ldr (by omega) (hs.ea (by omega)) (List.mem_append_right _ hs.wr |> fun h =>
      ⟨_, h, contains_sc (by omega)⟩) fun s₁ u₁ => ?_
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
  refine WP.mono (strs_ok h.base saves (fun p hp => by have := saves_bound p hp; simp only [SAVE] at this; omega)
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
        omega }
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
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off base (by omega)]; omega)
    (Or.inr (by rw [ofs_off base (by omega)]; omega))).symm).symm

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
    fun hd _ hi => O₁.limbs (Or.inl (by simp only [SAVE]; omega)) (by omega) hi
  have fa : ∀ {d : Nat}, d + 112 ≤ 3584 → fe s₁.mem base d = fe s.mem base d :=
    fun hd => valN_congr fun _ hi => ea hd _ hi
  rw [WP.seq_iff]
  refine WP.mono (hop s₁ E.scr E.po E.pa E.pb (fun i hi => by rw [ea ha' i hi]; exact ab i hi)
    (fun i hi => by rw [ea hb' i hi]; exact bb i hi)) fun s₂ ⟨K₂, M₂, B₂, R₂⟩ => ?_
  have hb₂ : Base s₂ base :=
    let hs₂ := E.scr.of_keeps K₂ (by decide)
    ⟨hs₂.r0, hs₂.wr, hs₂.nowrap⟩
  rw [restoreFn_eq]
  refine WP.mono (ldrs_ok hb₂ saves (fun p hp => by have := saves_bound p hp; simp only [SAVE] at this; omega)
    (by decide) (by decide)) fun s₃ ⟨M₃, K₃, V₃⟩ => ?_
  have sv : ∀ p ∈ saves, s₃.gpr p.1 = s.gpr p.1 := fun p hp => by
    have := saves_bound p hp
    rw [V₃ p hp, M₂.word this.1 (by simp only [SAVE] at this ⊢; omega) (by simp only [SAVE] at this; omega),
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
