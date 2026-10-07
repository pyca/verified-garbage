import VerifiedGarbage.Proof.X448.X86.Mul
import VerifiedGarbage.Proof.X448.X86.Small
import VerifiedGarbage.Proof.Framework.X86.Spill

/-!
# X448 on x86 (32-bit): the field functions

`vg_gf448_r16_{mul,add,sub,mul_a24}` (`Impl/X448/X86.lean`) from their entry
(`FnEntry`: the working space `ws` at `base` and the offsets on the stack):
`fnEntry` loads `ws` into `edi` and saves the callee-saved registers in the
last 16 bytes of the functions' own working space (`fnEntry_ok`), the
operation writes its result (`Mul.lean`, `AddSub.lean`, `Small.lean`), and
`fnExit` restores the registers (`fnExit_ok`). Each function changes only
`eax`, `ecx`, `edx` and the flags, the result and its own working space
(`FnOut`).
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

/-- A field function's entry: the working space `ws` (its first argument) at
`base`, writable and not wrapping around; the first `n` arguments readable
outside it, as is the return address; the offsets `o` and `a` of the result
and the first operand, below the functions' own working space. -/
structure FnEntry (s : State) (base : Addr) (n o a : Nat) : Prop where
  ws : (arg s 0).setWidth 64 = base
  wr : (⟨base, 8192⟩ : Region) ∈ s.wr
  nowrap : (arg s 0).toNat + 8192 ≤ 2 ^ 32
  args : ArgArea s base n
  n3 : 3 ≤ n
  ret : ∀ k < 4, 8192 ≤ ofs base ((s.gpr .esp).setWidth 64 + BitVec.ofNat 64 k)
  argO : arg s 1 = BitVec.ofNat 32 o
  argA : arg s 2 = BitVec.ofNat 32 a
  slotO : Slot o
  slotA : Slot a

/-- What a field function changes: `eax`, `ecx` and `edx`, and in memory
the result at `o` and its own working space; the result's limbs are below
`2^16`. -/
structure FnOut (base : Addr) (o : Nat) (s t : State) : Prop where
  keeps : Keeps [.eax, .ecx, .edx] s t
  mem : FieldMem base o s.mem t.mem
  bounded : Bounded t.mem base o

/-- Where the field functions save the callee-saved registers. -/
def fnSlots : Spill.Slots := [(.ebx, SAVE), (.esi, SAVE + 4), (.edi, SAVE + 8), (.ebp, SAVE + 12)]

theorem fnSlots_fits : Spill.Fits 8192 fnSlots := by decide

abbrev FnSaved (base : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop := Spill.Saved m (off base) g fnSlots

/-- A frame of the `n` bytes at offset `d`. -/
theorem Outside.of_frameAt {base : Addr} {d n : Nat} {m m' : Mem} (hd : d + n ≤ 8192)
    (hf : Frame [⟨off base d, n⟩] m m') : Outside base d n m m' :=
  fun x hx => hf x fun r hr => by
    rw [List.mem_singleton.mp hr]
    change ¬ ((x - (base + BitVec.ofNat 64 d)).toNat + 1 ≤ n)
    have := (Offset.lt_iff x base (d := d) (n := n) (by omega)).mp
    simp only [ofs] at hx
    intro h
    have := this (by omega)
    omega

theorem fnEntry_ok {s : State} {base : Addr} {n o a : Nat} (h : FnEntry s base n o a) :
    WP isa (.block fnEntry) s fun t =>
      FnCtx t base n o a ∧ FnSaved base s.gpr t.mem ∧ Outside base SAVE 16 s.mem t.mem ∧
      Keeps [.eax, .edi] s t := by
  change WP isa (.block (.mov .eax (.mem (argOp 0)) ::
    (Spill.saveCode .eax fnSlots ++ [.mov .edi (.reg .eax)]))) s _
  refine h.args.load (by have := h.n3; omega) fun t ht => ?_
  refine Spill.save_ofNat_ok fnSlots fnSlots_fits (by rw [ht.gpr]; exact h.nowrap)
    (fun p hp => by
      rw [ht.gpr, ht.wr, h.ws]
      exact ⟨_, h.wr, contains_sc (by have := fnSlots_fits.1 p hp; omega)⟩) fun u hu => ?_
  have hm : u.mem = Spill.saveMem s.mem (off base) s.gpr fnSlots := by
    rw [hu.mem, ht.gpr, ht.mem, h.ws]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp => ht.other _ (by revert p hp; decide)
  refine wp_mov rfl fun v hv => WP.block_nil ?_
  have kv : Keeps [.eax, .edi] s v :=
    ((ht.rest (by decide)).trans (⟨fun r _ => by rw [hu.gpr], hu.rd, hu.wr⟩ : Keeps [.eax, .edi] t u)).trans
      (hv.rest (by decide))
  have mv : Outside base SAVE 16 s.mem v.mem := by
    rw [hv.mem, hm]
    refine Outside.of_frameAt (by decide) (Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p hp => ?_)
    have := fnSlots_fits.1 p hp
    have h2 : SAVE ≤ p.2 ∧ p.2 + 4 ≤ SAVE + 16 := by revert p hp; decide
    exact Offset.contains _ h2.1 h2.2 (by simp only [SAVE]; omega)
  have vs : Scr v base := ⟨by rw [hv.gpr, hu.gpr, ht.gpr]; exact h.ws, by rw [hv.wr, hu.wr, ht.wr]; exact h.wr,
    by rw [hv.gpr, hu.gpr, ht.gpr]; exact h.nowrap⟩
  obtain ⟨va, varg⟩ := h.args.keep (kv.1 _ (by decide)) kv.2.1 kv.2.2 (mv.mono (by decide) (by decide))
  refine ⟨⟨vs, va, h.n3, by rw [varg 1 (by have := h.n3; omega)]; exact h.argO,
    by rw [varg 2 (by have := h.n3; omega)]; exact h.argA, h.slotO, h.slotA⟩, ?_, mv, kv⟩
  rw [hv.mem, hm]
  exact Spill.saveMem_saved_ofNat _ _ _ fnSlots_fits (by decide)

theorem fnExit_ok {s : State} {base : Addr} (hs : Scr s base) {g : Reg → BitVec 32}
    (hsv : FnSaved base g s.mem) :
    WP isa (.block fnExit) s fun t =>
      (∀ r ∈ [Reg.ebx, .esi, .edi, .ebp], t.gpr r = g r) ∧ t.mem = s.mem ∧
      Keeps [.ebx, .esi, .edi, .ebp] s t := by
  change WP isa (.block (Spill.restoreCode .edi ([(.ebx, SAVE), (.esi, SAVE + 4), (.ebp, SAVE + 12)] ++
    [(.edi, SAVE + 8)]) ++ [])) s _
  have hb : (s.gpr .edi).setWidth 64 = base := hs.edi
  have slot : ∀ p ∈ ([(.ebx, SAVE), (.esi, SAVE + 4), (.ebp, SAVE + 12)] ++ [(.edi, SAVE + 8)] : Spill.Slots),
      p ∈ fnSlots := by decide
  refine Spill.restoreBase_ok (g := g) _ (by decide) (fun p hp => ?_) (fun p hp => ?_) fun t ht => WP.block_nil ?_
  · have := fnSlots_fits.1 p (slot p hp)
    rw [Spill.addr_eq_of hs.nowrap (n := 8192) (by omega), hb]
    exact hs.read (by omega)
  · have := fnSlots_fits.1 p (slot p hp)
    rw [Spill.addr_eq_of hs.nowrap (n := 8192) (by omega), hb]
    exact hsv p (slot p hp)
  · refine ⟨fun r hr => ?_, ht.mem, ⟨fun r hr => ht.other r (by
      simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, not_or] at hr ⊢
      exact ⟨⟨hr.1, hr.2.1, hr.2.2.2⟩, hr.2.2.1⟩), ht.rd, ht.wr⟩⟩
    have := ht.regs r (by revert r hr; decide)
    exact this

theorem FnSaved.keep {base : Addr} {g : Reg → BitVec 32} {m m' : Mem} (hs : FnSaved base g m)
    {o : Nat} (ho : Slot o) (h : FieldMem base o m m' WORK) : FnSaved base g m' := by
  have ho' : o + 112 ≤ 3584 := ho
  refine hs.of_readW fun p hp => ?_
  have hp' : SAVE ≤ p.2 ∧ p.2 + 4 ≤ SAVE + 16 := by revert p hp; decide
  have hs' : p.2 + 4 < 2 ^ 64 := by simp only [SAVE] at hp'; omega
  exact Mem.readW_congr fun i hi => h _
    (Or.inr (by rw [ofs_off base (d := p.2) (i := i) (by omega)]; simp only [SAVE] at hp'; omega))
    (Or.inr (by rw [ofs_off base (d := p.2) (i := i) (by omega)]; simp only [SAVE, ACC, WORK, TMP] at hp' ⊢; omega))

/-- The exit, after a body that changed the registers `rs` (not `esp`) and,
in the working space, the result and the arithmetic's own bytes. -/
theorem fnExit_out {s t u : State} {base : Addr} {n o a : Nat} (tc : FnCtx t base n o a)
    (tv : FnSaved base s.gpr t.mem) (tm : Outside base SAVE 16 s.mem t.mem) (tk : Keeps [.eax, .edi] s t)
    {rs : List Reg} (hrs : .esp ∉ rs) (uk : Keeps rs t u) (us : Scr u base)
    (um : FieldMem base o t.mem u.mem WORK) (ub : Bounded u.mem base o) :
    WP isa (.block fnExit) u fun w => FnOut base o s w ∧ w.mem = u.mem := by
  refine WP.mono (fnExit_ok us (tv.keep tc.slotO um)) fun w ⟨wr, wm, wk⟩ => ?_
  refine ⟨⟨⟨fun r hr => ?_, wk.2.1.trans (uk.2.1.trans tk.2.1), wk.2.2.trans (uk.2.2.trans tk.2.2)⟩,
    ?_, by rw [wm]; exact ub⟩, wm⟩
  · by_cases hs : r ∈ [Reg.ebx, .esi, .edi, .ebp]
    · exact wr r hs
    · have hr' : r = .esp := by
        cases r <;> first | rfl | exact absurd (by decide) hr | exact absurd (by decide) hs
      subst hr'
      rw [wk.1 _ (by decide), uk.1 _ hrs, tk.1 _ (by decide)]
  · rw [wm]
    exact (FieldMem.work tm (by decide) (by decide)).trans (um.mono (by decide))

/-- A field function of one block: its entry, its `body`, and its exit. -/
theorem fnBlock_ok {s : State} {base : Addr} {n o a : Nat} (h : FnEntry s base n o a) {body : List Instr}
    {Q : Mem → Prop}
    (hb : ∀ t, FnCtx t base n o a → Outside base SAVE 16 s.mem t.mem → Keeps [.eax, .edi] s t →
      WP isa (.block body) t fun u => FnPost base o t u ∧ Q u.mem) :
    WP isa (.block (fnEntry ++ body ++ fnExit)) s fun w => FnOut base o s w ∧ Q w.mem := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (fnEntry_ok h) fun t ⟨tc, tv, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hb t tc tm tk) fun u ⟨⟨uk, um, ub⟩, uq⟩ => ?_
  refine WP.mono (fnExit_out tc tv tm tk (by decide) uk (tc.scr.of_keeps uk (by decide)) um ub)
    fun w ⟨hw, wm⟩ => ⟨hw, by rw [wm]; exact uq⟩

theorem mulA24Fn_ok {s : State} {base : Addr} {o a : Nat} (h : FnEntry s base 3 o a)
    (ab : Bounded s.mem base a) :
    WP isa mulA24Fn s fun t => FnOut base o s t ∧ F t.mem base o = Spec.X448.a24 * F s.mem base a := by
  have ha' : a + 112 ≤ 3584 := h.slotA
  refine WP.mono (fnBlock_ok (body := argPtr .esi 2 ++ a24Cols ++ normalize)
    (Q := fun m => F m base o = Spec.X448.a24 * F s.mem base a) h fun t tc tm _ => ?_) fun _ h => h
  have ea : fe t.mem base a = fe s.mem base a := tm.fe (Or.inl (by simp only [SAVE]; omega)) (by omega)
  have bt : Bounded t.mem base a := fun i hi => by
    rw [tm.limbs (Or.inl (by simp only [SAVE]; omega)) (by omega) hi]; exact ab i hi
  refine WP.mono (a24Body_ok tc bt) fun u ⟨up, uv⟩ => ⟨up, ?_⟩
  rw [uv, F, F, ea]

/-- The third argument after the entry. -/
theorem argB_keep {s t : State} {base : Addr} {o a b : Nat} (h : FnEntry s base 4 o a)
    (hvb : arg s 3 = BitVec.ofNat 32 b) (tk : Keeps [.eax, .edi] s t)
    (tm : Outside base SAVE 16 s.mem t.mem) : arg t 3 = BitVec.ofNat 32 b := by
  rw [(h.args.keep (tk.1 _ (by decide)) tk.2.1 tk.2.2 (tm.mono (by decide) (by decide))).2 3 (by decide), hvb]

/-- Operands below the own working space read the same after the entry. -/
theorem entry_operand {s t : State} {base : Addr} {a : Nat} (ha : Slot a)
    (tm : Outside base SAVE 16 s.mem t.mem) :
    fe t.mem base a = fe s.mem base a ∧ (Bounded s.mem base a → Bounded t.mem base a) := by
  have ha' : a + 112 ≤ 3584 := ha
  refine ⟨tm.fe (Or.inl (by simp only [SAVE]; omega)) (by omega), fun ab i hi => ?_⟩
  rw [tm.limbs (Or.inl (by simp only [SAVE]; omega)) (by omega) hi]; exact ab i hi

theorem addFn_ok {s : State} {base : Addr} {o a b : Nat} (h : FnEntry s base 4 o a)
    (hvb : arg s 3 = BitVec.ofNat 32 b) (hb : Slot b) (ab : Bounded s.mem base a)
    (bb : Bounded s.mem base b) :
    WP isa addFn s fun t => FnOut base o s t ∧ F t.mem base o = F s.mem base a + F s.mem base b := by
  rw [show addFn = .block (fnEntry ++ (argPtr .esi 2 ++ argPtr .ebp 3 ++ addCols ++ normalize) ++ fnExit)
    by simp only [addFn, List.append_assoc]]
  refine fnBlock_ok (Q := fun m => F m base o = F s.mem base a + F s.mem base b) h fun t tc tm tk => ?_
  obtain ⟨ea, ba⟩ := entry_operand h.slotA tm
  obtain ⟨eb, bb'⟩ := entry_operand hb tm
  exact WP.mono (addBody_ok tc (argB_keep h hvb tk tm) hb (ba ab) (bb' bb)) fun u ⟨up, uv⟩ =>
    ⟨up, by rw [uv, F, F, ea, eb]⟩

theorem subFn_ok {s : State} {base : Addr} {o a b : Nat} (h : FnEntry s base 4 o a)
    (hvb : arg s 3 = BitVec.ofNat 32 b) (hb : Slot b) (ab : Bounded s.mem base a)
    (bb : Bounded s.mem base b) :
    WP isa subFn s fun t => FnOut base o s t ∧ F t.mem base o = F s.mem base a - F s.mem base b := by
  rw [show subFn = .block (fnEntry ++ (argPtr .esi 2 ++ argPtr .ebp 3 ++ subCols ++ normalize) ++ fnExit)
    by simp only [subFn, List.append_assoc]]
  refine fnBlock_ok (Q := fun m => F m base o = F s.mem base a - F s.mem base b) h fun t tc tm tk => ?_
  obtain ⟨ea, ba⟩ := entry_operand h.slotA tm
  obtain ⟨eb, bb'⟩ := entry_operand hb tm
  exact WP.mono (subBody_ok tc (argB_keep h hvb tk tm) hb (ba ab) (bb' bb)) fun u ⟨up, uv⟩ =>
    ⟨up, by rw [uv, F, F, ea, eb]⟩

theorem mulFn_ok {s : State} {base : Addr} {o a b : Nat} (h : FnEntry s base 4 o a)
    (hvb : arg s 3 = BitVec.ofNat 32 b) (hb : Slot b) (ab : Bounded s.mem base a)
    (bb : Bounded s.mem base b) :
    WP isa mulFn s fun t => FnOut base o s t ∧ F t.mem base o = F s.mem base a * F s.mem base b := by
  unfold mulFn
  rw [List.append_assoc, WP.seq_iff, WP.block_append_iff]
  refine WP.mono (fnEntry_ok h) fun t ⟨tc, tv, tm, tk⟩ => ?_
  obtain ⟨ea, ba⟩ := entry_operand h.slotA tm
  obtain ⟨eb, bb'⟩ := entry_operand hb tm
  refine WP.mono (mulSetup_ok tc (argB_keep h hvb tk tm)) fun u ⟨s0, hu, hp, k0, m0⟩ => ?_
  have c0 := tc.keep k0 (by decide) (by decide) (by rw [m0]; exact Outside.refl _ _ _ _)
  rw [WP.seq_iff]
  refine WP.mono (mulRows_ok c0 hb hp (by rw [m0]; exact ba ab) (by rw [m0]; exact bb' bb) hu)
    fun v hv => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulTail_ok c0 hv) fun w ⟨wm, wb, wv, wk⟩ => ?_
  have kw : Keeps (.esi :: clob) t w :=
    ((k0.mono (by decide)).trans (hv.regs.mono (by decide))).trans (wk.mono (by decide))
  have mw : FieldMem base o t.mem w.mem WORK := by
    rw [← m0]
    exact (FieldMem.work hv.mem (by decide) (by decide)).trans wm
  refine WP.mono (fnExit_out tc tv tm tk (by decide) kw (tc.scr.of_keeps kw (by decide)) mw wb)
    fun x ⟨hx, xm⟩ => ⟨hx, ?_⟩
  rw [xm, wv, F, F, F, F, m0, ea, eb]

end VG.Proof.X448.X86
