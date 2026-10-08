import VerifiedGarbage.Proof.Idea.AArch64.Key
import VerifiedGarbage.Proof.Idea.Inverse

/-!
# IDEA decryption subkeys on AArch64

Each decryption subkey is a copy, the negation or the inverse of an
encryption subkey (`invertKey_getD`, `Impl.Idea.invOp`), computed into
`x3` (`invWord_ok`; the inverse by a loop of fifteen steps of
`t := (t ⊙ t) ⊙ a`, `invLoop_ok`), placed in its 16 bits of `x9`
(`invPlace`), and stored a quadword at a time (`invQuad_ok`).
-/

namespace VG.Proof.Idea.AArch64

open VG VG.AArch64 VG.Impl.Idea.AArch64 VG.Impl.Idea

/-- The registers computing a decryption subkey writes. -/
abbrev invWrites : List Reg := [.x3, .x4, .x5, .x6, .x7, .x11, .x12]

theorem loadKey_run (z : Spec.Idea.Schedule) (r : Reg) {k : Nat} (hk : k < 52) (t : State)
    (hz : KeyOk z t) :
    ∃ t', runBlock isa (loadKey r k) t = some t' ∧ (t'.gpr r).setWidth 16 = z.getD k 0 ∧
      Keep [r] t t' := by
  obtain ⟨hin, h0, h1⟩ := hz.pair (k := k / 2) (by omega)
  unfold loadKey
  split
  · rename_i h
    rw [show 2 * (k / 2) = k by omega] at h0
    refine ⟨t.write .w r (t.mem.readW (t.gpr .x0 + BitVec.ofNat 64 (4 * (k / 2))) 32), ?_, ?_, ?_⟩
    · rw [runBlock_cons, exec_ldr_w ⟨by omega, by omega⟩ hin, runStep_some, runBlock_nil]
    · rw [RegUpd.gpr_write_self]; exact h0
    · keep_tac
  · rename_i h
    rw [show 2 * (k / 2) + 1 = k by omega] at h1
    simp only [runBlock_cons, exec_ldr_w ⟨by omega, by omega⟩ hin, runStep_some, exec_lsr_x
      (show 16 < 64 by decide), runBlock_nil, Option.some.injEq, exists_eq_left',
      RegUpd.gpr_write_self, State.read, Size.bits, BitVec.setWidth_eq]
    exact ⟨h1, by keep_tac⟩

theorem sub_one_run (r : Reg) (s : State) :
    ∃ s', runBlock isa [.subImm .x r r 1] s = some s' ∧ s'.gpr r = s.gpr r - 1 ∧ Keep [r] s s' := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, isa, Size.bits,
    Nat.reduceLT, ↓reduceIte, BitVec.setWidth_eq, RegUpd.gpr_write, ofNat_one,
    Option.some.injEq, exists_eq_left', true_and]
  keep_tac

theorem invStep_run (t : State) (hm : MaskOk t) :
    ∃ t', runBlock isa invStep t = some t' ∧
      t'.gpr .x6 = (Spec.Idea.mul (Spec.Idea.mul ((t.gpr .x6).setWidth 16) ((t.gpr .x6).setWidth 16))
        ((t.gpr .x5).setWidth 16)).setWidth 64 ∧
      t'.gpr .x7 = t.gpr .x7 - 1 ∧ Keep [.x6, .x7, .x11, .x12] t t' := by
  obtain ⟨t₁, h₁, v₁, e₁⟩ := mul_run (d := .x6) .x6 (b := .x6) (by decide) t hm
  obtain ⟨t₂, h₂, v₂, e₂⟩ := mul_run (d := .x6) .x6 (b := .x5) (by decide) t₁
    ((e₁.reg .x15 (by decide)).trans hm)
  obtain ⟨t₃, h₃, v₃, e₃⟩ := sub_one_run .x7 t₂
  refine ⟨t₃, run_append (run_append h₁ h₂) h₃, ?_, ?_, ?_⟩
  · rw [e₃.reg .x6 (by decide), v₂, v₁, setWidth_setWidth16, e₁.reg .x5 (by decide)]
  · rw [v₃, e₂.reg .x7 (by decide), e₁.reg .x7 (by decide)]
  · exact (e₁.mono (by decide)).trans ((e₂.mono (by decide)).trans (e₃.mono (by decide)))

/-- `c` steps remain: `x6` holds `chain a (15 - c)` in its low word. -/
structure InvLoop (a : Spec.Idea.Word) (t₀ : State) (c : Nat) (t : State) : Prop where
  pos : 1 ≤ c
  le : c ≤ 15
  x7 : t.gpr .x7 = BitVec.ofNat 64 c
  x5 : (t.gpr .x5).setWidth 16 = a
  x6 : (t.gpr .x6).setWidth 16 = chain a (15 - c)
  keep : Keep [.x6, .x7, .x11, .x12] t₀ t

theorem invLoop_ok (a : Spec.Idea.Word) (t₀ : State) (hm : MaskOk t₀) (c : Nat) (t : State)
    (hi : InvLoop a t₀ c t) :
    WP isa (.loop (.block invStep) (.nonzero .x .x7)) t (fun t' =>
      t'.gpr .x6 = (Spec.Idea.inv a).setWidth 64 ∧ Keep [.x6, .x7, .x11, .x12] t₀ t') := by
  refine WP.loop (M := isa) (InvLoop a t₀) (fun c t hi => ?_) c t hi
  obtain ⟨t', h', x6', x7', e'⟩ := invStep_run t ((hi.keep.reg .x15 (by decide)).trans hm)
  refine WP.of_runBlock ⟨t', h', ?_⟩
  have hv : t'.gpr .x6 = (chain a (15 - c + 1)).setWidth 64 := by
    rw [x6', hi.x6, hi.x5]; rfl
  have hc : t'.gpr .x7 = BitVec.ofNat 64 (c - 1) := by
    rw [x7', hi.x7]
    apply BitVec.eq_of_toNat_eq
    have := hi.pos; have := hi.le
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, toNat_one]
    omega
  have hev : isa.eval (.nonzero .x .x7) t' = some (decide (c - 1 ≠ 0)) := by
    have := hi.le
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hc, bne, beq_zero,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c - 1 < 2 ^ 64 by omega), decide_not]
  have keep' : Keep [.x6, .x7, .x11, .x12] t₀ t' := hi.keep.trans e'
  by_cases hlast : c = 1
  · subst hlast
    left
    refine ⟨hev, ?_, keep'⟩
    rw [hv, show 15 - 1 + 1 = 15 from rfl, chain_inv]
  · right
    have := hi.pos; have := hi.le
    refine ⟨by rw [hev]; simp only [ne_eq, Option.some.injEq, decide_eq_true_eq]; omega,
      c - 1, by omega, by omega, by omega, hc, ?_, ?_, keep'⟩
    · rw [e'.reg .x5 (by decide)]; exact hi.x5
    · rw [hv, setWidth_setWidth16, show 15 - c + 1 = 15 - (c - 1) by omega]

theorem and_mask_run (r : Reg) (s : State) (hm : MaskOk s) :
    ∃ s', runBlock isa [.logic .and .x r r .x15] s = some s' ∧
      s'.gpr r = ((s.gpr r).setWidth 16).setWidth 64 ∧ Keep [r] s s' := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, isa, Size.bits,
    BitVec.setWidth_eq, RegUpd.gpr_write, ↓reduceIte, hm, mask_setWidth,
    Option.some.injEq, exists_eq_left', true_and]
  keep_tac

theorem invWord_ok (z : Spec.Idea.Schedule) {n : Nat} (hn : n < 52) (t : State) (hz : KeyOk z t)
    (hm : MaskOk t) :
    WP isa (invWord n) t (fun t' =>
      t'.gpr .x3 = ((Spec.Idea.invertKey z).getD n 0).setWidth 64 ∧ Keep invWrites t t') := by
  rw [invertKey_getD z hn]
  have hk := invOp_lt hn
  unfold invWord
  rcases hop : invOp n with ⟨op, k⟩
  rw [hop] at hk
  cases op with
  | copy =>
    obtain ⟨t₁, h₁, v₁, e₁⟩ := loadKey_run z .x3 hk t hz
    obtain ⟨t₂, h₂, v₂, e₂⟩ := and_mask_run .x3 t₁ ((e₁.reg .x15 (by decide)).trans hm)
    refine WP.of_runBlock ⟨t₂, run_append h₁ h₂, ?_, ?_⟩
    · rw [v₂, v₁]; rfl
    · exact (e₁.mono (by decide)).trans (e₂.mono (by decide))
  | neg =>
    obtain ⟨t₁, h₁, v₁, e₁⟩ := loadKey_run z .x4 hk t hz
    have m₁ : MaskOk t₁ := (e₁.reg .x15 (by decide)).trans hm
    obtain ⟨t₂, h₂, v₂, e₂⟩ : ∃ t₂, runBlock isa [.movz .x .x3 0 0, .sub .x .x3 .x3 .x4,
        .logic .and .x .x3 .x3 .x15] t₁ = some t₂ ∧
        t₂.gpr .x3 = (0 - t₁.gpr .x4) &&& 65535 ∧ Keep [.x3] t₁ t₂ := by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, isa, Size.bits,
        Nat.mul_zero, Nat.reduceLT, ↓reduceIte, BitVec.setWidth_eq, RegUpd.gpr_write, reduceCtorEq,
        m₁, Option.some.injEq, exists_eq_left']
      exact ⟨rfl, by keep_tac⟩
    refine WP.of_runBlock ⟨t₂, run_append h₁ h₂, ?_, ?_⟩
    · rw [v₂, neg_mask, v₁]; rfl
    · exact (e₁.mono (by decide)).trans (e₂.mono (by decide))
  | inv =>
    apply WP.seq
    obtain ⟨t₁, h₁, v₁, e₁⟩ := loadKey_run z .x5 hk t hz
    obtain ⟨t₂, h₂, x5₂, x6₂, x7₂, e₂⟩ : ∃ t₂, runBlock isa [.addImm .x .x6 .x5 0, .movz .x .x7 15 0] t₁ =
        some t₂ ∧ t₂.gpr .x5 = t₁.gpr .x5 ∧ t₂.gpr .x6 = t₁.gpr .x5 ∧ t₂.gpr .x7 = 15 ∧
        Keep [.x6, .x7] t₁ t₂ := by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, isa, Size.bits,
        Nat.mul_zero, Nat.reduceLT, ↓reduceIte, BitVec.setWidth_eq, RegUpd.gpr_write, reduceCtorEq,
        Option.some.injEq, exists_eq_left']
      exact ⟨trivial, BitVec.add_zero _, rfl, by keep_tac⟩
    have m₂ : MaskOk t₂ := (e₂.reg .x15 (by decide)).trans ((e₁.reg .x15 (by decide)).trans hm)
    refine WP.of_runBlock ⟨t₂, run_append h₁ h₂, ?_⟩
    apply WP.seq
    refine WP.mono (invLoop_ok (z.getD k 0) t₂ m₂ 15 t₂ ⟨by decide, by decide, x7₂, by rw [x5₂, v₁],
      by rw [x6₂, v₁]; rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩) fun t₃ ⟨x6₃, e₃⟩ => ?_
    obtain ⟨t₄, h₄, x3₄, e₄⟩ : ∃ t₄, runBlock isa [.addImm .x .x3 .x6 0] t₃ = some t₄ ∧
        t₄.gpr .x3 = t₃.gpr .x6 ∧ Keep [.x3] t₃ t₄ := by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, isa, Size.bits,
        Nat.reduceLT, ↓reduceIte, BitVec.setWidth_eq, RegUpd.gpr_write, Option.some.injEq,
        exists_eq_left']
      exact ⟨by simp, by keep_tac⟩
    refine WP.of_runBlock ⟨t₄, h₄, ?_, ?_⟩
    · rw [x3₄, x6₃]; rfl
    · exact (e₁.mono (by decide)).trans ((e₂.mono (by decide)).trans ((e₃.mono (by decide)).trans
        (e₄.mono (by decide))))

/-- Decryption subkey `n` of `z`. -/
abbrev dk (z : Spec.Idea.Schedule) (n : Nat) : Spec.Idea.Word := (Spec.Idea.invertKey z).getD n 0

/-- `x9` holds the first `i` decryption subkeys of quadword `q`, and zeros above. -/
def Acc (z : Spec.Idea.Schedule) (q i : Nat) (t : State) : Prop :=
  ∀ p < 64, (t.gpr .x9).getLsbD p =
    if p < 16 * i then (dk z (4 * q + p / 16)).getLsbD (p % 16) else false

theorem invPlace_run (z : Spec.Idea.Schedule) (q i : Nat) (hi : i < 4) (t : State)
    (hx3 : t.gpr .x3 = (dk z (4 * q + i)).setWidth 64) (hacc : i = 0 ∨ Acc z q i t) :
    ∃ t', runBlock isa (invPlace (4 * q + i)) t = some t' ∧ Acc z q (i + 1) t' ∧
      Keep [.x3, .x9] t t' := by
  unfold invPlace
  split
  · rename_i h
    have hi0 : i = 0 := by omega
    subst hi0
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, isa, Size.bits,
      Nat.reduceLT, ↓reduceIte, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
    refine ⟨fun p hp => ?_, by keep_tac⟩
    rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero, hx3,
      BitVec.getLsbD_setWidth, decide_eq_true hp, Bool.true_and, Nat.add_zero]
    by_cases hp16 : p < 16
    · rw [ite_eq_left (by omega), Nat.div_eq_of_lt hp16, Nat.mod_eq_of_lt hp16, Nat.add_zero]
    · rw [ite_eq_right (by omega)]; exact BitVec.getLsbD_of_ge _ _ (by omega)
  · rename_i h
    have hi0 : i ≠ 0 := by omega
    have hacc' := hacc.resolve_left hi0
    have hm : (4 * q + i) % 4 = i := by omega
    rw [hm]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, isa, Size.bits,
      show 16 * i < 64 by omega, ↓reduceIte, BitVec.setWidth_eq, RegUpd.gpr_write, reduceCtorEq,
      Option.some.injEq, exists_eq_left']
    refine ⟨fun p hp => ?_, by keep_tac⟩
    rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.getLsbD_or, hacc' p hp, hx3, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    by_cases h1 : p < 16 * i
    · simp [h1, show p < 16 * (i + 1) by omega]
    · by_cases h2 : p < 16 * (i + 1)
      · simp [h1, h2, hp, show p - 16 * i < 64 by omega, show 4 * q + p / 16 = 4 * q + i by omega,
          show p % 16 = p - 16 * i by omega]
      · simp only [h1, h2, ↓reduceIte, Bool.false_or]
        rw [BitVec.getLsbD_of_ge (dk z (4 * q + i)) _ (by omega)]
        simp

/-- The registers computing a quadword of decryption subkeys writes. -/
abbrev quadWrites : List Reg := [.x3, .x4, .x5, .x6, .x7, .x9, .x11, .x12]

theorem quadWord_ok (z : Spec.Idea.Schedule) (q i : Nat) (hq : q < 13) (hi : i < 4) (t : State)
    (hz : KeyOk z t) (hm : MaskOk t) (hacc : i = 0 ∨ Acc z q i t) {rest : Prog isa}
    {Q : State → Prop}
    (hrest : ∀ t', Acc z q (i + 1) t' → Keep quadWrites t t' → WP isa rest t' Q) :
    WP isa (.seq (invWord (4 * q + i)) (.seq (.block (invPlace (4 * q + i))) rest)) t Q := by
  apply WP.seq
  refine WP.mono (invWord_ok z (by omega) t hz hm) fun t₁ ⟨v₁, e₁⟩ => ?_
  apply WP.seq
  have hacc₁ : i = 0 ∨ Acc z q i t₁ := by
    rcases hacc with h | h
    · exact Or.inl h
    · right; intro p hp; rw [e₁.reg .x9 (by decide)]; exact h p hp
  obtain ⟨t₂, h₂, a₂, e₂⟩ := invPlace_run z q i hi t₁ v₁ hacc₁
  exact WP.of_runBlock ⟨t₂, h₂, hrest t₂ a₂ ((e₁.mono (by decide)).trans (e₂.mono (by decide)))⟩

/-- What `vg_idea_invert_key` needs of its state: the encryption subkeys (104
bytes at `x0`) readable, the decryption subkeys (104 bytes at `x1`)
writable, apart. -/
structure InvPre (s : State) : Prop where
  sched : ⟨s.gpr .x0, 104⟩ ∈ s.rd ++ s.wr
  out : ⟨s.gpr .x1, 104⟩ ∈ s.wr
  sep : (⟨s.gpr .x0, 104⟩ : Region).Disjoint ⟨s.gpr .x1, 104⟩

/-- After `q` quadwords of decryption subkeys. -/
structure QInv (s₀ : State) (q : Nat) (t : State) : Prop where
  x0 : t.gpr .x0 = s₀.gpr .x0
  x1 : t.gpr .x1 = s₀.gpr .x1
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  sp : t.sp = s₀.sp
  mask : MaskOk t
  regs : ∀ r ∈ preserved, t.gpr r = s₀.gpr r
  frame : Frame [⟨s₀.gpr .x1, 8 * q⟩] s₀.mem t.mem
  words : ∀ i < q, ∀ p < 64, (t.mem.readW (s₀.gpr .x1 + BitVec.ofNat 64 (8 * i)) 64).getLsbD p =
    (dk (Spec.Idea.scheduleAt s₀.mem (s₀.gpr .x0)) (4 * i + p / 16)).getLsbD (p % 16)

theorem QInv.keyOk {s₀ t : State} {q : Nat} (hp : InvPre s₀) (hi : QInv s₀ q t) (hq : q ≤ 13) :
    KeyOk (Spec.Idea.scheduleAt s₀.mem (s₀.gpr .x0)) t := by
  refine ⟨by rw [hi.x0, hi.rd, hi.wr]; exact hp.sched, ?_⟩
  rw [hi.x0]
  exact scheduleAt_congr (frame_bytes hi.frame (by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hp.sep.sub_right (Region.sub_prefix (by omega))) (by decide))

theorem invQuad_ok (s₀ : State) (hp : InvPre s₀) (q : Nat) (hq : q < 13) (t : State)
    (hi : QInv s₀ q t) : WP isa (invQuad q) t (QInv s₀ (q + 1)) := by
  have hz := hi.keyOk hp (by omega)
  have hm := hi.mask
  simp only [invQuad, show List.range 4 = [0, 1, 2, 3] from rfl, List.foldr_cons, List.foldr_nil]
  refine quadWord_ok _ q 0 hq (by decide) t hz hm (Or.inl rfl) fun t₁ a₁ e₁ => ?_
  have m₁ : MaskOk t₁ := (e₁.reg .x15 (by decide)).trans hm
  refine quadWord_ok _ q 1 hq (by decide) t₁ (hz.keep e₁ (by decide)) m₁ (Or.inr a₁)
    fun t₂ a₂ e₂ => ?_
  have m₂ : MaskOk t₂ := (e₂.reg .x15 (by decide)).trans m₁
  refine quadWord_ok _ q 2 hq (by decide) t₂ ((hz.keep e₁ (by decide)).keep e₂ (by decide)) m₂
    (Or.inr a₂) fun t₃ a₃ e₃ => ?_
  have m₃ : MaskOk t₃ := (e₃.reg .x15 (by decide)).trans m₂
  refine quadWord_ok _ q 3 hq (by decide) t₃
    (((hz.keep e₁ (by decide)).keep e₂ (by decide)).keep e₃ (by decide)) m₃ (Or.inr a₃)
    fun t₄ a₄ e₄ => ?_
  have e := e₁.trans (e₂.trans (e₃.trans e₄))
  have x1₄ : t₄.gpr .x1 = s₀.gpr .x1 := (e.reg .x1 (by decide)).trans hi.x1
  have hw : InRegions t₄.wr (t₄.gpr .x1 + BitVec.ofNat 64 (8 * q)) 8 := by
    rw [x1₄, e.wr, hi.wr]
    exact ⟨_, hp.out, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.of_runBlock ⟨{ t₄ with mem := t₄.mem.writeW (t₄.gpr .x1 + BitVec.ofNat 64 (8 * q)) (t₄.gpr .x9) },
    by rw [runBlock_cons, exec_str_x ⟨by omega, by omega⟩ hw, runStep_some, runBlock_nil], ?_⟩
  have sub : ∀ r ∈ preserved, r ∉ quadWrites := by decide
  refine ⟨(e.reg .x0 (by decide)).trans hi.x0, x1₄, e.rd.trans hi.rd, e.wr.trans hi.wr,
    e.sp.trans hi.sp, (e.reg .x15 (by decide)).trans hm,
    fun r hr => (e.reg r (sub r hr)).trans (hi.regs r hr), ?_, ?_⟩
  · show Frame _ s₀.mem (t₄.mem.writeW _ _)
    rw [e.mem, x1₄]
    refine (hi.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    simp only [List.mem_singleton] at hr; subst hr
    exact Region.sub_prefix (by omega)
  · intro i hiq p hp64
    show ((t₄.mem.writeW _ _).readW _ 64).getLsbD p = _
    rw [e.mem, x1₄]
    by_cases he : i = q
    · subst he
      rw [Mem.readW_writeW_self64, a₄ p hp64, ite_eq_left (by omega)]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact hi.words i (by omega) p hp64

/-- Quadwords `q … q + n - 1`. -/
def quads (q n : Nat) : Prog isa :=
  (List.range' q n).foldr (fun q rest => .seq (invQuad q) rest) (.block [])

theorem quads_ok (s₀ : State) (hp : InvPre s₀) :
    ∀ n q, q + n = 13 → ∀ t, QInv s₀ q t → WP isa (quads q n) t (QInv s₀ 13)
  | 0, q, h, t, hi => by
    rw [Nat.add_zero] at h; subst h
    exact WP.block_nil hi
  | n + 1, q, h, t, hi => by
    simp only [quads, List.range'_succ, List.foldr_cons]
    apply WP.seq
    exact WP.mono (invQuad_ok s₀ hp q (by omega) t hi) fun t₁ h₁ =>
      quads_ok s₀ hp n (q + 1) (by omega) t₁ h₁

theorem invertKey_eq : invertKey = .seq (.block [setMask]) (quads 0 13) := rfl

/-- `vg_idea_invert_key` on AArch64. -/
def invertContract : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 104⟩
    let out : Region := ⟨s.gpr .x1, 104⟩
    s.rd = [sched] ∧ s.wr = [out] ∧ sched.Disjoint out
  post s s' := Spec.Idea.scheduleAt s'.mem (s.gpr .x1) =
    Spec.Idea.invertKey (Spec.Idea.scheduleAt s.mem (s.gpr .x0))
  pub := PublicRegs [.x0, .x1]

theorem invert_correct (s : State) (hs : invertContract.pre s) :
    ∃ t s', Exec isa invertKey s t s' ∧ abiPreserved s s' ∧ invertContract.post s s' := by
  obtain ⟨hrd, hwr, hsep⟩ := hs
  have hp : InvPre s := ⟨by rw [hrd]; simp, by rw [hwr]; simp, hsep⟩
  obtain ⟨s₁, h₁, m₁, e₁⟩ := setMask_run s
  have hw : WP isa invertKey s (QInv s 13) := by
    rw [invertKey_eq]
    apply WP.seq
    refine WP.of_runBlock ⟨s₁, h₁, quads_ok s hp 13 0 rfl s₁ ⟨e₁.reg .x0 (by decide),
      e₁.reg .x1 (by decide), e₁.rd, e₁.wr, e₁.sp, m₁, fun r hr => e₁.reg r ?_,
      by rw [e₁.mem]; exact Frame.refl _ _, fun i hi => absurd hi (by omega)⟩⟩
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨tr, s', he, hi⟩ := hw
  refine ⟨tr, s', he, ⟨hi.regs, hi.sp, Exec.preservedV he (by lit_decide)⟩, ?_⟩
  show Spec.Idea.scheduleAt s'.mem (s.gpr .x1) = _
  apply Vector.ext
  intro n hn
  rw [← getD_lt _ 0 hn, ← getD_lt _ 0 hn]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  rw [scheduleAt_getLsbD _ _ hn hb, hi.words (n / 4) (by omega) _ (by omega),
    show 4 * (n / 4) + (16 * (n % 4) + b) / 16 = n by omega,
    show (16 * (n % 4) + b) % 16 = b by omega]

def invertSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 104⟩]
  wr := [⟨0x2000, 104⟩]

theorem invertKey_verified : Verified target invertKey (Spec.Idea.invertKeyContract abi) := by
  refine Verified.of_correct invert_correct (invertKey_constantTime _) ?_
  sig_implies [Spec.Idea.invertKeyContract, Spec.Idea.invertKeySig, Spec.Idea.invertKeyPost, abi,
    argRegs, invertContract, publicRegs_two] [invertSat] using invertSat

end VG.Proof.Idea.AArch64
