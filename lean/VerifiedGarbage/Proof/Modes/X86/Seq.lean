import VerifiedGarbage.Proof.Modes.X86.Step
import VerifiedGarbage.TCB.X86.Target

/-!
# A mode on x86 (32-bit), for any core: the whole function

`seq_wp`: `c.seq M`, for a core `c` with `CoreSpec c` and a mode `M` whose
operations compute the step function `F` (`Computes`), with its arguments
on the stack (`f(key, iv, data, n, scratch)`), replaces the `n` steps of
data at `data` with the outputs of `F` from the IV, and (if `M.ivOut`) the
IV with the last chaining value; it keeps the callee-saved registers and
the return address. Each mode's and cipher's contract follows from it.
-/

namespace VG.Proof.Modes.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Modes VG.Impl.Modes.X86
open VG.Spec.Aes (bytesAt)

variable {c : Core} {M : Mode}

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev P : BitVec 32 := arg s₀ 1
abbrev Dp : BitVec 32 := arg s₀ 2
abbrev N : Nat := (arg s₀ 3).toNat
abbrev S : BitVec 32 := arg s₀ 4

abbrev argsR : Region := ⟨argAddr s₀ 0, 20⟩
abbrev retR : Region := ⟨(s₀.gpr .esp).setWidth 64, 4⟩
abbrev ivR (c : Core) : Region := ⟨(P s₀).setWidth 64, 4 * c.bw⟩
abbrev scrR (c : Core) : Region := ⟨(S s₀).setWidth 64, 4 * c.total⟩

end

/-- What the function needs on entry: the arguments readable, the IV
readable (and writable, apart from the data and the return address, if the
mode writes it back), the data and the scratch buffer writable, none wrapping
around, and apart from each other, the arguments, the return address and the
core's stack. -/
structure SeqPre (c : Core) (M : Mode) (s₀ : State) : Prop where
  args : argsR s₀ ∈ s₀.rd ++ s₀.wr
  espFit : (s₀.gpr .esp).toNat + 24 ≤ 2 ^ 32
  scr : ScrIn s₀ (S s₀) c.total
  ivRd : ivR s₀ c ∈ s₀.rd ++ s₀.wr
  ivWr : M.ivOut = true → ivR s₀ c ∈ s₀.wr
  ivFit : (P s₀).toNat + 4 * c.bw ≤ 2 ^ 32
  dataW : dataRegion (Dp s₀) M.step (N s₀) ∈ s₀.wr
  dataFit : (Dp s₀).toNat + M.step * N s₀ ≤ 2 ^ 32
  dataScr : Region.Disjoint (dataRegion (Dp s₀) M.step (N s₀)) (scrR s₀ c)
  ivScr : Region.Disjoint (ivR s₀ c) (scrR s₀ c)
  ivData : M.ivOut = true → Region.Disjoint (ivR s₀ c) (dataRegion (Dp s₀) M.step (N s₀))
  argsScr : Region.Disjoint (argsR s₀) (scrR s₀ c)
  argsData : Region.Disjoint (argsR s₀) (dataRegion (Dp s₀) M.step (N s₀))
  retScr : Region.Disjoint (retR s₀) (scrR s₀ c)
  retData : Region.Disjoint (retR s₀) (dataRegion (Dp s₀) M.step (N s₀))
  retIv : M.ivOut = true → Region.Disjoint (retR s₀) (ivR s₀ c)
  stkData : Region.Disjoint (stkRegion (E s₀) c.stack) (dataRegion (Dp s₀) M.step (N s₀))
  stkMode : Region.Disjoint (stkRegion (E s₀) c.stack) ⟨slotA (S s₀) c.slots, 40⟩
  stkArgs : Region.Disjoint (stkRegion (E s₀) c.stack) (argsR s₀)
  stkRet : Region.Disjoint (stkRegion (E s₀) c.stack) (retR s₀)
  stack : c.stack ≤ (s₀.gpr .esp).toNat
  step : 0 < M.step ∧ M.step ≤ 4 * c.bw
  layout : Layout c

/-! ## The arguments -/

theorem argAddr_eq (s₀ : State) (hfit : (s₀.gpr .esp).toNat + 24 ≤ 2 ^ 32) {i : Nat} (hi : i < 5) :
    argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  simp only [argAddr]
  rw [show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * i) from rfl,
    show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * 0) from rfl,
    addr_eq (by omega), addr_eq (by omega), VG.Offset.add_add]

theorem arg_contains (s₀ : State) (hfit : (s₀.gpr .esp).toNat + 24 ≤ 2 ^ 32) {i : Nat} (hi : i < 5) :
    (argsR s₀).Contains (argAddr s₀ i) 4 := by
  rw [argAddr_eq s₀ hfit hi]; exact VG.Offset.contains_base _ (by omega) (by omega)

/-- `mov r, [esp + 4 + 4 i]`: argument `i`, while the arguments are unchanged. -/
theorem wp_arg {s₀ s : State} (hp : SeqPre c M s₀) (hesp : s.gpr .esp = s₀.gpr .esp)
    (hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr) (hm : ∀ i < 5, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i) {d : Reg}
    {i : Nat} (hi : i < 5) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem (argOp i)) :: is)) s Q := by
  have e : addr (s.gpr .esp) (4 + 4 * i) = argAddr s₀ i := by rw [hesp]; rfl
  refine wp_ldm (B := s.gpr .esp) rfl (by rw [e, hrw]; exact ⟨_, hp.args, arg_contains s₀ hp.espFit hi⟩) fun s' u => ?_
  rw [e, hm i hi] at u
  exact k s' u

/-! ## The entry -/

/-- The mode's slots. -/
abbrev modeR (c : Core) (B : BitVec 32) : Region := ⟨slotA B c.slots, 40⟩

/-- `omega`, with the mode's slots unfolded. -/
local macro "slot_omega" : tactic =>
  `(tactic| ((try simp only [Core.chnSlot, Core.dSlot, Core.nSlot, Core.savedSlot]); omega))

theorem range4_map {α : Type} (f : Nat → α) : (List.range 4).map f = [f 0, f 1, f 2, f 3] := rfl

/-- The areas of the IV's copies: the IV as the data. -/
def ivAreas (c : Core) (P B : BitVec 32) : Loc → Addr
  | .dat => P.setWidth 64
  | .chn => slotA B c.chnSlot
  | .buf => slotA B c.buf

theorem ivAreasOk {s₀ s : State} (hp : SeqPre c M s₀) (hb : s.gpr sb = S s₀) (hesi : s.gpr .esi = P s₀)
    (hrw : s.rd = s₀.rd) (hw : s.wr = s₀.wr) {ws : List Loc} (hws : ∀ l ∈ ws, l = .dat → ivR s₀ c ∈ s₀.wr) :
    AreasOk c s (fun _ => 4 * c.bw) (ivAreas c (P s₀) (S s₀)) ws := by
  have hL := hp.layout
  have hfit := hp.scr.fit
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hG := hL.G_pos
  have hbG : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG
  have hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega
  have hP := hp.ivFit
  have inScr : ∀ d w, d + w ≤ 4 * c.total → InRegions s.wr ((S s₀).setWidth 64 + BitVec.ofNat 64 d) w :=
    fun d w h => ⟨_, by rw [hw]; exact hp.scr.wr, slot_contains hfit h⟩
  refine ⟨fun l off ho => ?_, fun l off w ho => ?_, fun l hl off w ho => ?_, fun l l' hne => ?_, fun _ => by omega⟩
  · cases l
    · simp only [Core.loc, ivAreas] at ho ⊢; rw [hesi, Nat.zero_add, addr_eq (by omega)]
    · simp only [Core.loc, ivAreas] at ho ⊢; rw [hb]; exact addr_slot hfit (by slot_omega)
    · simp only [Core.loc, ivAreas] at ho ⊢; rw [hb]; exact addr_slot hfit (by omega)
  · rw [hrw, hw]
    cases l
    · exact ⟨_, hp.ivRd, VG.Offset.contains_base _ ho (by omega)⟩
    · obtain ⟨r, hr, hc⟩ := inScr (4 * c.chnSlot + off) w (by slot_omega)
      refine ⟨r, List.mem_append_right _ (by rw [← hw]; exact hr), ?_⟩
      simp only [ivAreas]; rw [VG.Offset.add_add]; exact hc
    · obtain ⟨r, hr, hc⟩ := inScr (4 * c.buf + off) w (by omega)
      refine ⟨r, List.mem_append_right _ (by rw [← hw]; exact hr), ?_⟩
      simp only [ivAreas]; rw [VG.Offset.add_add]; exact hc
  · cases l
    · rw [hw]; exact ⟨_, hws _ hl rfl, VG.Offset.contains_base _ ho (by omega)⟩
    · simp only [ivAreas]; rw [VG.Offset.add_add]; exact inScr _ _ (by slot_omega)
    · simp only [ivAreas]; rw [VG.Offset.add_add]; exact inScr _ _ (by omega)
  · have dIv : ∀ d, d + 4 * c.bw ≤ 4 * c.total →
        Region.Disjoint (ivR s₀ c) ⟨(S s₀).setWidth 64 + BitVec.ofNat 64 d, 4 * c.bw⟩ :=
      fun d h => hp.ivScr.sub_right (slot_sub h)
    have dCB : Region.Disjoint ⟨slotA (S s₀) c.chnSlot, 4 * c.bw⟩ ⟨slotA (S s₀) c.buf, 4 * c.bw⟩ :=
      VG.Offset.disjoint _ (.inr (by slot_omega)) (by slot_omega) (by omega)
    cases l <;> cases l' <;> simp only [ne_eq, not_true_eq_false] at hne <;> simp only [ivAreas]
    · exact dIv _ (by slot_omega)
    · exact dIv _ (by omega)
    · exact (dIv _ (by slot_omega)).symm
    · exact dCB
    · exact (dIv _ (by omega)).symm
    · exact dCB.symm

/-- After the entry: the scratch buffer at `sb`, the callee-saved registers in
their slots, the IV in the chaining value's. -/
structure Entered (c : Core) (s₀ s : State) : Prop where
  b : s.gpr sb = S s₀
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : ∀ i < 4, s.mem.readW (slotA (S s₀) (c.savedSlot i)) 32 = s₀.gpr (Core.savedRegs.getD i .ebx)
  chn : bytesAt s.mem (slotA (S s₀) c.chnSlot) (4 * c.bw) = bytesAt s₀.mem ((P s₀).setWidth 64) (4 * c.bw)
  frame : Frame [modeR c (S s₀)] s₀.mem s.mem

theorem entry_wp {s₀ : State} (hp : SeqPre c M s₀) :
    WP isa (.block (c.entry ++ c.ivIn)) s₀ (Entered c s₀) := by
  have hL := hp.layout
  have hfit := hp.scr.fit
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega
  have hbG : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hL.G_pos
  have slotW : ∀ k, k < c.total → InRegions s₀.wr (addr (S s₀) (4 * k)) 4 := fun k hk =>
    ⟨_, hp.scr.wr, by rw [addr_eq (by omega)]; exact slot_contains hfit (by omega)⟩
  have inMode : ∀ i < 4, (modeR c (S s₀)).Contains (slotA (S s₀) (c.savedSlot i)) (32 / 8) := fun i hi =>
    VG.Offset.contains _ (by slot_omega) (by slot_omega) (by omega)
  have sep : ∀ i < 4, ∀ j < 4, i ≠ j →
      Region.Disjoint ⟨slotA (S s₀) (c.savedSlot i), 4⟩ ⟨slotA (S s₀) (c.savedSlot j), 4⟩ := fun i hi j hj hij =>
    VG.Offset.disjoint _ (by slot_omega) (by slot_omega) (by slot_omega)
  have aS : ∀ i < 4, addr (S s₀) (4 * c.savedSlot i) = slotA (S s₀) (c.savedSlot i) := fun i hi =>
    addr_slotA hfit (by slot_omega)
  simp only [Core.entry, Core.ivIn, range4_map, List.cons_append,
    List.nil_append, at_]
  refine wp_arg hp rfl rfl (fun _ _ => rfl) (by decide) fun s₁ u₁ => ?_
  have b₁ : s₁.gpr .eax = (S s₀) := u₁.gpr
  refine wp_stm b₁ (by rw [u₁.wr]; exact slotW _ (by slot_omega)) fun s₂ u₂ => ?_
  refine wp_stm (B := S s₀) (by rw [u₂.gpr]; exact b₁) (by rw [u₂.wr, u₁.wr]; exact slotW _ (by slot_omega))
    fun s₃ u₃ => ?_
  refine wp_stm (B := S s₀) (by rw [u₃.gpr, u₂.gpr]; exact b₁)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact slotW _ (by slot_omega)) fun s₄ u₄ => ?_
  refine wp_stm (B := S s₀) (by rw [u₄.gpr, u₃.gpr, u₂.gpr]; exact b₁)
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact slotW _ (by slot_omega)) fun s₅ u₅ => ?_
  refine wp_mov fun s₆ u₆ => ?_
  have g₅ : s₅.gpr = s₁.gpr := by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]
  have vals : ∀ r, r ≠ .eax → s₁.gpr r = s₀.gpr r := fun r h => u₁.other r h
  have m₅ : s₅.mem = (((s₀.mem.writeW (slotA (S s₀) (c.savedSlot 0)) (s₀.gpr .ebx)).writeW (slotA (S s₀) (c.savedSlot 1))
      (s₀.gpr .esi)).writeW (slotA (S s₀) (c.savedSlot 2)) (s₀.gpr .edi)).writeW (slotA (S s₀) (c.savedSlot 3))
      (s₀.gpr .ebp) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₄.gpr, u₃.gpr, u₂.gpr, aS 0 (by decide), aS 1 (by decide),
      aS 2 (by decide), aS 3 (by decide)]
    simp only [Core.savedRegs, List.getD_cons_zero, List.getD_cons_succ]
    rw [vals _ (by decide), vals _ (by decide), vals _ (by decide), vals _ (by decide)]
  have f₅ : Frame [modeR c (S s₀)] s₀.mem s₅.mem := by
    rw [m₅]
    exact ((((Frame.refl _ _).writeW List.mem_cons_self _ (inMode 0 (by decide))).writeW List.mem_cons_self _
      (inMode 1 (by decide))).writeW List.mem_cons_self _ (inMode 2 (by decide))).writeW List.mem_cons_self _
      (inMode 3 (by decide))
  have sv₅ : ∀ i < 4, s₅.mem.readW (slotA (S s₀) (c.savedSlot i)) 32 = s₀.gpr (Core.savedRegs.getD i .ebx) := by
    intro i hi
    rw [m₅]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [readW_write_sep (sep 0 (by decide) 3 (by decide) (by decide)),
        readW_write_sep (sep 0 (by decide) 2 (by decide) (by decide)),
        readW_write_sep (sep 0 (by decide) 1 (by decide) (by decide)), Mem.readW_writeW_self32]; rfl
    · rw [readW_write_sep (sep 1 (by decide) 3 (by decide) (by decide)),
        readW_write_sep (sep 1 (by decide) 2 (by decide) (by decide)), Mem.readW_writeW_self32]; rfl
    · rw [readW_write_sep (sep 2 (by decide) 3 (by decide) (by decide)), Mem.readW_writeW_self32]; rfl
    · rw [Mem.readW_writeW_self32]; rfl
  have argsK : ∀ i < 5, s₆.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => by
    rw [u₆.mem]
    exact f₅.readW (arg_contains s₀ hp.espFit hi) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.argsScr.sub_right (VG.Offset.sub_base _ (by slot_omega))) (by decide)
  have esp₆ : s₆.gpr .esp = s₀.gpr .esp := by rw [u₆.other _ (by decide), g₅, vals _ (by decide)]
  have rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine wp_arg hp esp₆ (by rw [rd₆, wr₆]) argsK (by decide) fun s₇ u₇ => ?_
  have b₇ : s₇.gpr sb = (S s₀) := by rw [u₇.other _ (by decide), u₆.gpr, g₅]; exact b₁
  rw [← List.append_nil (c.opsCode _)]
  refine opsCode_wp c (ws := [.chn]) (fun o ho => ?_) (ivAreasOk hp b₇ u₇.gpr (by rw [u₇.rd, rd₆])
    (by rw [u₇.wr, wr₆]) (fun l hl e => by simp at hl; subst hl; cases e)) fun s₈ a₈ f₈ g₈ rd₈ wr₈ => ?_
  · simp only [copyBlk, List.mem_map, List.mem_range] at ho
    obtain ⟨w, hw, rfl⟩ := ho
    exact ⟨⟨by simp [Op.width]; omega, by simp [Op.width]; omega, fun _ _ h => by cases h⟩, List.mem_singleton_self _⟩
  refine WP.block_nil ⟨by rw [g₈ _ (by decide) (by decide)]; exact b₇,
    by rw [g₈ _ (by decide) (by decide), u₇.other _ (by decide), esp₆], by rw [rd₈, u₇.rd, rd₆],
    by rw [wr₈, u₇.wr, wr₆], fun i hi => ?_, ?_, ?_⟩
  · rw [← sv₅ i hi, ← u₆.mem, ← u₇.mem]
    exact f₈.readW (Region.contains_self _ _) (fun r hr => by
      simp only [areaRegions, ivAreas, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega)) (by decide)
  · refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    have e := a₈ .chn i hi
    simp only [cont, ivAreas] at e
    rw [e, copyBlk_apply (by decide), ite_eq_left ⟨rfl, hi⟩, u₇.mem, u₆.mem]
    exact f₅.bytes (R := ivR s₀ c) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.ivScr.sub_right (VG.Offset.sub_base _ (by slot_omega))) (by show 4 * c.bw ≤ 2 ^ 64; omega) hi
  · refine f₅.trans ?_
    rw [← u₆.mem, ← u₇.mem]
    refine f₈.sub fun r hr => ?_
    simp only [areaRegions, ivAreas, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨_, List.mem_singleton_self _, VG.Offset.sub _ (by slot_omega) (by slot_omega)⟩

/-! ## The exit -/

theorem restore_wp {s₀ t : State} (hp : SeqPre c M s₀) (hb : t.gpr sb = S s₀)
    (hrw : t.rd ++ t.wr = s₀.rd ++ s₀.wr)
    (hsv : ∀ i < 4, t.mem.readW (slotA (S s₀) (c.savedSlot i)) 32 = s₀.gpr (Core.savedRegs.getD i .ebx))
    {Q : State → Prop}
    (k : ∀ t', (∀ r ∈ calleeSaved, r ≠ .esp → t'.gpr r = s₀.gpr r) → t'.gpr .esp = t.gpr .esp → t'.mem = t.mem →
      Q t') :
    WP isa (.block c.restore) t Q := by
  have hL := hp.layout
  have hfit := hp.scr.fit
  have hroom := hL.room
  have slotR : ∀ i < 4, InRegions (t.rd ++ t.wr) (addr (S s₀) (4 * c.savedSlot i)) 4 := fun i hi =>
    ⟨_, by rw [hrw]; exact List.mem_append_right _ hp.scr.wr, by
      rw [addr_eq (by slot_omega)]; exact slot_contains hfit (by slot_omega)⟩
  have aS : ∀ i < 4, addr (S s₀) (4 * c.savedSlot i) = slotA (S s₀) (c.savedSlot i) := fun i hi =>
    addr_slotA hfit (by slot_omega)
  simp only [Core.restore, slotAt, at_]
  refine wp_ldm hb (slotR 0 (by decide)) fun t₁ u₁ => ?_
  refine wp_ldm (B := S s₀) (by rw [u₁.other _ (by decide)]; exact hb) (by rw [u₁.rd, u₁.wr]; exact slotR 1 (by decide))
    fun t₂ u₂ => ?_
  refine wp_ldm (B := S s₀) (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact hb)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact slotR 3 (by decide)) fun t₃ u₃ => ?_
  refine wp_ldm (B := S s₀) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact hb)
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact slotR 2 (by decide)) fun t₄ u₄ => WP.block_nil ?_
  have mm : t₃.mem = t.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine k t₄ (fun r hr hne => ?_) (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
    u₁.other _ (by decide)]) (by rw [u₄.mem, mm])
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, aS 0 (by decide),
      hsv 0 (by decide)]; rfl
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, aS 1 (by decide), hsv 1 (by decide)]; rfl
  · rw [show sb = .edi from rfl] at u₄
    rw [u₄.gpr, mm, aS 2 (by decide), hsv 2 (by decide)]; rfl
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, aS 3 (by decide), hsv 3 (by decide)]; rfl
  · exact absurd rfl hne

/-! ## The setup -/

theorem chunksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {D : BitVec 32} {st n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint (dataRegion D st n) r) (hn : st * n ≤ 2 ^ 64) :
    chunksAt st m' (D.setWidth 64) n = chunksAt st m (D.setWidth 64) n := by
  refine List.map_congr_left fun j hj => List.map_congr_left fun u hu => ?_
  have hj := List.mem_range.mp hj
  have hu := List.mem_range.mp hu
  have : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  rw [VG.Offset.add_add]
  exact hf.bytes (R := dataRegion D st n) hd hn (by show st * j + u < st * n; omega)

/-- The inputs: the data's steps and the IV, on entry. -/
abbrev xs0 (M : Mode) (s₀ : State) : List (List Byte) := chunksAt M.step s₀.mem ((Dp s₀).setWidth 64) (N s₀)
abbrev iv0 (c : Core) (s₀ : State) : List Byte := bytesAt s₀.mem ((P s₀).setWidth 64) (4 * c.bw)

/-- After the setup, at the loop. -/
structure SetUp (cs : CoreSpec c) (M : Mode) (F : StepFn) (k : cs.Key) (s₀ s : State) : Prop where
  fixed : Fixed c s (S s₀) (Dp s₀) (N s₀) M.step
  inv : Inv cs s (S s₀) (Dp s₀) (N s₀) M.step k F (iv0 c s₀) (xs0 M s₀) 0 s
  zf : s.zf = some (decide (N s₀ = 0))
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : ∀ i < 4, s.mem.readW (slotA (S s₀) (c.savedSlot i)) 32 = s₀.gpr (Core.savedRegs.getD i .ebx)
  frame : Frame [modeR c (S s₀), coreRegion c (S s₀), stkRegion (E s₀) c.stack] s₀.mem s.mem

theorem setup_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {k : cs.Key} (hp : SeqPre c M s₀)
    (hk : cs.KeyArgs s₀ [scrR s₀ c] k) :
    WP isa (.seq (.block (c.entry ++ c.ivIn)) (.seq c.prepare (.block c.args))) s₀ (SetUp cs M F k s₀) := by
  have hL := hp.layout
  have hfit := hp.scr.fit
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega
  have hbG : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hL.G_pos
  have modeScr : Region.Sub (modeR c (S s₀)) (scrR s₀ c) := VG.Offset.sub_base _ (by omega)
  have coreScr : Region.Sub (coreRegion c (S s₀)) (scrR s₀ c) := Region.sub_prefix (by omega)
  refine WP.seq (WP.mono (entry_wp hp) fun s₁ h₁ => ?_)
  have hS₁ : ScrIn s₁ (S s₀) c.total := ⟨by rw [h₁.wr]; exact hp.scr.wr, hfit⟩
  refine WP.seq (WP.mono (cs.prepare_wp h₁.b hS₁ List.mem_cons_self
    (cs.keyArgs_congr hk h₁.esp h₁.rd h₁.wr (h₁.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, modeScr⟩))
    (by rw [h₁.esp]; exact hp.stack)) fun s₂ ⟨ready₂, b₂, esp₂, f₂, rd₂, wr₂⟩ => ?_)
  rw [h₁.esp] at f₂
  have esp₂' : s₂.gpr .esp = s₀.gpr .esp := by rw [esp₂, h₁.esp]
  have f₀₂ : Frame [modeR c (S s₀), coreRegion c (S s₀), stkRegion (E s₀) c.stack] s₀.mem s₂.mem :=
    (h₁.frame.mono (by simp)).trans (f₂.mono (by simp))
  have argsOut : ∀ r ∈ [modeR c (S s₀), coreRegion c (S s₀), stkRegion (E s₀) c.stack], Region.Disjoint (argsR s₀) r :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.argsScr.sub_right modeScr
      · exact hp.argsScr.sub_right coreScr
      · exact hp.stkArgs.symm
  have argsK : ∀ {m : Mem}, Frame [modeR c (S s₀), coreRegion c (S s₀), stkRegion (E s₀) c.stack] s₀.mem m →
      ∀ i < 5, m.readW (argAddr s₀ i) 32 = arg s₀ i := fun h i hi =>
    h.readW (arg_contains s₀ hp.espFit hi) argsOut (by decide)
  have hd : c.dSlot < c.total := by slot_omega
  have hn : c.nSlot < c.total := by slot_omega
  have dIn : (modeR c (S s₀)).Contains (slotA (S s₀) c.dSlot) (32 / 8) :=
    VG.Offset.contains _ (by slot_omega) (by slot_omega) (by omega)
  have nIn : (modeR c (S s₀)).Contains (slotA (S s₀) c.nSlot) (32 / 8) :=
    VG.Offset.contains _ (by slot_omega) (by slot_omega) (by omega)
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [rd₂, wr₂, h₁.rd, h₁.wr]
  have hS₂ : ScrIn s₂ (S s₀) c.total := ⟨by rw [wr₂]; exact hS₁.wr, hfit⟩
  simp only [Core.args, slotAt, at_]
  refine wp_arg hp esp₂' rw₂ (argsK f₀₂) (by decide) fun s₃ u₃ => ?_
  refine wp_stm (B := S s₀) (by rw [u₃.other _ (by decide)]; exact b₂)
    (by rw [u₃.wr]; exact slot_inW hS₂ hd) fun s₄ u₄ => ?_
  have m₄ : s₄.mem = s₂.mem.writeW (slotA (S s₀) c.dSlot) (arg s₀ 2) := by
    rw [u₄.mem, u₃.mem, u₃.gpr, addr_slotA hfit hd]
  have f₀₄ : Frame [modeR c (S s₀), coreRegion c (S s₀), stkRegion (E s₀) c.stack] s₀.mem s₄.mem := by
    rw [m₄]; exact f₀₂.writeW List.mem_cons_self _ dIn
  refine wp_arg hp (by rw [u₄.gpr, u₃.other _ (by decide), esp₂']) (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rw₂])
    (argsK f₀₄) (by decide) fun s₅ u₅ => ?_
  refine wp_stm (B := S s₀) (by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide)]; exact b₂)
    (by rw [u₅.wr, u₄.wr, u₃.wr]; exact slot_inW hS₂ hn) fun s₆ u₆ => ?_
  refine wp_test fun s₇ f₇ z₇ => WP.block_nil ?_
  have m₇ : s₇.mem = (s₂.mem.writeW (slotA (S s₀) c.dSlot) (arg s₀ 2)).writeW (slotA (S s₀) c.nSlot) (arg s₀ 3) := by
    rw [f₇.mem, u₆.mem, u₅.mem, u₅.gpr, addr_slotA hfit hn, m₄]
  have g₇ : ∀ r, r ≠ .eax → s₇.gpr r = s₂.gpr r := fun r h => by
    rw [f₇.gpr, u₆.gpr, u₅.other r h, u₄.gpr, u₃.other r h]
  have eax₇ : s₇.gpr .eax = arg s₀ 3 := by rw [f₇.gpr, u₆.gpr, u₅.gpr]
  have rd₇ : s₇.rd = s₀.rd := by rw [f₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, h₁.rd]
  have wr₇ : s₇.wr = s₀.wr := by rw [f₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, h₁.wr]
  have esp₇ : s₇.gpr .esp = s₀.gpr .esp := by rw [g₇ _ (by decide), esp₂']
  have b₇ : s₇.gpr sb = S s₀ := by rw [g₇ _ (by decide)]; exact b₂
  have fdn : Frame (dnSlots c (S s₀)) s₂.mem s₇.mem := by
    rw [m₇]
    have h1 : (⟨slotA (S s₀) c.dSlot, 4⟩ : Region).Contains (slotA (S s₀) c.dSlot) (32 / 8) :=
      Region.contains_self _ _
    have h2 : (⟨slotA (S s₀) c.nSlot, 4⟩ : Region).Contains (slotA (S s₀) c.nSlot) (32 / 8) :=
      Region.contains_self _ _
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ h1).writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ h2
  have f₀₇ : Frame [modeR c (S s₀), coreRegion c (S s₀), stkRegion (E s₀) c.stack] s₀.mem s₇.mem := by
    rw [m₇]; exact f₀₄.writeW List.mem_cons_self _ nIn |> fun h => by rw [← m₄]; exact h
  have hF : Fixed c s₇ (S s₀) (Dp s₀) (N s₀) M.step :=
    ⟨⟨by rw [wr₇]; exact hp.scr.wr, hfit⟩, by rw [wr₇]; exact hp.dataW, hp.dataFit, hp.dataScr,
      by rw [esp₇]; exact hp.stkData, by rw [esp₇]; exact hp.stkMode, by rw [esp₇]; exact hp.stack, hp.step, hL⟩
  have sChn : Region.Sub (chnRegion c (S s₀)) (modeR c (S s₀)) := VG.Offset.sub _ (by slot_omega) (by slot_omega)
  have dn : Region.Disjoint ⟨slotA (S s₀) c.dSlot, 4⟩ ⟨slotA (S s₀) c.nSlot, 4⟩ :=
    VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega)
  have dnOut : ∀ r ∈ dnSlots c (S s₀), Region.Disjoint (coreRegion c (S s₀)) r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Offset.base_disjoint _ (by slot_omega) (by slot_omega)
    · exact VG.Offset.base_disjoint _ (by slot_omega) (by slot_omega)
  -- A slot of the mode outside the slots of the data pointer and the count.
  have keepSlot : ∀ {R : Region}, Region.Sub R (modeR c (S s₀)) → (∀ r ∈ dnSlots c (S s₀), R.Disjoint r) →
      R.len ≤ 2 ^ 64 → ∀ {i}, i < R.len → s₇.mem (R.base + BitVec.ofNat 64 i) = s₁.mem (R.base + BitVec.ofNat 64 i) :=
    fun hsub hd hl _ hi => by
      rw [fdn.bytes hd hl hi]
      refine f₂.bytes (fun r hr => ?_) hl hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (VG.Offset.disjoint_base _ (by slot_omega) (by omega)).sub_left hsub
      · exact (hp.stkMode.symm.sub_left hsub)
  refine ⟨hF, ⟨b₇, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, Frame.refl _ _⟩, ?_, esp₇, rd₇, wr₇, fun i hi => ?_, f₀₇⟩
  · rw [m₇, readW_write_sep dn, Mem.readW_writeW_self32, Nat.mul_zero]
    exact (BitVec.add_zero _).symm
  · rw [m₇, Mem.readW_writeW_self32, Nat.sub_zero]
    simp only [N, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · exact cs.ready_frame ready₂ (by rw [esp₇, esp₂']) (by rw [rd₇, rd₂, h₁.rd]) (by rw [wr₇, wr₂, h₁.wr]) fdn
      (fun r hr => ⟨_, by rw [wr₂, h₁.wr]; exact hp.scr.wr, by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact VG.Offset.sub_base _ (by slot_omega)
        · exact VG.Offset.sub_base _ (by slot_omega)⟩)
      (fun r hr => .inl (dnOut r hr))
  · rw [chunksAt_frame f₀₇ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.dataScr.sub_right modeScr
      · exact hp.dataScr.sub_right coreScr
      · exact hp.stkData.symm) (by have := hp.dataFit; omega)]
    simp only [List.take_zero, run, List.nil_append, List.drop_zero]
  · simp only [List.take_zero, run]
    rw [iv0, ← h₁.chn]
    refine List.map_congr_left fun i hi => keepSlot sChn (fun r hr => ?_) (by show 4 * c.bw ≤ 2 ^ 64; omega)
      (List.mem_range.mp hi)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Offset.disjoint _ (.inr (by slot_omega)) (by slot_omega) (by slot_omega)
    · exact VG.Offset.disjoint _ (.inr (by slot_omega)) (by slot_omega) (by slot_omega)
  · rw [z₇, u₆.gpr, u₅.gpr, BitVec.and_self]
    refine congrArg some (Bool.eq_iff_iff.mpr ?_)
    rw [beq_iff_eq, decide_eq_true_iff]
    exact ⟨fun h => by simp only [N, h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
  · rw [← h₁.saved i hi]
    exact Mem.readW_congr fun u hu => keepSlot (R := ⟨slotA (S s₀) (c.savedSlot i), 4⟩)
      (VG.Offset.sub _ (by slot_omega) (by slot_omega)) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega)
        · exact VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega))
      (by show 4 ≤ 2 ^ 64; omega) (by simpa using hu)

/-! ## The function -/

theorem seq_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {k : cs.Key} (hp : SeqPre c M s₀)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c M.step)) (hpost : ∀ o ∈ M.post, o.InBounds (lens c M.step))
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F) (hk : cs.KeyArgs s₀ [scrR s₀ c] k) :
    WP isa (c.seq M) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt M.step s'.mem ((Dp s₀).setWidth 64) (N s₀) = (run F (iv0 c s₀) (xs0 M s₀)).1 ∧
      (M.ivOut = true → bytesAt s'.mem ((P s₀).setWidth 64) (4 * c.bw) = (run F (iv0 c s₀) (xs0 M s₀)).2) := by
  have hL := hp.layout
  have hfit := hp.scr.fit
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hbw : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega
  have hbG : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hL.G_pos
  have modeScr : Region.Sub (modeR c (S s₀)) (scrR s₀ c) := VG.Offset.sub_base _ (by omega)
  have coreScr : Region.Sub (coreRegion c (S s₀)) (scrR s₀ c) := Region.sub_prefix (by omega)
  have dnScr : Region.Sub (dnRegion c (S s₀)) (scrR s₀ c) := VG.Offset.sub_base _ (by slot_omega)
  have hlen : (xs0 M s₀).length = N s₀ := chunksAt_length _ _ _ _
  have hsu := setup_wp cs (F := F) hp hk
  rw [WP.seq_iff] at hsu
  unfold Core.seq
  refine WP.seq (WP.mono hsu fun s₁ h₁ => ?_)
  rw [WP.seq_iff] at h₁
  refine WP.seq (WP.mono h₁ fun s₂ h₂ => WP.seq (WP.mono h₂ fun s₃ h₃ => ?_))
  refine WP.seq (WP.mono (loop_wp cs h₃.fixed rfl hpre hpost hcomp hlen h₃.inv h₃.zf) fun s₄ h₄ => ?_)
  -- What the run so far changed.
  have big₀ : ∀ {R : Region}, (∀ r ∈ [modeR c (S s₀), coreRegion c (S s₀), stkRegion (E s₀) c.stack] ++
      big c (S s₀) (Dp s₀) (N s₀) M.step (E s₀), R.Disjoint r) → R.len ≤ 2 ^ 64 → ∀ {i}, i < R.len →
      s₄.mem (R.base + BitVec.ofNat 64 i) = s₀.mem (R.base + BitVec.ofNat 64 i) := fun hd hl _ hi => by
    have f := h₄.frame
    rw [h₃.esp] at f
    rw [f.bytes (fun r hr => hd r (List.mem_append_right _ hr)) hl hi]
    exact h₃.frame.bytes (fun r hr => hd r (List.mem_append_left _ hr)) hl hi
  have bigScr : ∀ {R : Region}, R.Disjoint (scrR s₀ c) → R.Disjoint (stkRegion (E s₀) c.stack) →
      R.Disjoint (dataRegion (Dp s₀) M.step (N s₀)) →
      ∀ r ∈ [modeR c (S s₀), coreRegion c (S s₀), stkRegion (E s₀) c.stack] ++
        big c (S s₀) (Dp s₀) (N s₀) M.step (E s₀), R.Disjoint r := fun h1 h2 h3 r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1.sub_right modeScr
    · exact h1.sub_right coreScr
    · exact h2
    · exact h1.sub_right coreScr
    · exact h1.sub_right dnScr
    · exact h3
    · exact h2
  have b₄ : s₄.gpr sb = S s₀ := h₄.b
  have esp₄ : s₄.gpr .esp = s₀.gpr .esp := by rw [h₄.esp, h₃.esp]
  have rw₄ : s₄.rd ++ s₄.wr = s₀.rd ++ s₀.wr := by rw [h₄.rd, h₄.wr, h₃.rd, h₃.wr]
  have sv₄ : ∀ i < 4, s₄.mem.readW (slotA (S s₀) (c.savedSlot i)) 32 = s₀.gpr (Core.savedRegs.getD i .ebx) :=
    fun i hi => by
      rw [← h₃.saved i hi]
      refine h₄.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact VG.Offset.disjoint_base _ (by slot_omega) (by slot_omega)
      · exact VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega)
      · exact (hp.dataScr.sub_right (VG.Offset.sub_base _ (by slot_omega))).symm
      · rw [h₃.esp]; exact (hp.stkMode.sub_right (VG.Offset.sub _ (by slot_omega) (by slot_omega))).symm
  have ret₄ : s₄.mem.readW ((s₀.gpr .esp).setWidth 64) 32 = s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32 :=
    Mem.readW_congr fun u hu => big₀ (R := retR s₀) (bigScr hp.retScr hp.stkRet.symm hp.retData)
      (by show 4 ≤ 2 ^ 64; omega) (by simpa using hu)
  have data₄ : chunksAt M.step s₄.mem ((Dp s₀).setWidth 64) (N s₀) = (run F (iv0 c s₀) (xs0 M s₀)).1 := by
    rw [h₄.data, List.take_of_length_le (by omega), List.drop_of_length_le (by omega), List.append_nil]
  have abi : ∀ t : State, (∀ r ∈ calleeSaved, r ≠ .esp → t.gpr r = s₀.gpr r) → t.gpr .esp = s₀.gpr .esp →
      t.mem.readW ((s₀.gpr .esp).setWidth 64) 32 = s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32 →
      abiPreserved s₀ t := fun t hg he hm => ⟨fun r hr => by
        by_cases h : r = .esp
        · subst h; exact he
        · exact hg r hr h, hm⟩
  cases hiv : M.ivOut
  · rw [show (if false = true then c.ivBack else []) ++ c.restore = c.restore by simp]
    refine restore_wp hp b₄ rw₄ sv₄ fun t g e m => ⟨abi t g (by rw [e, esp₄]) (by rw [m, ret₄]), by rw [m, data₄],
      fun h => by cases h⟩
  · rw [show (if true = true then c.ivBack else []) ++ c.restore =
      .mov .esi (.mem (argOp 1)) :: (c.opsCode (copyBlk c.bw .dat .chn) ++ c.restore) by simp [Core.ivBack]]
    have argsOut : ∀ r ∈ big c (S s₀) (Dp s₀) (N s₀) M.step (E s₀), Region.Disjoint (argsR s₀) r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.argsScr.sub_right coreScr
      · exact hp.argsScr.sub_right dnScr
      · exact hp.argsData
      · exact hp.stkArgs.symm
    have argsOut₀ : ∀ r ∈ [modeR c (S s₀), coreRegion c (S s₀), stkRegion (E s₀) c.stack],
        Region.Disjoint (argsR s₀) r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.argsScr.sub_right modeScr
      · exact hp.argsScr.sub_right coreScr
      · exact hp.stkArgs.symm
    have argsK : ∀ i < 5, s₄.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => by
      have f := h₄.frame
      rw [h₃.esp] at f
      rw [f.readW (arg_contains s₀ hp.espFit hi) argsOut (by decide),
        h₃.frame.readW (arg_contains s₀ hp.espFit hi) argsOut₀ (by decide)]
      rfl
    refine wp_arg hp esp₄ rw₄ argsK (by decide) fun s₅ u₅ => ?_
    have b₅ : s₅.gpr sb = S s₀ := by rw [u₅.other _ (by decide)]; exact b₄
    refine opsCode_wp c (ws := [.dat]) (fun o ho => ?_) (ivAreasOk hp b₅ u₅.gpr (by rw [u₅.rd, h₄.rd, h₃.rd])
      (by rw [u₅.wr, h₄.wr, h₃.wr]) (fun _ _ _ => hp.ivWr hiv)) fun s₆ a₆ f₆ g₆ rd₆ wr₆ => ?_
    · simp only [copyBlk, List.mem_map, List.mem_range] at ho
      obtain ⟨w, hw, rfl⟩ := ho
      exact ⟨⟨by simp [Op.width]; omega, by simp [Op.width]; omega, fun _ _ h => by cases h⟩,
        List.mem_singleton_self _⟩
    rw [u₅.mem] at a₆ f₆
    have ivOnly : ∀ {R : Region}, R.Disjoint (ivR s₀ c) → ∀ r ∈ areaRegions (fun _ => 4 * c.bw)
        (ivAreas c (P s₀) (S s₀)) [.dat], R.Disjoint r := fun h r hr => by
      simp only [areaRegions, ivAreas, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact h
    have sv₆ : ∀ i < 4, s₆.mem.readW (slotA (S s₀) (c.savedSlot i)) 32 = s₀.gpr (Core.savedRegs.getD i .ebx) :=
      fun i hi => by
        rw [← sv₄ i hi]
        exact f₆.readW (Region.contains_self _ _)
          (ivOnly (hp.ivScr.sub_right (VG.Offset.sub_base _ (by slot_omega))).symm) (by decide)
    refine restore_wp hp (by rw [g₆ _ (by decide) (by decide)]; exact b₅)
      (by rw [rd₆, wr₆, u₅.rd, u₅.wr, rw₄]) sv₆ fun t g e m => ⟨abi t g ?_ ?_, ?_, fun _ => ?_⟩
    · rw [e, g₆ _ (by decide) (by decide), u₅.other _ (by decide), esp₄]
    · rw [m, f₆.readW (Region.contains_self _ _) (ivOnly (hp.retIv hiv)) (by decide), ret₄]
    · rw [m, chunksAt_frame f₆ (ivOnly (hp.ivData hiv).symm) (by have := hp.dataFit; omega), data₄]
    · rw [m]
      have hc := h₄.chn
      rw [List.take_of_length_le (by omega)] at hc
      rw [← hc]
      refine List.map_congr_left fun i hi => ?_
      have hi := List.mem_range.mp hi
      have e₆ := a₆ .dat i hi
      simp only [cont, ivAreas] at e₆
      rw [e₆, copyBlk_apply (by decide), ite_eq_left ⟨rfl, hi⟩]
      rfl

end VG.Proof.Modes.X86
