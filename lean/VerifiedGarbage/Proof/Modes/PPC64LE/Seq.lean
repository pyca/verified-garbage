module

public import VerifiedGarbage.Proof.Modes.PPC64LE.Step
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# A mode on PPC64LE, for any core: the whole function

`seq_wp`: `c.seq M`, for a core `c` with `CoreSpec c` and a mode `M` whose
operations compute the step function `F` (`Computes`), with its arguments in
registers (`f(key = r3, iv = r4, data = r5, n = r6, scratch = r7)`),
replaces the `n` steps of data at `data` with the outputs of `F` from the
IV, and (if `M.ivOut`) the IV with the last chaining value; it keeps the
registers the caller expects preserved, the stack pointer and the return
address. Each mode's and cipher's contract follows from it.
-/

@[expose] public section

namespace VG.Proof.Modes.PPC64LE

open VG VG.PPC64LE VG.Impl.Modes VG.Impl.Modes.PPC64LE
open VG.Spec.Aes (bytesAt)

variable {c : Core} {M : Mode}

section
variable (s₀ : State)

abbrev P : Addr := s₀.gpr .r4
abbrev Dp : Addr := s₀.gpr .r5
abbrev N : Nat := (s₀.gpr .r6).toNat
abbrev S : Addr := s₀.gpr .r7

abbrev ivR (c : Core) : Region := ⟨P s₀, 4 * c.bw⟩

end

/-- What the function needs on entry: the IV readable (and writable, apart
from the data, if the mode writes it back), the data and the scratch buffer
writable, none wrapping around, and the scratch buffer apart from the IV and
the data. -/
structure SeqPre (c : Core) (M : Mode) (s₀ : State) : Prop where
  scr : ScrIn s₀ (S s₀) c.total
  ivRd : ivR s₀ c ∈ s₀.rd ++ s₀.wr
  ivWr : M.ivOut = true → ivR s₀ c ∈ s₀.wr
  ivFit : (P s₀).toNat + 4 * c.bw ≤ 2 ^ 64
  dataW : dataRegion (Dp s₀) M.step (N s₀) ∈ s₀.wr
  dataFit : (Dp s₀).toNat + M.step * N s₀ ≤ 2 ^ 64
  dataScr : Region.Disjoint (dataRegion (Dp s₀) M.step (N s₀)) (scrRegion c (S s₀))
  ivScr : Region.Disjoint (ivR s₀ c) (scrRegion c (S s₀))
  ivData : M.ivOut = true → Region.Disjoint (ivR s₀ c) (dataRegion (Dp s₀) M.step (N s₀))
  step : 0 < M.step ∧ M.step ≤ 4 * c.bw
  layout : Layout c

/-! ## Instructions -/

theorem range3_map {α : Type} (f : Nat → α) : (List.range 3).map f = [f 0, f 1, f 2] := rfl

theorem wp_mflr {is : List Instr} {s : State} {Q : State → Prop} {d : Reg}
    (k : ∀ s', Upd s s' d s.lr → WP isa (.block is) s' Q) : WP isa (.block (.mflr d :: is)) s Q :=
  WP.cons exec_mflr (k _ (Upd.write _ _ _))

theorem wp_mtlr {is : List Instr} {s : State} {Q : State → Prop} {r : Reg}
    (k : WP isa (.block is) { s with lr := s.gpr r } Q) : WP isa (.block (.mtlr r :: is)) s Q :=
  WP.cons exec_mtlr k

/-- `Q` of the state after `c`, which may assume `c` kept the stack pointer
(`Exec.sp`). -/
theorem WP.sp_intro {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa c s fun s' => s'.sp = s.sp → Q s') : WP isa c s Q := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq (Exec.sp he)⟩

theorem readW_sep64 {m : Mem} {a b : Addr} {v : BitVec 64} (h : Region.Disjoint ⟨a, 8⟩ ⟨b, 8⟩) :
    (m.writeW b v).readW a 64 = m.readW a 64 :=
  Mem.readW_writeW_sep (fun x h1 h2 => h x (by simp only [Region.Contains]; omega_using [h1])
    (by simp only [Region.Contains]; omega_using [h2])) (by decide)

/-! ## The slots -/

/-- The mode's slots. -/
abbrev modeR (c : Core) (B : Addr) : Region := ⟨slotA B c.slots, 48⟩

/-- `omega_arith`, with the mode's slots unfolded. -/
local macro "slot_omega" : tactic =>
  `(tactic| plain_simp_names ((try simp only [Core.chnSlot, Core.lrSlot, Core.savedSlot]); omega_arith))

theorem buf_le4 (hL : Layout c) : 8 * c.buf + 4 * c.bw ≤ 8 * c.slots :=
  Nat.le_trans (Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hL.G_pos) _) hL.buf_le

theorem bw_le (hL : Layout c) : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_using [h]

/-- Two different slots are apart. -/
theorem slot_sep {B : Addr} {total i j : Nat} (ht : 8 * total < 2 ^ 15) (hi : i < total) (hj : j < total)
    (hne : i ≠ j) : Region.Disjoint ⟨slotA B i, 8⟩ ⟨slotA B j, 8⟩ :=
  VG.Offset.disjoint _ (by omega_using [hne]) (by omega_using [ht, hi]) (by omega_using [ht, hj])

/-- A slot of the scratch buffer is writable. -/
theorem slot_inW {s : State} {B : Addr} {total k : Nat} (hS : ScrIn s B total) (ht : 8 * total < 2 ^ 15)
    (hk : k < total) : InRegions s.wr (slotA B k) 8 :=
  ⟨_, hS.wr, slot_contains ht (by omega_using [hk])⟩

/-- A slot of the scratch buffer is readable. -/
theorem slot_in {s : State} {B : Addr} {total k : Nat} (hS : ScrIn s B total) (ht : 8 * total < 2 ^ 15)
    (hk : k < total) : InRegions (s.rd ++ s.wr) (slotA B k) 8 :=
  ⟨_, List.mem_append_right _ hS.wr, slot_contains ht (by omega_using [hk])⟩

/-- A slot of the mode, in its slots. -/
theorem slot_mode {B : Addr} {i : Nat} (hL : Layout c) (hi : c.slots ≤ i) (hi' : i + 1 ≤ c.slots + 6) :
    (modeR c B).Contains (slotA B i) (64 / 8) :=
  VG.Offset.contains _ (by omega_using [hi]) (by omega_using [hi']) (by have := hL.disp; have := hL.room; omega_arith)

/-! ## The IV's copies -/

/-- The areas of the IV's copies: the IV as the data. -/
def ivAreas (c : Core) (P B : Addr) : Loc → Addr
  | .dat => P
  | .chn => slotA B c.chnSlot
  | .buf => slotA B c.buf

theorem ivAreasOk {s₀ s : State} (hp : SeqPre c M s₀) (hb : s.gpr sb = S s₀) (h31 : s.gpr .r31 = P s₀)
    (hrd : s.rd = s₀.rd) (hw : s.wr = s₀.wr) {ws : List Loc} (hws : ∀ l ∈ ws, l = .dat → ivR s₀ c ∈ s₀.wr) :
    AreasOk c s (fun _ => 4 * c.bw) (ivAreas c (P s₀) (S s₀)) ws := by
  have hL := hp.layout
  have hroom := hL.room
  have hdisp := hL.disp
  have hbw := bw_le hL
  have hb4 := buf_le4 hL
  have hP := hp.ivFit
  have inScr : ∀ d w, d + w ≤ 8 * c.total → InRegions s₀.wr (S s₀ + BitVec.ofNat 64 d) w :=
    fun d w h => ⟨_, hp.scr.wr, slot_contains hdisp h⟩
  refine ⟨fun l off ho => ?_, fun l off ho => ?_, fun l off w hw0 ho => ?_, fun l hl off w hw0 ho => ?_,
    fun l l' hne => ?_, fun _ => by omega_arith⟩
  · cases l
    · simp only [Core.loc, ivAreas] at ho ⊢; rw [h31, Nat.zero_add]
    · simp only [Core.loc, ivAreas] at ho ⊢; rw [hb, VG.Offset.add_add]
    · simp only [Core.loc, ivAreas] at ho ⊢; rw [hb, VG.Offset.add_add]
  · cases l <;> simp only [Core.loc] at ho ⊢ <;> slot_omega
  · rw [hrd, hw]
    cases l
    · exact ⟨_, hp.ivRd, VG.Offset.contains_base _ ho (by omega_arith)⟩
    · obtain ⟨r, hr, hc⟩ := inScr (8 * c.chnSlot + off) w (by slot_omega)
      refine ⟨r, List.mem_append_right _ hr, ?_⟩
      simp only [ivAreas]; rw [VG.Offset.add_add]; exact hc
    · obtain ⟨r, hr, hc⟩ := inScr (8 * c.buf + off) w (by omega_arith)
      refine ⟨r, List.mem_append_right _ hr, ?_⟩
      simp only [ivAreas]; rw [VG.Offset.add_add]; exact hc
  · rw [hw]
    cases l
    · exact ⟨_, hws _ hl rfl, VG.Offset.contains_base _ ho (by omega_arith)⟩
    · simp only [ivAreas]; rw [VG.Offset.add_add]; exact inScr _ _ (by slot_omega)
    · simp only [ivAreas]; rw [VG.Offset.add_add]; exact inScr _ _ (by omega_arith)
  · have dIv : ∀ d, d + 4 * c.bw ≤ 8 * c.total →
        Region.Disjoint (ivR s₀ c) ⟨S s₀ + BitVec.ofNat 64 d, 4 * c.bw⟩ :=
      fun d h => hp.ivScr.sub_right (slot_sub h)
    have dCB : Region.Disjoint ⟨slotA (S s₀) c.chnSlot, 4 * c.bw⟩ ⟨slotA (S s₀) c.buf, 4 * c.bw⟩ :=
      VG.Offset.disjoint _ (.inr (by slot_omega)) (by slot_omega) (by omega_arith)
    cases l <;> cases l' <;> simp only [ne_eq, not_true_eq_false] at hne <;> simp only [ivAreas]
    · exact dIv _ (by slot_omega)
    · exact dIv _ (by omega_arith)
    · exact (dIv _ (by slot_omega)).symm
    · exact dCB
    · exact (dIv _ (by omega_arith)).symm
    · exact dCB.symm

theorem copyBlk_ok {bw : Nat} {dst src : Loc} {ws : List Loc} (hd : dst ∈ ws) {len : Loc → Nat}
    (hl : ∀ l, len l = 4 * bw) : ∀ o ∈ copyBlk bw dst src, Plain o ∧ o.InBounds len ∧ o.dst ∈ ws := by
  intro o ho
  simp only [copyBlk, List.mem_map, List.mem_range] at ho
  obtain ⟨w, hw, rfl⟩ := ho
  refine ⟨⟨rfl, rfl⟩, ⟨?_, ?_, fun _ _ h => by cases h⟩, hd⟩ <;>
    simp only [Op.width, Bool.false_eq_true, ite_false, ite_true, hl] <;> omega_using [hw]

/-! ## The entry -/

/-- After the entry: the scratch buffer at `sb`, the mode's state in `r29`–`r31`,
the caller's `r29`–`r31` and the return address in their slots, the IV in
the chaining value's. -/
structure Entered (c : Core) (s₀ s : State) : Prop where
  b : s.gpr sb = S s₀
  r29 : s.gpr .r29 = P s₀
  r30 : s.gpr .r30 = s₀.gpr .r6
  r31 : s.gpr .r31 = Dp s₀
  keep : ∀ r ∈ kept, r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : ∀ i < 3, s.mem.readW (slotA (S s₀) (c.savedSlot i)) 64 = s₀.gpr (Core.savedRegs.getD i .r29)
  lr : s.mem.readW (slotA (S s₀) c.lrSlot) 64 = s₀.lr
  chn : bytesAt s.mem (slotA (S s₀) c.chnSlot) (4 * c.bw) = bytesAt s₀.mem (P s₀) (4 * c.bw)
  frame : Frame [modeR c (S s₀)] s₀.mem s.mem

/-- The registers the entry writes are not kept, but for `r29`–`r31`. -/
theorem kept_ne_entry : ∀ r ∈ kept, r ≠ .r0 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r8 ∧ r ≠ .r9 := by decide

theorem entry_wp {s₀ : State} (hp : SeqPre c M s₀) :
    WP isa (.block (c.entry ++ c.ivIn)) s₀ (Entered c s₀) := by
  have hL := hp.layout
  have hroom := hL.room
  have hdisp := hL.disp
  have hbw := bw_le hL
  have hS := hp.scr
  have hlr : c.lrSlot < c.total := by slot_omega
  have hsv : ∀ i < 3, c.savedSlot i < c.total := fun i hi => by slot_omega
  simp only [Core.entry, Core.ivIn, range3_map, Core.savedRegs, List.getD_cons_zero, List.getD_cons_succ,
    List.cons_append, List.nil_append, mov]
  refine wp_mflr fun s₁ u₁ => ?_
  refine wp_std (a := slotA (S s₀) c.lrSlot) (by decide) ⟨by slot_omega, by slot_omega⟩
    (by rw [u₁.other _ (by decide)]) (by rw [u₁.wr]; exact slot_inW hS hdisp hlr) fun s₂ u₂ => ?_
  refine wp_std (a := slotA (S s₀) (c.savedSlot 0)) (by decide) ⟨by slot_omega, by slot_omega⟩
    (by rw [u₂.gpr, u₁.other _ (by decide)]) (by rw [u₂.wr, u₁.wr]; exact slot_inW hS hdisp (hsv 0 (by decide)))
    fun s₃ u₃ => ?_
  refine wp_std (a := slotA (S s₀) (c.savedSlot 1)) (by decide) ⟨by slot_omega, by slot_omega⟩
    (by rw [u₃.gpr, u₂.gpr, u₁.other _ (by decide)])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact slot_inW hS hdisp (hsv 1 (by decide))) fun s₄ u₄ => ?_
  refine wp_std (a := slotA (S s₀) (c.savedSlot 2)) (by decide) ⟨by slot_omega, by slot_omega⟩
    (by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide)])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact slot_inW hS hdisp (hsv 2 (by decide))) fun s₅ u₅ => ?_
  have g₅ : s₅.gpr = s₁.gpr := by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]
  have v₁ : ∀ r, r ≠ .r0 → s₁.gpr r = s₀.gpr r := u₁.other
  have m₅ : s₅.mem = (((s₀.mem.writeW (slotA (S s₀) c.lrSlot) s₀.lr).writeW (slotA (S s₀) (c.savedSlot 0))
      (s₀.gpr .r29)).writeW (slotA (S s₀) (c.savedSlot 1)) (s₀.gpr .r30)).writeW (slotA (S s₀) (c.savedSlot 2))
      (s₀.gpr .r31) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr,
      v₁ .r29 (by decide), v₁ .r30 (by decide), v₁ .r31 (by decide)]
  refine wp_mr fun s₆ u₆ => wp_mr fun s₇ u₇ => wp_mr fun s₈ u₈ => wp_mr fun s₉ u₉ => wp_mr fun s₁₀ u₁₀ => ?_
  have m₁₀ : s₁₀.mem = s₅.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  have rd₁₀ : s₁₀.rd = s₀.rd := by rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₁₀ : s₁₀.wr = s₀.wr := by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have b₁₀ : s₁₀.gpr sb = S s₀ := by
    rw [show sb = .r5 from rfl] at u₁₀ ⊢
    rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      g₅, v₁ _ (by decide)]
  have r31₁₀ : s₁₀.gpr .r31 = P s₀ := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide),
      g₅, v₁ _ (by decide)]
  have r6₁₀ : s₁₀.gpr .r6 = Dp s₀ := by
    rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      g₅, v₁ _ (by decide)]
  have r29₁₀ : s₁₀.gpr .r29 = P s₀ := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr,
      g₅, v₁ _ (by decide)]
  have r30₁₀ : s₁₀.gpr .r30 = s₀.gpr .r6 := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide),
      g₅, v₁ _ (by decide)]
  have keep₁₀ : ∀ r ∈ kept, r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → s₁₀.gpr r = s₀.gpr r := fun r hr h29 h30 h31 => by
    have h := kept_ne_entry r hr
    rw [u₁₀.other r h.2.1, u₉.other r h.2.2.1, u₈.other r h31, u₇.other r h30, u₆.other r h29, g₅, v₁ r h.1]
  -- The saved values.
  have sep : ∀ i j, i < c.total → j < c.total → i ≠ j →
      Region.Disjoint ⟨slotA (S s₀) i, 8⟩ ⟨slotA (S s₀) j, 8⟩ := fun i j hi hj hne => slot_sep hdisp hi hj hne
  have sv₅ : ∀ i < 3, s₅.mem.readW (slotA (S s₀) (c.savedSlot i)) 64 = s₀.gpr (Core.savedRegs.getD i .r29) := by
    intro i hi
    rw [m₅]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega_arith) with rfl | rfl | rfl
    · rw [readW_sep64 (sep _ _ (hsv 0 (by decide)) (hsv 2 (by decide)) (by slot_omega)),
        readW_sep64 (sep _ _ (hsv 0 (by decide)) (hsv 1 (by decide)) (by slot_omega)), Mem.readW_writeW_self64]; rfl
    · rw [readW_sep64 (sep _ _ (hsv 1 (by decide)) (hsv 2 (by decide)) (by slot_omega)),
        Mem.readW_writeW_self64]; rfl
    · rw [Mem.readW_writeW_self64]; rfl
  have lr₅ : s₅.mem.readW (slotA (S s₀) c.lrSlot) 64 = s₀.lr := by
    rw [m₅, readW_sep64 (sep _ _ hlr (hsv 2 (by decide)) (by slot_omega)),
      readW_sep64 (sep _ _ hlr (hsv 1 (by decide)) (by slot_omega)),
      readW_sep64 (sep _ _ hlr (hsv 0 (by decide)) (by slot_omega)), Mem.readW_writeW_self64]
  have f₅ : Frame [modeR c (S s₀)] s₀.mem s₅.mem := by
    rw [m₅]
    exact ((((Frame.refl _ _).writeW List.mem_cons_self _ (slot_mode hL (by slot_omega) (by slot_omega))).writeW
      List.mem_cons_self _ (slot_mode hL (by slot_omega) (by slot_omega))).writeW List.mem_cons_self _
      (slot_mode hL (by slot_omega) (by slot_omega))).writeW List.mem_cons_self _
      (slot_mode hL (by slot_omega) (by slot_omega))
  -- The IV to the chaining value.
  refine opsCode_wp c (ws := [.chn]) (copyBlk_ok (List.mem_singleton_self _) fun _ => rfl)
    (ivAreasOk hp b₁₀ r31₁₀ rd₁₀ wr₁₀ (fun l hl e => by simp at hl; subst hl; cases e))
    fun s₁₁ a₁₁ f₁₁ g₁₁ rd₁₁ wr₁₁ => wp_mr fun s₁₂ u₁₂ => wp_nil ?_
  rw [m₁₀] at a₁₁ f₁₁
  have chnOnly : ∀ {R : Region}, R.Disjoint (chnRegion c (S s₀)) →
      ∀ r ∈ areaRegions (fun _ => 4 * c.bw) (ivAreas c (P s₀) (S s₀)) [.chn], R.Disjoint r := fun h r hr => by
    simp only [areaRegions, ivAreas, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h
  have g : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r31 → s₁₂.gpr r = s₁₀.gpr r := fun r h8 h9 h31 => by
    rw [u₁₂.other r h31, g₁₁ r h8 h9]
  refine ⟨by rw [g _ (by decide) (by decide) (by decide)]; exact b₁₀,
    by rw [g _ (by decide) (by decide) (by decide)]; exact r29₁₀,
    by rw [g _ (by decide) (by decide) (by decide)]; exact r30₁₀,
    by rw [u₁₂.gpr, g₁₁ _ (by decide) (by decide), r6₁₀],
    fun r hr h29 h30 h31 => by
      rw [g r (kept_ne_entry r hr).2.2.2.1 (kept_ne_entry r hr).2.2.2.2 h31, keep₁₀ r hr h29 h30 h31],
    by rw [u₁₂.rd, rd₁₁, rd₁₀], by rw [u₁₂.wr, wr₁₁, wr₁₀], fun i hi => ?_, ?_, ?_, ?_⟩
  · rw [u₁₂.mem, ← sv₅ i hi]
    exact f₁₁.readW (Region.contains_self _ _) (chnOnly
      (VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega))) (by decide)
  · rw [u₁₂.mem, ← lr₅]
    exact f₁₁.readW (Region.contains_self _ _) (chnOnly
      (VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega))) (by decide)
  · refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    have e := a₁₁ .chn i hi
    simp only [cont, ivAreas] at e
    rw [u₁₂.mem, e, copyBlk_apply (by decide), ite_eq_left ⟨rfl, hi⟩]
    exact f₅.bytes (R := ivR s₀ c) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.ivScr.sub_right (VG.Offset.sub_base _ (by slot_omega))) (by show 4 * c.bw ≤ 2 ^ 64; omega_arith) hi
  · rw [u₁₂.mem]
    refine f₅.trans (f₁₁.sub fun r hr => ?_)
    simp only [areaRegions, ivAreas, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨_, List.mem_singleton_self _, VG.Offset.sub _ (by slot_omega) (by slot_omega)⟩

/-! ## The exit -/

theorem restore_wp {s₀ t : State} (hp : SeqPre c M s₀) (hb : t.gpr sb = S s₀) (hwr : t.wr = s₀.wr)
    (hsv : ∀ i < 3, t.mem.readW (slotA (S s₀) (c.savedSlot i)) 64 = s₀.gpr (Core.savedRegs.getD i .r29))
    (hlr : t.mem.readW (slotA (S s₀) c.lrSlot) 64 = s₀.lr) {Q : State → Prop}
    (k : ∀ t', t'.gpr .r29 = s₀.gpr .r29 → t'.gpr .r30 = s₀.gpr .r30 → t'.gpr .r31 = s₀.gpr .r31 →
      t'.lr = s₀.lr → (∀ r, r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → r ≠ .r0 → t'.gpr r = t.gpr r) →
      t'.mem = t.mem → Q t') :
    WP isa (.block c.restore) t Q := by
  have hL := hp.layout
  have hroom := hL.room
  have hdisp := hL.disp
  have hS : ScrIn t (S s₀) c.total := ⟨by rw [hwr]; exact hp.scr.wr, hp.scr.fit⟩
  have hlrs : c.lrSlot < c.total := by slot_omega
  have hsv' : ∀ i < 3, c.savedSlot i < c.total := fun i hi => by slot_omega
  simp only [Core.restore, range3_map, Core.savedRegs, List.getD_cons_zero, List.getD_cons_succ,
    List.cons_append, List.nil_append]
  refine wp_ld (a := slotA (S s₀) (c.savedSlot 0)) (by decide) ⟨by slot_omega, by slot_omega⟩
    (by rw [hb]) (slot_in hS hdisp (hsv' 0 (by decide))) fun t₁ u₁ => ?_
  refine wp_ld (a := slotA (S s₀) (c.savedSlot 1)) (by decide) ⟨by slot_omega, by slot_omega⟩
    (by rw [u₁.other _ (by decide), hb]) (by rw [u₁.rd, u₁.wr]; exact slot_in hS hdisp (hsv' 1 (by decide)))
    fun t₂ u₂ => ?_
  refine wp_ld (a := slotA (S s₀) (c.savedSlot 2)) (by decide) ⟨by slot_omega, by slot_omega⟩
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hb])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact slot_in hS hdisp (hsv' 2 (by decide))) fun t₃ u₃ => ?_
  refine wp_ld (a := slotA (S s₀) c.lrSlot) (by decide) ⟨by slot_omega, by slot_omega⟩
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hb])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact slot_in hS hdisp hlrs) fun t₄ u₄ => ?_
  refine wp_mtlr (wp_nil ?_)
  have mm : t₃.mem = t.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine k _ ?_ ?_ ?_ ?_ (fun r h29 h30 h31 h0 => ?_) (by show t₄.mem = t.mem; rw [u₄.mem, mm])
  · show t₄.gpr .r29 = _
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hsv 0 (by decide)]; rfl
  · show t₄.gpr .r30 = _
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, hsv 1 (by decide)]; rfl
  · show t₄.gpr .r31 = _
    rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, hsv 2 (by decide)]; rfl
  · show t₄.gpr .r0 = _
    rw [u₄.gpr, mm, hlr]
  · show t₄.gpr r = _
    rw [u₄.other r h0, u₃.other r h31, u₂.other r h30, u₁.other r h29]

/-! ## The setup -/

theorem chunksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {D : Addr} {st n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint (dataRegion D st n) r) (hn : st * n ≤ 2 ^ 64) :
    chunksAt st m' D n = chunksAt st m D n := by
  refine List.map_congr_left fun j hj => List.map_congr_left fun u hu => ?_
  have hj := List.mem_range.mp hj
  have hu := List.mem_range.mp hu
  have : st * j + st ≤ st * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  rw [VG.Offset.add_add]
  exact hf.bytes (R := dataRegion D st n) hd hn (by show st * j + u < st * n; omega_arith)

/-- The inputs: the data's steps and the IV, on entry. -/
abbrev xs0 (M : Mode) (s₀ : State) : List (List Byte) := chunksAt M.step s₀.mem (Dp s₀) (N s₀)
abbrev iv0 (c : Core) (s₀ : State) : List Byte := bytesAt s₀.mem (P s₀) (4 * c.bw)

/-- The regions the mode writes, on entry. -/
abbrev wrs0 (c : Core) (M : Mode) (s₀ : State) : List Region := wrs c (S s₀) (Dp s₀) (N s₀) M.step

/-- After the setup, at the loop. -/
structure SetUp (cs : CoreSpec c) (M : Mode) (F : StepFn) (k : cs.Key) (s₀ s : State) : Prop where
  fixed : Fixed c s (S s₀) (Dp s₀) (N s₀) M.step
  inv : Inv cs s (S s₀) (Dp s₀) (N s₀) M.step k F (iv0 c s₀) (xs0 M s₀) 0 s
  keep : ∀ r ∈ kept, r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → s.gpr r = s₀.gpr r
  r29 : s.gpr .r29 = P s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : ∀ i < 3, s.mem.readW (slotA (S s₀) (c.savedSlot i)) 64 = s₀.gpr (Core.savedRegs.getD i .r29)
  lr : s.mem.readW (slotA (S s₀) c.lrSlot) 64 = s₀.lr
  frame : Frame [modeR c (S s₀), coreRegion c (S s₀)] s₀.mem s.mem

theorem setup_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {k : cs.Key} (hp : SeqPre c M s₀)
    (hk : cs.KeyArgs s₀ (wrs0 c M s₀) k) :
    WP isa (.seq (.block (c.entry ++ c.ivIn)) c.prepare) s₀ (SetUp cs M F k s₀) := by
  have hL := hp.layout
  have hfit := hp.scr.fit
  have hroom := hL.room
  have hdisp := hL.disp
  have hbw := bw_le hL
  have hb4 := buf_le4 hL
  have modeScr : Region.Sub (modeR c (S s₀)) (scrRegion c (S s₀)) := VG.Offset.sub_base _ (by omega_arith)
  have coreScr : Region.Sub (coreRegion c (S s₀)) (scrRegion c (S s₀)) := Region.sub_prefix (by omega_arith)
  refine WP.seq (WP.mono (entry_wp hp) fun s₁ h₁ => ?_)
  have hS₁ : ScrIn s₁ (S s₀) c.total := ⟨by rw [h₁.wr]; exact hp.scr.wr, hfit⟩
  have m1 : ∀ {a b : Region} {l : List Region}, b ∈ a :: b :: l := List.mem_cons_of_mem _ List.mem_cons_self
  refine WP.mono (cs.prepare_wp h₁.b hS₁ m1
    (cs.keyArgs_congr hk (h₁.keep _ (by decide) (by decide) (by decide) (by decide)) h₁.rd h₁.wr
      (h₁.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, m1, modeScr⟩)))
    fun s₂ ⟨ready₂, b₂, kept₂, f₂, rd₂, wr₂⟩ => ?_
  have kp : ∀ r, r ∈ kept → s₂.gpr r = s₁.gpr r := kept₂
  have f₀₂ : Frame [modeR c (S s₀), coreRegion c (S s₀)] s₀.mem s₂.mem :=
    (h₁.frame.mono (by simp)).trans (f₂.mono (by simp))
  have dataOut : ∀ r ∈ [modeR c (S s₀), coreRegion c (S s₀)],
      Region.Disjoint (dataRegion (Dp s₀) M.step (N s₀)) r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dataScr.sub_right modeScr
    · exact hp.dataScr.sub_right coreScr
  have modeOut : ∀ {R : Region}, Region.Sub R (modeR c (S s₀)) → ∀ r ∈ [coreRegion c (S s₀)], R.Disjoint r :=
    fun hsub r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (VG.Offset.disjoint_base _ (by slot_omega) (by omega_arith)).sub_left hsub
  refine ⟨⟨⟨by rw [wr₂, h₁.wr]; exact hp.scr.wr, hfit⟩, by rw [wr₂, h₁.wr]; exact hp.dataW, hp.dataFit, hp.dataScr,
      (s₀.gpr .r6).isLt, hp.step, hL⟩,
    ⟨b₂, fun _ _ _ _ => rfl, rfl, rfl, ?_, ?_, ready₂, ?_, ?_, Frame.refl _ _⟩,
    fun r hr h29 h30 h31 => by rw [kp r hr, h₁.keep r hr h29 h30 h31],
    by rw [kp _ (by decide), h₁.r29], by rw [rd₂, h₁.rd], by rw [wr₂, h₁.wr], fun i hi => ?_, ?_, f₀₂⟩
  · rw [kp _ (by decide), h₁.r31, Nat.mul_zero]; exact (BitVec.add_zero _).symm
  · rw [kp _ (by decide), h₁.r30, Nat.sub_zero]; simp only [N, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [chunksAt_frame f₀₂ dataOut (by have := hp.dataFit; omega_arith)]
    simp only [List.take_zero, run, List.nil_append, List.drop_zero]
  · simp only [List.take_zero, run]
    rw [iv0, ← h₁.chn]
    refine List.map_congr_left fun i hi => f₂.bytes (R := chnRegion c (S s₀))
      (modeOut (VG.Offset.sub _ (by slot_omega) (by slot_omega))) (by show 4 * c.bw ≤ 2 ^ 64; omega_arith)
      (List.mem_range.mp hi)
  · rw [← h₁.saved i hi]
    exact f₂.readW (Region.contains_self _ _) (modeOut (VG.Offset.sub _ (by slot_omega) (by slot_omega)))
      (by decide)
  · rw [← h₁.lr]
    exact f₂.readW (Region.contains_self _ _) (modeOut (VG.Offset.sub _ (by slot_omega) (by slot_omega)))
      (by decide)

/-! ## The function -/

theorem seq_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {k : cs.Key} (hp : SeqPre c M s₀)
    (hpre : ∀ o ∈ M.pre, Plain o ∧ o.InBounds (lens c M.step))
    (hpost : ∀ o ∈ M.post, Plain o ∧ o.InBounds (lens c M.step))
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F) (hk : cs.KeyArgs s₀ (wrs0 c M s₀) k) :
    WP isa (c.seq M) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt M.step s'.mem (Dp s₀) (N s₀) = (run F (iv0 c s₀) (xs0 M s₀)).1 ∧
      (M.ivOut = true → bytesAt s'.mem (P s₀) (4 * c.bw) = (run F (iv0 c s₀) (xs0 M s₀)).2) := by
  have hL := hp.layout
  have hfit := hp.scr.fit
  have hroom := hL.room
  have hdisp := hL.disp
  have hbw := bw_le hL
  have hb4 := buf_le4 hL
  have modeScr : Region.Sub (modeR c (S s₀)) (scrRegion c (S s₀)) := VG.Offset.sub_base _ (by omega_arith)
  have coreScr : Region.Sub (coreRegion c (S s₀)) (scrRegion c (S s₀)) := Region.sub_prefix (by omega_arith)
  have chnScr : Region.Sub (chnRegion c (S s₀)) (scrRegion c (S s₀)) := VG.Offset.sub_base _ (by slot_omega)
  have hlen : (xs0 M s₀).length = N s₀ := chunksAt_length _ _ _ _
  have hsu := setup_wp cs (F := F) hp hk
  rw [WP.seq_iff] at hsu
  refine WP.sp_intro ?_
  unfold Core.seq
  refine WP.seq (WP.mono hsu fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono h₁ fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (loop_wp cs h₃.fixed rfl hpre hpost hcomp hlen h₃.inv) fun s₄ h₄ => ?_)
  -- What the run so far changed.
  have slotOut : ∀ {R : Region}, Region.Sub R (modeR c (S s₀)) → Region.Disjoint R (chnRegion c (S s₀)) →
      ∀ r ∈ big c (S s₀) (Dp s₀) (N s₀) M.step, R.Disjoint r := fun hsub hc r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (VG.Offset.disjoint_base _ (by slot_omega) (by omega_arith)).sub_left hsub
    · exact hc
    · exact (hp.dataScr.sub_right modeScr).symm.sub_left hsub
  have sv₄ : ∀ i < 3, s₄.mem.readW (slotA (S s₀) (c.savedSlot i)) 64 = s₀.gpr (Core.savedRegs.getD i .r29) :=
    fun i hi => by
      rw [← h₃.saved i hi]
      exact h₄.frame.readW (Region.contains_self _ _) (slotOut (VG.Offset.sub _ (by slot_omega) (by slot_omega))
        (VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega))) (by decide)
  have lr₄ : s₄.mem.readW (slotA (S s₀) c.lrSlot) 64 = s₀.lr := by
    rw [← h₃.lr]
    exact h₄.frame.readW (Region.contains_self _ _) (slotOut (VG.Offset.sub _ (by slot_omega) (by slot_omega))
      (VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega))) (by decide)
  have data₄ : chunksAt M.step s₄.mem (Dp s₀) (N s₀) = (run F (iv0 c s₀) (xs0 M s₀)).1 := by
    rw [h₄.data, List.take_of_length_le (by omega_arith), List.drop_of_length_le (by omega_arith), List.append_nil]
  have keep₄ : ∀ r ∈ kept, r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → s₄.gpr r = s₀.gpr r :=
    fun r hr h29 h30 h31 => by rw [h₄.keep r hr h30 h31, h₃.keep r hr h29 h30 h31]
  have r29₄ : s₄.gpr .r29 = P s₀ := by rw [h₄.keep _ (by decide) (by decide) (by decide), h₃.r29]
  have rd₄ : s₄.rd = s₀.rd := by rw [h₄.rd, h₃.rd]
  have wr₄ : s₄.wr = s₀.wr := by rw [h₄.wr, h₃.wr]
  have abi : ∀ t : State, t.sp = s₀.sp → t.lr = s₀.lr → t.gpr .r29 = s₀.gpr .r29 → t.gpr .r30 = s₀.gpr .r30 →
      t.gpr .r31 = s₀.gpr .r31 → (∀ r ∈ kept, r ≠ .r29 → r ≠ .r30 → r ≠ .r31 → t.gpr r = s₀.gpr r) →
      abiPreserved s₀ t := fun t hsp hlr h29 h30 h31 hk => ⟨fun r hr => by
        by_cases e29 : r = .r29
        · subst e29; exact h29
        by_cases e30 : r = .r30
        · subst e30; exact h30
        by_cases e31 : r = .r31
        · subst e31; exact h31
        exact hk r (List.mem_cons_of_mem _ hr) e29 e30 e31, hsp, hlr⟩
  have ne0 : ∀ r ∈ kept, r ≠ .r0 := fun r hr => (kept_ne_entry r hr).1
  cases hiv : M.ivOut
  · rw [show (if false = true then c.ivBack else []) ++ c.restore = c.restore by simp]
    refine restore_wp hp h₄.b wr₄ sv₄ lr₄ fun t g29 g30 g31 glr g m hsp =>
      ⟨abi t hsp glr g29 g30 g31 fun r hr h29 h30 h31 => by rw [g r h29 h30 h31 (ne0 r hr), keep₄ r hr h29 h30 h31],
        by rw [m, data₄], fun h => by cases h⟩
  · rw [show (if true = true then c.ivBack else []) ++ c.restore =
      mov .r31 .r29 :: (c.opsCode (copyBlk c.bw .dat .chn) ++ c.restore) by simp [Core.ivBack]]
    refine wp_mr fun s₅ u₅ => ?_
    have b₅ : s₅.gpr sb = S s₀ := by rw [u₅.other _ (by decide)]; exact h₄.b
    refine opsCode_wp c (ws := [.dat]) (copyBlk_ok (List.mem_singleton_self _) fun _ => rfl)
      (ivAreasOk hp b₅ (by rw [u₅.gpr, r29₄]) (by rw [u₅.rd, rd₄]) (by rw [u₅.wr, wr₄])
        (fun _ _ _ => hp.ivWr hiv)) fun s₆ a₆ f₆ g₆ rd₆ wr₆ => ?_
    rw [u₅.mem] at a₆ f₆
    have ivOnly : ∀ {R : Region}, R.Disjoint (ivR s₀ c) → ∀ r ∈ areaRegions (fun _ => 4 * c.bw)
        (ivAreas c (P s₀) (S s₀)) [.dat], R.Disjoint r := fun h r hr => by
      simp only [areaRegions, ivAreas, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact h
    have scrIv : ∀ {R : Region}, Region.Sub R (scrRegion c (S s₀)) → R.Disjoint (ivR s₀ c) :=
      fun h => (hp.ivScr.sub_right h).symm
    have sv₆ : ∀ i < 3, s₆.mem.readW (slotA (S s₀) (c.savedSlot i)) 64 = s₀.gpr (Core.savedRegs.getD i .r29) :=
      fun i hi => by
        rw [← sv₄ i hi]
        exact f₆.readW (Region.contains_self _ _)
          (ivOnly (scrIv (VG.Offset.sub_base _ (by slot_omega)))) (by decide)
    have lr₆ : s₆.mem.readW (slotA (S s₀) c.lrSlot) 64 = s₀.lr := by
      rw [← lr₄]
      exact f₆.readW (Region.contains_self _ _) (ivOnly (scrIv (VG.Offset.sub_base _ (by slot_omega)))) (by decide)
    have g₆' : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r31 → s₆.gpr r = s₄.gpr r := fun r h8 h9 h31 => by
      rw [g₆ r h8 h9, u₅.other r h31]
    refine restore_wp hp (by rw [g₆' _ (by decide) (by decide) (by decide)]; exact h₄.b)
      (by rw [wr₆, u₅.wr, wr₄]) sv₆ lr₆ fun t g29 g30 g31 glr g m hsp =>
        ⟨abi t hsp glr g29 g30 g31 fun r hr h29 h30 h31 => by
          rw [g r h29 h30 h31 (ne0 r hr), g₆' r (kept_ne r hr).1 (kept_ne r hr).2 h31, keep₄ r hr h29 h30 h31],
          ?_, fun _ => ?_⟩
    · rw [m, chunksAt_frame f₆ (ivOnly (hp.ivData hiv).symm) (by have := hp.dataFit; omega_arith), data₄]
    · rw [m]
      have hc := h₄.chn
      rw [List.take_of_length_le (by omega_arith)] at hc
      rw [← hc]
      refine List.map_congr_left fun i hi => ?_
      have hi := List.mem_range.mp hi
      have e₆ := a₆ .dat i hi
      simp only [cont, ivAreas] at e₆
      rw [e₆, copyBlk_apply (by decide), ite_eq_left ⟨rfl, hi⟩]
      rfl

end VG.Proof.Modes.PPC64LE
