module

public import VerifiedGarbage.Proof.Modes.RISCV64.Step
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
public import VerifiedGarbage.Proof.Framework.RISCV64.BigFrame

/-!
# A mode on RISC-V, for any core: the whole function

`seq_wp`: `c.seq M`, for a core `c` with `CoreSpec c` and a mode `M` whose
operations compute the step function `F` (`Computes`), with its arguments in
registers (`f(key = a0, iv = a1, data = a2, n = a3)`), replaces the `n`
steps of data at `data` with the outputs of `F` from the IV, and (if
`M.ivOut`) the IV with the last chaining value; it keeps the registers the
caller expects preserved, the stack pointer and the return address. Each
mode's and cipher's contract follows from it. `seq_changes_wp`: besides,
memory changes only in the frame (below the stack pointer), the data and the
IV, and the frame is zeroed (`Changes`).
-/

@[expose] public section

namespace VG.Proof.Modes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Modes VG.Impl.Modes.RISCV64
open VG.Spec.Aes (bytesAt)

variable {c : Core} {M : Mode}

section
variable (s₀ : State)

abbrev P : Addr := s₀.gpr .a1
abbrev Dp : Addr := s₀.gpr .a2
abbrev N : Nat := (s₀.gpr .a3).toNat

abbrev ivR (c : Core) : Region := ⟨P s₀, 4 * c.bw⟩

/-- The frame's base. -/
abbrev Fb (c : Core) : Addr := s₀.sp - BitVec.ofNat 64 (8 * c.total)

end

/-- What the function needs on entry: the IV readable (and writable, apart
from the data, if the mode writes it back), the data writable, neither
wrapping around, the frame's bytes below the stack pointer, apart from the
IV and the data. -/
structure SeqPre (c : Core) (M : Mode) (s₀ : State) : Prop where
  spAl : s₀.sp.toNat % 16 = 0
  spFit : 8 * c.total ≤ s₀.sp.toNat
  ivRd : ivR s₀ c ∈ s₀.rd ++ s₀.wr
  ivWr : M.ivOut = true → ivR s₀ c ∈ s₀.wr
  ivFit : (P s₀).toNat + 4 * c.bw ≤ 2 ^ 64
  dataW : dataRegion (Dp s₀) M.step (N s₀) ∈ s₀.wr
  dataFit : (Dp s₀).toNat + M.step * N s₀ ≤ 2 ^ 64
  dataScr : Region.Disjoint (dataRegion (Dp s₀) M.step (N s₀)) (scrRegion c (Fb s₀ c))
  ivScr : Region.Disjoint (ivR s₀ c) (scrRegion c (Fb s₀ c))
  ivData : M.ivOut = true → Region.Disjoint (ivR s₀ c) (dataRegion (Dp s₀) M.step (N s₀))
  step : 0 < M.step ∧ M.step ≤ 4 * c.bw
  layout : Layout c

/-- `SeqPre` for a mode whose operations write only the areas `wd`: the data
readable, and writable only if the operations write them (`.dat ∈ wd`), as
CBC-MAC's (`Mode.cbcMac`) do not. -/
structure SeqPreW (c : Core) (M : Mode) (wd : List Loc) (s₀ : State) : Prop where
  spAl : s₀.sp.toNat % 16 = 0
  spFit : 8 * c.total ≤ s₀.sp.toNat
  ivRd : ivR s₀ c ∈ s₀.rd ++ s₀.wr
  ivWr : M.ivOut = true → ivR s₀ c ∈ s₀.wr
  ivFit : (P s₀).toNat + 4 * c.bw ≤ 2 ^ 64
  dataR : dataRegion (Dp s₀) M.step (N s₀) ∈ s₀.rd ++ s₀.wr
  dataW : Loc.dat ∈ wd → dataRegion (Dp s₀) M.step (N s₀) ∈ s₀.wr
  dataFit : (Dp s₀).toNat + M.step * N s₀ ≤ 2 ^ 64
  dataScr : Region.Disjoint (dataRegion (Dp s₀) M.step (N s₀)) (scrRegion c (Fb s₀ c))
  ivScr : Region.Disjoint (ivR s₀ c) (scrRegion c (Fb s₀ c))
  ivData : M.ivOut = true → Region.Disjoint (ivR s₀ c) (dataRegion (Dp s₀) M.step (N s₀))
  step : 0 < M.step ∧ M.step ≤ 4 * c.bw
  layout : Layout c
  preW : ∀ o ∈ M.pre, o.dst ∈ wd
  postW : ∀ o ∈ M.post, o.dst ∈ wd

/-- `SeqPre`, for any mode: its operations write any area. -/
theorem SeqPre.w {s₀ : State} (hp : SeqPre c M s₀) : SeqPreW c M allLocs s₀ :=
  ⟨hp.spAl, hp.spFit, hp.ivRd, hp.ivWr, hp.ivFit, List.mem_append_right _ hp.dataW, fun _ => hp.dataW,
    hp.dataFit, hp.dataScr, hp.ivScr, hp.ivData, hp.step, hp.layout, fun _ _ => mem_allLocs _,
    fun _ _ => mem_allLocs _⟩

/-! ## The slots -/

/-- The mode's slots. -/
abbrev modeR (B : Addr) : Region := ⟨B, 48⟩

/-- `omega_arith`, with the mode's slots unfolded. -/
local macro "slot_omega" : tactic =>
  `(tactic| plain_simp_names ((try simp only [Core.chnSlot, Core.savedSlot, coreSlot]); omega_arith))

theorem range4_map {α : Type} (f : Nat → α) : (List.range 4).map f = [f 0, f 1, f 2, f 3] := rfl

theorem bw_le (hL : Layout c) : c.bw ≤ 4 := by rcases hL.bw with h | h <;> omega_using [h]

theorem buf_le4 (hL : Layout c) : 8 * c.buf + 4 * c.bw ≤ min (8 * c.total) 2032 :=
  Nat.le_min.mpr ⟨Nat.le_trans (Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hL.G_pos) _) hL.buf_le,
    Nat.le_trans (Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hL.G_pos) _) hL.disp⟩

/-- The mode's slots are below the core's. -/
theorem total_ge (hL : Layout c) : coreSlot + 1 ≤ c.total := by
  have := hL.buf_ge; have := buf_le4 hL; have := hL.bw
  simp only [coreSlot] at *; omega_arith

theorem fb_toNat' {s₀ : State} (hfit : 8 * c.total ≤ s₀.sp.toNat) :
    (Fb s₀ c).toNat = s₀.sp.toNat - 8 * c.total := by
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_arith), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega_arith)]

theorem fb_toNat {wd : List Loc} {s₀ : State} (hp : SeqPreW c M wd s₀) : (Fb s₀ c).toNat = s₀.sp.toNat - 8 * c.total :=
  fb_toNat' hp.spFit

/-- The frame, from inside `bigFrame`, for any function in the modes' frame. -/
theorem scrIn_of' {s₀ t : State} (hs : s₀.sp.toNat % 16 = 0) (hsp : 8 * c.total ≤ s₀.sp.toNat)
    (hL : Layout c) (ht : FrameAt (8 * c.total) s₀ t)
    (hw : 0 < 8 * c.total → 8 * c.total ≤ 4064 → (⟨t.sp, 8 * c.total⟩ : Region) ∈ t.wr) :
    ScrIn t (Fb s₀ c) c.total := by
  have hf := fb_toNat' hsp
  have he := hL.even
  have := s₀.sp.isLt
  have hg := total_ge hL
  have e : Fb s₀ c = t.sp := ht.sp.symm
  refine ⟨by rw [hf]; omega_arith, by rw [hf]; omega_arith, fun o w ho => ?_,
    fun h4 => by rw [e]; exact hw (by simp only [coreSlot] at hg; omega_arith) h4, ?_⟩
  · obtain ⟨L, h1, h2, h3⟩ := ht.low (by simp only [coreSlot] at hg; omega_arith)
    rw [e]
    exact ⟨_, h3, VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · intro o w h0 ho hc
    have e : Fb s₀ c = t.sp := ht.sp.symm
    rw [e]; exact ht.inFrame o w h0 ho hc

/-- The frame, from inside `bigFrame`. -/
theorem scrIn_of {wd : List Loc} {s₀ t : State} (hp : SeqPreW c M wd s₀) (ht : FrameAt (8 * c.total) s₀ t)
    (hw : 0 < 8 * c.total → 8 * c.total ≤ 4064 → (⟨t.sp, 8 * c.total⟩ : Region) ∈ t.wr) :
    ScrIn t (Fb s₀ c) c.total :=
  scrIn_of' hp.spAl hp.spFit hp.layout ht hw

/-- A slot of the mode, in its lowest region. -/
theorem slot_low {s : State} {B : Addr} {k : Nat} (hS : ScrIn s B c.total) (hL : Layout c) (hk : k < coreSlot) :
    InRegions s.wr (slotA B k) 8 := by
  have := total_ge hL
  have h6 : coreSlot = 6 := rfl
  exact hS.low _ _ (by omega_arith)

theorem slot_al {s : State} {B : Addr} {k : Nat} (hS : ScrIn s B c.total) (hk : k < c.total) :
    (slotA B k).toNat % 8 = 0 := by
  have := hS.al; have := hS.fit
  have e : (B + BitVec.ofNat 64 (8 * k)).toNat = B.toNat + 8 * k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * k) (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
  rw [e]
  omega_arith

theorem readW_sep64 {m : Mem} {a b : Addr} {v : BitVec 64} (h : Region.Disjoint ⟨a, 8⟩ ⟨b, 8⟩) :
    (m.writeW b v).readW a 64 = m.readW a 64 :=
  Mem.readW_writeW_sep (fun x h1 h2 => h x (by simp only [Region.Contains]; omega_using [h1])
    (by simp only [Region.Contains]; omega_using [h2])) (by decide)

/-- Two different slots of the mode are apart. -/
theorem slot_sep {B : Addr} {i j : Nat} (hi : i < coreSlot) (hj : j < coreSlot) (hne : i ≠ j) :
    Region.Disjoint ⟨slotA B i, 8⟩ ⟨slotA B j, 8⟩ :=
  VG.Offset.disjoint _ (by omega_using [hne]) (by simp only [coreSlot] at *; omega_arith)
    (by simp only [coreSlot] at *; omega_arith)

/-- A slot of the mode, in its slots. -/
theorem slot_mode {B : Addr} {i : Nat} (hi : i < coreSlot) : (modeR B).Contains (slotA B i) (64 / 8) :=
  VG.Offset.contains_base _ (by simp only [coreSlot] at *; omega_arith) (by simp only [coreSlot] at *; omega_arith)

/-! ## The IV's copies -/

/-- The areas of the IV's copies: the IV as the data. -/
def ivAreas (c : Core) (P B : Addr) : Loc → Addr
  | .dat => P
  | .chn => slotA B Core.chnSlot
  | .buf => slotA B c.buf

theorem ivAreasOk {wd : List Loc} {s₀ s : State} (hp : SeqPreW c M wd s₀) (hS : ScrIn s (Fb s₀ c) c.total)
    (hb : s.gpr sb = Fb s₀ c) (h2 : s.gpr .s2 = P s₀) {ws : List Loc} (hws : ∀ l ∈ ws, l = .dat → ivR s₀ c ∈ s.wr)
    (hiv : ivR s₀ c ∈ s.rd ++ s.wr) :
    AreasOk c s (fun _ => 4 * c.bw) (ivAreas c (P s₀) (Fb s₀ c)) ws := by
  have hL := hp.layout
  have hdisp := hL.disp
  have hge := hL.buf_ge
  have hbw := bw_le hL
  have hb4 := buf_le4 hL
  have hP := hp.ivFit
  have hfit := hS.fit
  have h6 : coreSlot = 6 := rfl
  have inScr : ∀ d w, d + w ≤ min (8 * c.total) 2032 → InRegions s.wr (Fb s₀ c + BitVec.ofNat 64 d) w :=
    fun d w h => hS.low d w h
  refine ⟨fun l off ho => ?_, fun l off ho => ?_, fun l off w hw0 ho => ?_, fun l hl off w hw0 ho => ?_,
    fun l l' hne => ?_, fun _ => by omega_arith⟩
  · cases l
    · simp only [Core.loc, ivAreas] at ho ⊢; rw [h2, Nat.zero_add]
    · simp only [Core.loc, ivAreas] at ho ⊢; rw [hb, VG.Offset.add_add]
    · simp only [Core.loc, ivAreas] at ho ⊢; rw [hb, VG.Offset.add_add]
  · cases l <;> simp only [Core.loc] at ho ⊢ <;> slot_omega
  · cases l
    · exact ⟨_, hiv, VG.Offset.contains_base _ ho (by omega_arith)⟩
    · obtain ⟨r, hr, hc⟩ := inScr (8 * Core.chnSlot + off) w (by slot_omega)
      refine ⟨r, List.mem_append_right _ hr, ?_⟩
      simp only [ivAreas]; rw [VG.Offset.add_add]; exact hc
    · obtain ⟨r, hr, hc⟩ := inScr (8 * c.buf + off) w (by omega_arith)
      refine ⟨r, List.mem_append_right _ hr, ?_⟩
      simp only [ivAreas]; rw [VG.Offset.add_add]; exact hc
  · cases l
    · exact ⟨_, hws _ hl rfl, VG.Offset.contains_base _ ho (by omega_arith)⟩
    · simp only [ivAreas]; rw [VG.Offset.add_add]; exact inScr _ _ (by slot_omega)
    · simp only [ivAreas]; rw [VG.Offset.add_add]; exact inScr _ _ (by omega_arith)
  · have hb8 : 8 * c.buf + 4 * c.bw ≤ 8 * c.total := Nat.le_trans hb4 (Nat.min_le_left _ _)
    have dIv : ∀ d, d + 4 * c.bw ≤ 8 * c.total →
        Region.Disjoint (ivR s₀ c) ⟨Fb s₀ c + BitVec.ofNat 64 d, 4 * c.bw⟩ :=
      fun d h => hp.ivScr.sub_right (slot_sub h)
    have hc : 8 * Core.chnSlot + 4 * c.bw ≤ 8 * c.buf := by slot_omega
    have dCB : Region.Disjoint ⟨slotA (Fb s₀ c) Core.chnSlot, 4 * c.bw⟩ ⟨slotA (Fb s₀ c) c.buf, 4 * c.bw⟩ :=
      VG.Offset.disjoint _ (.inl hc) (by omega_arith) (by omega_arith)
    cases l <;> cases l' <;> simp only [ne_eq, not_true_eq_false] at hne <;> simp only [ivAreas]
    · exact dIv _ (by omega_arith)
    · exact dIv _ hb8
    · exact (dIv _ (by omega_arith)).symm
    · exact dCB
    · exact (dIv _ hb8).symm
    · exact dCB.symm

theorem copyBlk_ok {bw : Nat} {dst src : Loc} {ws : List Loc} (hd : dst ∈ ws) {len : Loc → Nat}
    (hl : ∀ l, len l = 4 * bw) : ∀ o ∈ copyBlk bw dst src, o.InBounds len ∧ o.dst ∈ ws := by
  intro o ho
  simp only [copyBlk, List.mem_map, List.mem_range] at ho
  obtain ⟨w, hw, rfl⟩ := ho
  refine ⟨⟨?_, ?_, fun _ _ h => by cases h⟩, hd⟩ <;>
    simp only [Op.width, Bool.false_eq_true, ite_false, ite_true, hl] <;> omega_using [hw]

/-! ## The entry -/

/-- After the entry, from `t` in the frame: the frame's base in `sb`, the
mode's state in `s1`–`s3`, the caller's `s1`–`s4` in their slots, the IV in
the chaining value's. -/
structure Entered (c : Core) (s₀ t s : State) : Prop where
  b : s.gpr sb = Fb s₀ c
  s1 : s.gpr .s1 = P s₀
  s3 : s.gpr .s3 = s₀.gpr .a3
  s2 : s.gpr .s2 = Dp s₀
  keep : ∀ r ∈ kept, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = t.wr
  saved : ∀ i < 4, s.mem.readW (slotA (Fb s₀ c) (Core.savedSlot i)) 64 = s₀.gpr (Core.savedRegs.getD i .s1)
  chn : bytesAt s.mem (slotA (Fb s₀ c) Core.chnSlot) (4 * c.bw) = bytesAt s₀.mem (P s₀) (4 * c.bw)
  frame : Frame [modeR (Fb s₀ c)] s₀.mem s.mem

/-- The registers the entry writes are not kept, but for `s1`–`s4`. -/
theorem kept_ne_entry : ∀ r ∈ kept, r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2 := by decide

/-- After `Core.entry`, from `t` in the frame: the frame's base in `sb`,
the second and fourth arguments in `s1`, `s2` and `s3`, the caller's
`s1`–`s4` in their slots, and the rest as on entry but for `t0`. -/
structure Saves (c : Core) (s₀ t s : State) : Prop where
  b : s.gpr sb = Fb s₀ c
  s1 : s.gpr .s1 = s₀.gpr .a1
  s2 : s.gpr .s2 = s₀.gpr .a1
  s3 : s.gpr .s3 = s₀.gpr .a3
  other : ∀ r, r ≠ .t0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = t.wr
  saved : ∀ i < 4, s.mem.readW (slotA (Fb s₀ c) (Core.savedSlot i)) 64 = s₀.gpr (Core.savedRegs.getD i .s1)
  frame : Frame [modeR (Fb s₀ c)] s₀.mem s.mem

/-- The caller's `s1`–`s4` saved, for any function in the modes' frame. -/
theorem saves_wp {s₀ t : State} (hL : Layout c) (hS : ScrIn t (Fb s₀ c) c.total)
    (ht : FrameAt (8 * c.total) s₀ t) :
    WP isa (.block Core.entry) t (Saves c s₀ t) := by
  have hg := total_ge hL
  have h6 : coreSlot = 6 := rfl
  have hsv : ∀ i < 4, Core.savedSlot i < coreSlot := fun i hi => by slot_omega
  have ha : ∀ i < 4, (slotA (Fb s₀ c) (Core.savedSlot i)).toNat % 8 = 0 := fun i hi =>
    slot_al hS (by have := hsv i hi; omega_arith)
  have hw : ∀ i < 4, InRegions t.wr (slotA (Fb s₀ c) (Core.savedSlot i)) 8 := fun i hi =>
    slot_low hS hL (hsv i hi)
  have g₀ : ∀ r, t.gpr r = s₀.gpr r := fun r => by rw [ht.gpr]
  simp only [Core.entry, range4_map, Core.savedRegs, List.getD_cons_zero, List.getD_cons_succ,
    List.cons_append, List.nil_append, mov]
  refine wp_addSp (imm := 0) (by decide) fun s₁ u₁ => ?_
  have b₁ : s₁.gpr .t0 = Fb s₀ c := by rw [u₁.gpr, BitVec.add_zero, ht.sp]
  refine wp_sd (a := slotA (Fb s₀ c) (Core.savedSlot 0)) (by decide) (by rw [b₁]) (ha 0 (by decide))
    (by rw [u₁.wr]; exact hw 0 (by decide)) fun s₂ u₂ => ?_
  refine wp_sd (a := slotA (Fb s₀ c) (Core.savedSlot 1)) (by decide) (by rw [u₂.gpr, b₁])
    (ha 1 (by decide)) (by rw [u₂.wr, u₁.wr]; exact hw 1 (by decide)) fun s₃ u₃ => ?_
  refine wp_sd (a := slotA (Fb s₀ c) (Core.savedSlot 2)) (by decide) (by rw [u₃.gpr, u₂.gpr, b₁])
    (ha 2 (by decide)) (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hw 2 (by decide)) fun s₄ u₄ => ?_
  refine wp_sd (a := slotA (Fb s₀ c) (Core.savedSlot 3)) (by decide) (by rw [u₄.gpr, u₃.gpr, u₂.gpr, b₁])
    (ha 3 (by decide)) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hw 3 (by decide)) fun s₅ u₅ => ?_
  have g₅ : s₅.gpr = s₁.gpr := by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]
  have v₁ : ∀ r, r ≠ .t0 → s₁.gpr r = s₀.gpr r := fun r h => by rw [u₁.other r h, g₀]
  have m₅ : s₅.mem = (((s₀.mem.writeW (slotA (Fb s₀ c) (Core.savedSlot 0)) (s₀.gpr .s1)).writeW
      (slotA (Fb s₀ c) (Core.savedSlot 1)) (s₀.gpr .s2)).writeW (slotA (Fb s₀ c) (Core.savedSlot 2))
      (s₀.gpr .s3)).writeW (slotA (Fb s₀ c) (Core.savedSlot 3)) (s₀.gpr .s4) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₄.gpr, u₃.gpr, u₂.gpr, ht.mem,
      v₁ .s1 (by decide), v₁ .s2 (by decide), v₁ .s3 (by decide), v₁ .s4 (by decide)]
  refine wp_mv fun s₆ u₆ => wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ => wp_mv fun s₉ u₉ => WP.block_nil ?_
  have m₉ : s₉.mem = s₅.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  -- The saved values.
  have sv₅ : ∀ i < 4, s₅.mem.readW (slotA (Fb s₀ c) (Core.savedSlot i)) 64 =
      s₀.gpr (Core.savedRegs.getD i .s1) := by
    intro i hi
    rw [m₅]
    have sep := fun i j hi hj hne => slot_sep (B := Fb s₀ c) (i := Core.savedSlot i) (j := Core.savedSlot j)
      (hsv i hi) (hsv j hj) (by simp only [Core.savedSlot]; exact hne)
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_arith) with rfl | rfl | rfl | rfl
    · rw [readW_sep64 (sep 0 3 (by decide) (by decide) (by decide)),
        readW_sep64 (sep 0 2 (by decide) (by decide) (by decide)),
        readW_sep64 (sep 0 1 (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]; rfl
    · rw [readW_sep64 (sep 1 3 (by decide) (by decide) (by decide)),
        readW_sep64 (sep 1 2 (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]; rfl
    · rw [readW_sep64 (sep 2 3 (by decide) (by decide) (by decide)), Mem.readW_writeW_self64]; rfl
    · rw [Mem.readW_writeW_self64]; rfl
  have f₅ : Frame [modeR (Fb s₀ c)] s₀.mem s₅.mem := by
    rw [m₅]
    exact ((((Frame.refl _ _).writeW List.mem_cons_self _ (slot_mode (hsv 0 (by decide)))).writeW
      List.mem_cons_self _ (slot_mode (hsv 1 (by decide)))).writeW List.mem_cons_self _
      (slot_mode (hsv 2 (by decide)))).writeW List.mem_cons_self _ (slot_mode (hsv 3 (by decide)))
  refine ⟨?_, ?_, ?_, ?_, fun r h0 h1 h2 h3 h4 => ?_, ?_, ?_, fun i hi => by rw [m₉]; exact sv₅ i hi,
    by rw [m₉]; exact f₅⟩
  · rw [show sb = .s4 from rfl] at u₆ ⊢
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅, b₁]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), g₅, v₁ _ (by decide)]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g₅, v₁ _ (by decide)]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), g₅, v₁ _ (by decide)]
  · rw [u₉.other r h3, u₈.other r h2, u₇.other r h1, u₆.other r h4, g₅, v₁ r h0]
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, ht.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

theorem entry_wp {wd : List Loc} {s₀ t : State} (hp : SeqPreW c M wd s₀) (ht : FrameAt (8 * c.total) s₀ t)
    (hw : 0 < 8 * c.total → 8 * c.total ≤ 4064 → (⟨t.sp, 8 * c.total⟩ : Region) ∈ t.wr) :
    WP isa (.block (Core.entry ++ c.ivIn)) t (Entered c s₀ t) := by
  have hL := hp.layout
  have hbw := bw_le hL
  have hS := scrIn_of hp ht hw
  have hg := total_ge hL
  have h6 : coreSlot = 6 := rfl
  rw [WP.block_append_iff]
  refine WP.mono (saves_wp hL hS ht) fun s₉ h₉ => ?_
  have hsv : ∀ i < 4, Core.savedSlot i < coreSlot := fun i hi => by slot_omega
  have keep₉ : ∀ r ∈ kept, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → s₉.gpr r = s₀.gpr r :=
    fun r hr h1 h2 h3 h4 => h₉.other r (kept_ne_entry r hr).1 h1 h2 h3 h4
  simp only [Core.ivIn, mov]
  -- The IV to the chaining value.
  have hS₉ : ScrIn s₉ (Fb s₀ c) c.total := hS.congr h₉.wr
  refine opsCode_wp c (ws := [.chn]) (copyBlk_ok (List.mem_singleton_self _) fun _ => rfl)
    (ivAreasOk hp hS₉ h₉.b h₉.s2 (fun l hl e => by simp at hl; subst hl; cases e)
      (by rw [h₉.rd, h₉.wr]; obtain ⟨ws, hws⟩ := ht.wr; rw [hws]
          rcases List.mem_append.mp hp.ivRd with h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ (List.mem_append_right _ h)))
    fun s₁₁ a₁₁ f₁₁ g₁₁ rd₁₁ wr₁₁ => wp_mv fun s₁₂ u₁₂ => WP.block_nil ?_
  have chnOnly : ∀ {R : Region}, R.Disjoint (chnRegion c (Fb s₀ c)) →
      ∀ r ∈ areaRegions (fun _ => 4 * c.bw) (ivAreas c (P s₀) (Fb s₀ c)) [.chn], R.Disjoint r := fun h r hr => by
    simp only [areaRegions, ivAreas, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h
  have g : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .s2 → s₁₂.gpr r = s₉.gpr r := fun r h0 h1 h2 hs => by
    rw [u₁₂.other r hs, g₁₁ r h0 h1 h2]
  refine ⟨by rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact h₉.b,
    by rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact h₉.s1,
    by rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact h₉.s3,
    by rw [u₁₂.gpr, g₁₁ _ (by decide) (by decide) (by decide),
      h₉.other _ (by decide) (by decide) (by decide) (by decide) (by decide)],
    fun r hr h1 h2 h3 h4 => by
      rw [g r (kept_ne_entry r hr).1 (kept_ne_entry r hr).2.1 (kept_ne_entry r hr).2.2 h2,
        keep₉ r hr h1 h2 h3 h4],
    by rw [u₁₂.rd, rd₁₁, h₉.rd], by rw [u₁₂.wr, wr₁₁, h₉.wr], fun i hi => ?_, ?_, ?_⟩
  · rw [u₁₂.mem, ← h₉.saved i hi]
    exact f₁₁.readW (Region.contains_self _ _) (chnOnly
      (VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega))) (by decide)
  · refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    have e := a₁₁ .chn i hi
    simp only [cont, ivAreas] at e
    rw [u₁₂.mem, e, copyBlk_apply (by decide), ite_eq_left ⟨rfl, hi⟩]
    exact h₉.frame.bytes (R := ivR s₀ c) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.ivScr.sub_right (Region.sub_prefix (by omega_arith))) (by show 4 * c.bw ≤ 2 ^ 64; omega_arith) hi
  · rw [u₁₂.mem]
    refine h₉.frame.trans (f₁₁.sub fun r hr => ?_)
    simp only [areaRegions, ivAreas, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨_, List.mem_singleton_self _, VG.Offset.sub_base _ (by slot_omega)⟩

/-! ## The exit -/

theorem restore_wp {s₀ u : State} (hL : Layout c) (hS : ScrIn u (Fb s₀ c) c.total)
    (hb : u.gpr sb = Fb s₀ c)
    (hsv : ∀ i < 4, u.mem.readW (slotA (Fb s₀ c) (Core.savedSlot i)) 64 = s₀.gpr (Core.savedRegs.getD i .s1))
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u', u'.gpr .s1 = s₀.gpr .s1 → u'.gpr .s2 = s₀.gpr .s2 → u'.gpr .s3 = s₀.gpr .s3 →
      u'.gpr .s4 = s₀.gpr .s4 → u'.gpr .t3 = Fb s₀ c →
      (∀ r, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → r ≠ .t3 → u'.gpr r = u.gpr r) →
      u'.mem = u.mem → u'.rd = u.rd → u'.wr = u.wr → WP isa (.block is) u' Q) :
    WP isa (.block (Core.restore ++ is)) u Q := by
  have hg := total_ge hL
  have h6 : coreSlot = 6 := rfl
  have hsv' : ∀ i < 4, Core.savedSlot i < coreSlot := fun i hi => by slot_omega
  have ha : ∀ i < 4, (slotA (Fb s₀ c) (Core.savedSlot i)).toNat % 8 = 0 := fun i hi =>
    slot_al hS (by have := hsv' i hi; omega_arith)
  have hin : ∀ i < 4, InRegions (u.rd ++ u.wr) (slotA (Fb s₀ c) (Core.savedSlot i)) 8 := fun i hi => by
    obtain ⟨r, hr, hc⟩ := slot_low hS hL (hsv' i hi)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  simp only [Core.restore, range4_map, Core.savedRegs, List.getD_cons_zero, List.getD_cons_succ,
    List.cons_append, List.nil_append, mov]
  refine wp_mv fun u₀ v₀ => ?_
  have b₀ : u₀.gpr .t3 = Fb s₀ c := by rw [v₀.gpr]; exact hb
  refine wp_ld (a := slotA (Fb s₀ c) (Core.savedSlot 0)) (by decide) (by rw [b₀]) (ha 0 (by decide))
    (by rw [v₀.rd, v₀.wr]; exact hin 0 (by decide)) fun u₁ v₁ => ?_
  refine wp_ld (a := slotA (Fb s₀ c) (Core.savedSlot 1)) (by decide) (by rw [v₁.other _ (by decide), b₀])
    (ha 1 (by decide)) (by rw [v₁.rd, v₁.wr, v₀.rd, v₀.wr]; exact hin 1 (by decide)) fun u₂ v₂ => ?_
  refine wp_ld (a := slotA (Fb s₀ c) (Core.savedSlot 2)) (by decide)
    (by rw [v₂.other _ (by decide), v₁.other _ (by decide), b₀]) (ha 2 (by decide))
    (by rw [v₂.rd, v₂.wr, v₁.rd, v₁.wr, v₀.rd, v₀.wr]; exact hin 2 (by decide)) fun u₃ v₃ => ?_
  refine wp_ld (a := slotA (Fb s₀ c) (Core.savedSlot 3)) (by decide)
    (by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), b₀]) (ha 3 (by decide))
    (by rw [v₃.rd, v₃.wr, v₂.rd, v₂.wr, v₁.rd, v₁.wr, v₀.rd, v₀.wr]; exact hin 3 (by decide)) fun u₄ v₄ => ?_
  have m₃ : u₃.mem = u.mem := by rw [v₃.mem, v₂.mem, v₁.mem, v₀.mem]
  refine k u₄ ?_ ?_ ?_ ?_ ?_ (fun r h1 h2 h3 h4 ht => ?_) (by rw [v₄.mem, m₃])
    (by rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd, v₀.rd]) (by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr, v₀.wr])
  · rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, v₀.mem,
      hsv 0 (by decide)]; rfl
  · rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.mem, v₀.mem, hsv 1 (by decide)]; rfl
  · rw [v₄.other _ (by decide), v₃.gpr, v₂.mem, v₁.mem, v₀.mem, hsv 2 (by decide)]; rfl
  · rw [v₄.gpr, m₃, hsv 3 (by decide)]; rfl
  · rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), b₀]
  · rw [v₄.other r h4, v₃.other r h3, v₂.other r h2, v₁.other r h1, v₀.other r ht]

theorem wipe_wp {u : State} {B : Addr} (hL : Layout c) (hS : ScrIn u B c.total) (h3 : u.gpr .t3 = B) :
    WP isa c.wipe u fun u' => (∀ j < c.total, u'.mem.readW (slotA B j) 64 = 0#64) ∧
      Frame [⟨B, 8 * c.total⟩] u.mem u'.mem ∧
      (∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  have hg := total_ge hL
  have ht := hL.total
  have h6 : coreSlot = 6 := rfl
  have hal := hS.al
  have hfit := hS.fit
  unfold Core.wipe
  apply WP.seq
  refine WP.mono (Q := fun (v : State) => v.gpr .t0 = 0#64 ∧ v.gpr .t1 = B ∧ v.gpr .t2 = BitVec.ofNat 64 c.total ∧
      (∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → v.gpr r = u.gpr r) ∧ v.mem = u.mem ∧ v.rd = u.rd ∧ v.wr = u.wr)
    (wp_li (imm := 0) (by decide) fun v₁ w₁ => wp_mv fun v₂ w₂ => wp_li (by omega_arith) fun v₃ w₃ =>
      WP.block_nil ⟨by rw [w₃.other _ (by decide), w₂.other _ (by decide), w₁.gpr],
        by rw [w₃.other _ (by decide), w₂.gpr, w₁.other _ (by decide), h3], w₃.gpr,
        fun r h0 h1 h2 => by rw [w₃.other r h2, w₂.other r h1, w₁.other r h0],
        by rw [w₃.mem, w₂.mem, w₁.mem], by rw [w₃.rd, w₂.rd, w₁.rd], by rw [w₃.wr, w₂.wr, w₁.wr]⟩)
    fun v ⟨z0, p1, c2, gv, mv, rv, wv⟩ => ?_
  refine WP.mono (fillLoop_ok (v := .t0) (ptr := .t1) (cnt := .t2) (by decide) (by decide) (by decide) v
    (N := c.total) (by simp only [coreSlot] at hg; omega_arith) (by omega_arith) c2
    (by rw [p1]; omega_arith) (fun i hi => by
      rw [wv, p1]; exact hS.wr _ _ (by decide) (by omega_arith) (by omega_arith)))
    fun u' ⟨tz, tf, tk⟩ => ⟨fun j hj => by rw [← z0, ← p1]; exact tz j hj, by rw [← mv, ← p1]; exact tf,
      fun r h0 h1 h2 => by rw [tk.gpr (by simp [h1, h2]), gv r h0 h1 h2], by rw [tk.2.1, rv],
      by rw [tk.2.2, wv]⟩

/-! ## The function -/

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

/-- The regions the mode writes, on entry: the data and the frame. -/
abbrev wrs0 (c : Core) (M : Mode) (s₀ : State) : List Region := wrs c (Fb s₀ c) (Dp s₀) (N s₀) M.step

/-- What the function changes besides the registers: memory only in the
frame, the data and the IV; and it leaves the frame zeroed. -/
structure Changes (c : Core) (M : Mode) (s₀ s' : State) : Prop where
  frame : Frame [scrRegion c (Fb s₀ c), dataRegion (Dp s₀) M.step (N s₀), ivR s₀ c] s₀.mem s'.mem
  zeroed : ∀ j < c.total, s'.mem.readW (slotA (Fb s₀ c) j) 64 = 0#64

/-- `seqW_wp`, and what the function changes (`Changes`). -/
theorem seqW_changes_wp (cs : CoreSpec c) {M : Mode} {wd : List Loc} {F : StepFn} {s₀ : State} {k : cs.Key}
    (hp : SeqPreW c M wd s₀)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c M.step))
    (hpost : ∀ o ∈ M.post, o.InBounds (lens c M.step))
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F) (hk : cs.KeyArgs s₀ (wrs0 c M s₀) k) :
    WP isa (c.seq M) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt M.step s'.mem (Dp s₀) (N s₀) = (run F (iv0 c s₀) (xs0 M s₀)).1 ∧
      (M.ivOut = true → bytesAt s'.mem (P s₀) (4 * c.bw) = (run F (iv0 c s₀) (xs0 M s₀)).2) ∧
      Changes c M s₀ s' := by
  have hL := hp.layout
  have hg := total_ge hL
  have h6 : coreSlot = 6 := rfl
  have hbw := bw_le hL
  have hb4 := buf_le4 hL
  have hf := fb_toNat hp
  have hspf := hp.spFit
  have hsp := s₀.sp.isLt
  have hfit : (Fb s₀ c).toNat + 8 * c.total ≤ 2 ^ 64 := by omega_arith
  have hlen : (xs0 M s₀).length = N s₀ := chunksAt_length _ _ _ _
  have modeScr : Region.Sub (modeR (Fb s₀ c)) (scrRegion c (Fb s₀ c)) := Region.sub_prefix (by omega_arith)
  have coreScr : Region.Sub (coreRegion c (Fb s₀ c)) (scrRegion c (Fb s₀ c)) :=
    VG.Offset.sub_base _ (by omega_arith)
  have chnScr : Region.Sub (chnRegion c (Fb s₀ c)) (scrRegion c (Fb s₀ c)) := VG.Offset.sub_base _ (by slot_omega)
  have m1 : ∀ {a b : Region} {l : List Region}, b ∈ a :: b :: l := List.mem_cons_of_mem _ List.mem_cons_self
  unfold Core.seq
  refine bigFrame_wp (by simp only [Core.frameBytes]; have := hL.even; omega_arith)
    (by simp only [Core.frameBytes]; omega_arith) fun t ht hw => ?_
  have hS := scrIn_of hp ht hw
  obtain ⟨ws, hws⟩ := ht.wr
  -- The entry and the key.
  refine WP.seq (WP.of_syms (WP.mono (entry_wp hp ht hw) fun s₁ h₁ sy₁ => ?_))
  have wr₁ : s₁.wr = ws ++ s₀.wr := by rw [h₁.wr, hws]
  refine WP.seq (WP.mono (cs.prepare_wp h₁.b (hS.congr h₁.wr) m1
    (cs.keyArgs_congr hk h₁.keep h₁.rd ⟨ws, wr₁⟩ (sy₁.trans ht.syms)
      (h₁.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, m1, modeScr⟩)))
    fun s₂ ⟨ready₂, b₂, kept₂, f₂, rd₂, wr₂⟩ => ?_)
  have kp : ∀ r, r ∈ kept → s₂.gpr r = s₁.gpr r := kept₂
  have f₀₂ : Frame [modeR (Fb s₀ c), coreRegion c (Fb s₀ c)] s₀.mem s₂.mem :=
    (h₁.frame.mono (by simp)).trans (f₂.mono (by simp))
  have dataOut : ∀ r ∈ [modeR (Fb s₀ c), coreRegion c (Fb s₀ c)],
      Region.Disjoint (dataRegion (Dp s₀) M.step (N s₀)) r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dataScr.sub_right modeScr
    · exact hp.dataScr.sub_right coreScr
  have modeOut : ∀ {R : Region}, Region.Sub R (modeR (Fb s₀ c)) → ∀ r ∈ [coreRegion c (Fb s₀ c)], R.Disjoint r :=
    fun hsub r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (VG.Offset.disjoint_base _ (by slot_omega) (by omega_arith)).symm.sub_left hsub
  have wr₂' : s₂.wr = ws ++ s₀.wr := by rw [wr₂, wr₁]
  have hFx : Fixed c s₂ (Fb s₀ c) (Dp s₀) (N s₀) M.step wd :=
    ⟨hS.congr (by rw [wr₂, h₁.wr]), by
        rw [rd₂, h₁.rd, wr₂']
        rcases List.mem_append.mp hp.dataR with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (List.mem_append_right _ h),
      fun h => by rw [wr₂']; exact List.mem_append_right _ (hp.dataW h), hp.dataFit,
      hp.dataScr, (s₀.gpr .a3).isLt, hp.step, hL⟩
  have hI : Inv cs s₂ (Fb s₀ c) (Dp s₀) (N s₀) M.step k F (iv0 c s₀) (xs0 M s₀) 0 s₂ := by
    refine ⟨b₂, fun _ _ _ _ => rfl, rfl, rfl, ?_, ?_, ready₂, ?_, ?_, Frame.refl _ _⟩
    · rw [kp _ (by decide), h₁.s2, Nat.mul_zero]; exact (BitVec.add_zero _).symm
    · rw [kp _ (by decide), h₁.s3, Nat.sub_zero]; simp only [N, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [chunksAt_frame f₀₂ dataOut (by have := hp.dataFit; omega_arith)]
      simp only [List.take_zero, run, List.nil_append, List.drop_zero]
    · simp only [List.take_zero, run]
      rw [iv0, ← h₁.chn]
      refine List.map_congr_left fun i hi => f₂.bytes (R := chnRegion c (Fb s₀ c))
        (modeOut (VG.Offset.sub_base _ (by slot_omega))) (by show 4 * c.bw ≤ 2 ^ 64; omega_arith)
        (List.mem_range.mp hi)
  have sv₂ : ∀ i < 4, s₂.mem.readW (slotA (Fb s₀ c) (Core.savedSlot i)) 64 =
      s₀.gpr (Core.savedRegs.getD i .s1) := fun i hi => by
    rw [← h₁.saved i hi]
    exact f₂.readW (Region.contains_self _ _) (modeOut (VG.Offset.sub_base _ (by slot_omega))) (by decide)
  -- The steps.
  refine WP.seq (WP.mono (loop_wp cs hFx rfl hpre hpost hp.preW hp.postW hcomp hlen hI) fun s₄ h₄ => ?_)
  have slotOut : ∀ i < 4, ∀ r ∈ big c (Fb s₀ c) (Dp s₀) (N s₀) M.step,
      Region.Disjoint ⟨slotA (Fb s₀ c) (Core.savedSlot i), 64 / 8⟩ r := fun i hi r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by omega_arith)
    · exact VG.Offset.disjoint _ (.inl (by slot_omega)) (by slot_omega) (by slot_omega)
    · exact (hp.dataScr.sub_right (VG.Offset.sub_base _ (by slot_omega))).symm
  have sv₄ : ∀ i < 4, s₄.mem.readW (slotA (Fb s₀ c) (Core.savedSlot i)) 64 =
      s₀.gpr (Core.savedRegs.getD i .s1) := fun i hi => by
    rw [← sv₂ i hi]
    exact h₄.frame.readW (Region.contains_self _ _) (slotOut i hi) (by decide)
  have data₄ : chunksAt M.step s₄.mem (Dp s₀) (N s₀) = (run F (iv0 c s₀) (xs0 M s₀)).1 := by
    rw [h₄.data, List.take_of_length_le (by omega_arith), List.drop_of_length_le (by omega_arith), List.append_nil]
  have keep₄ : ∀ r ∈ kept, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → s₄.gpr r = s₀.gpr r :=
    fun r hr h1 h2 h3 h4 => by rw [h₄.keep r hr h3 h2, kp r hr, h₁.keep r hr h1 h2 h3 h4]
  have s1₄ : s₄.gpr .s1 = P s₀ := by rw [h₄.keep _ (by decide) (by decide) (by decide), kp _ (by decide), h₁.s1]
  have wr₄ : s₄.wr = t.wr := by rw [h₄.wr, wr₂, h₁.wr]
  have rd₄ : s₄.rd = s₀.rd := by rw [h₄.rd, rd₂, h₁.rd]
  have hS₄ : ScrIn s₄ (Fb s₀ c) c.total := hS.congr wr₄
  have fr₄ : Frame [scrRegion c (Fb s₀ c), dataRegion (Dp s₀) M.step (N s₀), ivR s₀ c] s₀.mem s₄.mem := by
    refine (f₀₂.sub fun r hr => ?_).trans (h₄.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, modeScr⟩
      · exact ⟨_, List.mem_cons_self, coreScr⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, coreScr⟩
      · exact ⟨_, List.mem_cons_self, chnScr⟩
      · exact ⟨_, m1, fun _ h => h⟩
  -- The end: the registers back, the frame zeroed.
  have abi : ∀ v : State, v.gpr .s1 = s₀.gpr .s1 → v.gpr .s2 = s₀.gpr .s2 → v.gpr .s3 = s₀.gpr .s3 →
      v.gpr .s4 = s₀.gpr .s4 → (∀ r ∈ kept, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → v.gpr r = s₀.gpr r) →
      abiPreserved s₀ { v with sp := s₀.sp, wr := s₀.wr } := fun v g1 g2 g3 g4 hk => ⟨fun r hr => by
        show v.gpr r = _
        by_cases e1 : r = .s1
        · subst e1; exact g1
        by_cases e2 : r = .s2
        · subst e2; exact g2
        by_cases e3 : r = .s3
        · subst e3; exact g3
        by_cases e4 : r = .s4
        · subst e4; exact g4
        exact hk r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)) e1 e2 e3 e4, rfl,
        hk .ra (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  have ne3 : ∀ r ∈ kept, r ≠ .t3 ∧ r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2 := by decide
  have scrData : Region.Disjoint (dataRegion (Dp s₀) M.step (N s₀)) ⟨Fb s₀ c, 8 * c.total⟩ := hp.dataScr
  apply WP.seq
  cases hiv : M.ivOut
  · rw [show (if false = true then c.ivBack else []) = [] by simp, List.nil_append, ← List.append_nil Core.restore]
    refine restore_wp hL hS₄ h₄.b sv₄ fun u g1 g2 g3 g4 g3' g m rdu wru => WP.block_nil ?_
    refine WP.mono (wipe_wp hL (hS₄.congr wru) g3') fun s' ⟨z, f, g', rd', wr'⟩ =>
      ⟨abi s' (by rw [g' _ (by decide) (by decide) (by decide), g1])
        (by rw [g' _ (by decide) (by decide) (by decide), g2]) (by rw [g' _ (by decide) (by decide) (by decide), g3])
        (by rw [g' _ (by decide) (by decide) (by decide), g4]) fun r hr h1 h2 h3 h4 => by
          rw [g' r (ne3 r hr).2.1 (ne3 r hr).2.2.1 (ne3 r hr).2.2.2, g r h1 h2 h3 h4 (ne3 r hr).1,
            keep₄ r hr h1 h2 h3 h4], ?_, (fun h => by cases h), ⟨?_, z⟩⟩
    · show chunksAt M.step s'.mem (Dp s₀) (N s₀) = _
      rw [chunksAt_frame f (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact scrData) (by have := hp.dataFit; omega_arith), m,
        data₄]
    · show Frame _ s₀.mem s'.mem
      rw [m] at f
      exact fr₄.trans (f.sub fun r hr => ⟨_, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩)
  · rw [show (if true = true then c.ivBack else []) ++ Core.restore =
      mov .s2 .s1 :: (c.opsCode (copyBlk c.bw .dat .chn) ++ Core.restore) by simp [Core.ivBack]]
    refine wp_mv fun s₅ u₅ => ?_
    have b₅ : s₅.gpr sb = Fb s₀ c := by rw [u₅.other _ (by decide)]; exact h₄.b
    have ivW : ivR s₀ c ∈ s₅.wr := by rw [u₅.wr, wr₄, hws]; exact List.mem_append_right _ (hp.ivWr hiv)
    refine opsCode_wp c (ws := [.dat]) (copyBlk_ok (List.mem_singleton_self _) fun _ => rfl)
      (ivAreasOk hp (hS₄.congr u₅.wr) b₅ (by rw [u₅.gpr, s1₄]) (fun _ _ _ => ivW)
        (List.mem_append_right _ ivW)) fun s₆ a₆ f₆ g₆ rd₆ wr₆ => ?_
    rw [u₅.mem] at a₆ f₆
    have ivOnly : ∀ {R : Region}, R.Disjoint (ivR s₀ c) → ∀ r ∈ areaRegions (fun _ => 4 * c.bw)
        (ivAreas c (P s₀) (Fb s₀ c)) [.dat], R.Disjoint r := fun h r hr => by
      simp only [areaRegions, ivAreas, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact h
    have sv₆ : ∀ i < 4, s₆.mem.readW (slotA (Fb s₀ c) (Core.savedSlot i)) 64 =
        s₀.gpr (Core.savedRegs.getD i .s1) := fun i hi => by
      rw [← sv₄ i hi]
      exact f₆.readW (Region.contains_self _ _)
        (ivOnly (hp.ivScr.sub_right (VG.Offset.sub_base _ (by slot_omega))).symm) (by decide)
    have g₆' : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .s2 → s₆.gpr r = s₄.gpr r := fun r h0 h1 h2 h3 => by
      rw [g₆ r h0 h1 h2, u₅.other r h3]
    have b₆ : s₆.gpr sb = Fb s₀ c := by
      rw [g₆' _ (by decide) (by decide) (by decide) (by decide)]; exact h₄.b
    refine restore_wp hL (hS₄.congr (by rw [wr₆, u₅.wr])) b₆ sv₆ fun u g1 g2 g3 g4 g3' g m rdu wru => WP.block_nil ?_
    refine WP.mono (wipe_wp hL (hS₄.congr (by rw [wru, wr₆, u₅.wr])) g3') fun s' ⟨z, f, g', rd', wr'⟩ =>
      ⟨abi s' (by rw [g' _ (by decide) (by decide) (by decide), g1])
        (by rw [g' _ (by decide) (by decide) (by decide), g2]) (by rw [g' _ (by decide) (by decide) (by decide), g3])
        (by rw [g' _ (by decide) (by decide) (by decide), g4]) fun r hr h1 h2 h3 h4 => by
          rw [g' r (ne3 r hr).2.1 (ne3 r hr).2.2.1 (ne3 r hr).2.2.2, g r h1 h2 h3 h4 (ne3 r hr).1,
            g₆' r (ne3 r hr).2.1 (ne3 r hr).2.2.1 (ne3 r hr).2.2.2 h2, keep₄ r hr h1 h2 h3 h4], ?_, (fun _ => ?_),
        ⟨?_, z⟩⟩
    · show chunksAt M.step s'.mem (Dp s₀) (N s₀) = _
      rw [chunksAt_frame f (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact scrData) (by have := hp.dataFit; omega_arith), m,
        chunksAt_frame f₆ (ivOnly (hp.ivData hiv).symm) (by have := hp.dataFit; omega_arith), data₄]
    · show bytesAt s'.mem (P s₀) (4 * c.bw) = _
      have hc := h₄.chn
      rw [List.take_of_length_le (by omega_arith)] at hc
      rw [← hc]
      refine List.map_congr_left fun i hi => ?_
      have hi := List.mem_range.mp hi
      rw [f.bytes (R := ivR s₀ c) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hp.ivScr) (by show 4 * c.bw ≤ 2 ^ 64; omega_arith) hi,
        m]
      have e₆ := a₆ .dat i hi
      simp only [cont, ivAreas] at e₆
      rw [e₆, copyBlk_apply (by decide), ite_eq_left ⟨rfl, hi⟩]
      rfl
    · show Frame _ s₀.mem s'.mem
      rw [m] at f
      refine (fr₄.trans (f₆.sub fun r hr => ?_)).trans (f.sub fun r hr => ⟨_, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩)
      simp only [areaRegions, ivAreas, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact ⟨_, by simp, fun _ h => h⟩

/-- `seqW_changes_wp`, for any mode. -/
theorem seq_changes_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {k : cs.Key} (hp : SeqPre c M s₀)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c M.step))
    (hpost : ∀ o ∈ M.post, o.InBounds (lens c M.step))
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F) (hk : cs.KeyArgs s₀ (wrs0 c M s₀) k) :
    WP isa (c.seq M) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt M.step s'.mem (Dp s₀) (N s₀) = (run F (iv0 c s₀) (xs0 M s₀)).1 ∧
      (M.ivOut = true → bytesAt s'.mem (P s₀) (4 * c.bw) = (run F (iv0 c s₀) (xs0 M s₀)).2) ∧
      Changes c M s₀ s' :=
  seqW_changes_wp cs hp.w hpre hpost hcomp hk

theorem seqW_wp (cs : CoreSpec c) {M : Mode} {wd : List Loc} {F : StepFn} {s₀ : State} {k : cs.Key}
    (hp : SeqPreW c M wd s₀)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c M.step))
    (hpost : ∀ o ∈ M.post, o.InBounds (lens c M.step))
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F) (hk : cs.KeyArgs s₀ (wrs0 c M s₀) k) :
    WP isa (c.seq M) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt M.step s'.mem (Dp s₀) (N s₀) = (run F (iv0 c s₀) (xs0 M s₀)).1 ∧
      (M.ivOut = true → bytesAt s'.mem (P s₀) (4 * c.bw) = (run F (iv0 c s₀) (xs0 M s₀)).2) :=
  WP.mono (seqW_changes_wp cs hp hpre hpost hcomp hk) fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

theorem seq_wp (cs : CoreSpec c) {M : Mode} {F : StepFn} {s₀ : State} {k : cs.Key} (hp : SeqPre c M s₀)
    (hpre : ∀ o ∈ M.pre, o.InBounds (lens c M.step))
    (hpost : ∀ o ∈ M.post, o.InBounds (lens c M.step))
    (hcomp : Computes M (4 * c.bw) (cs.cipher k) F) (hk : cs.KeyArgs s₀ (wrs0 c M s₀) k) :
    WP isa (c.seq M) s₀ fun s' => abiPreserved s₀ s' ∧
      chunksAt M.step s'.mem (Dp s₀) (N s₀) = (run F (iv0 c s₀) (xs0 M s₀)).1 ∧
      (M.ivOut = true → bytesAt s'.mem (P s₀) (4 * c.bw) = (run F (iv0 c s₀) (xs0 M s₀)).2) :=
  seqW_wp cs hp.w hpre hpost hcomp hk

end VG.Proof.Modes.RISCV64
