module

public import VerifiedGarbage.Proof.Seed.RISCV64.G16
public import VerifiedGarbage.Proof.Seed.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Straight

import VerifiedGarbage.Proof.Seed.RISCV64.Swap
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# A round on RISC-V

As on PPC64LE (`Proof/Seed/PPC64LE/Round.lean`): `g16_lanes` restates
`g16_ok` on the lanes of the arrays, and `round_ok` puts the steps of a
round together: on every lane, the round's code does RFC 4269 §2's round
(`Spec.Seed.round`) to the arrays of `L0`, `L1`, `R0`, `R1`, with the round
key at `a0`. `g16` reads its masks through `a3` (`Masks`), which the steps,
writing only the arrays, keep.
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.RegUpd VG.Impl.Seed.RISCV64
open VG.Impl.Aes.RISCV64 (sb)

/-- A block that runs to `Q`, run. -/
theorem run_of_wp {is : List Instr} {s : State} {Q : State → Prop} (h : WP isa (.block is) s Q) :
    ∃ s', runBlock isa is s = some s' ∧ Q s' := by
  induction is generalizing s with
  | nil => exact ⟨s, runBlock_nil, WP.block_nil_iff.mp h⟩
  | cons i is ih =>
    obtain ⟨s₁, h₁, h₂⟩ := WP.block_cons_iff.mp h
    obtain ⟨s', hs', hq⟩ := ih h₂
    exact ⟨s', by show (isa.exec i s).bind _ = _; rw [h₁, Option.bind_some, hs'], hq⟩

/-! ## The masks -/

/-- `a3` points to `g16`'s masks, in the scratch buffer from slot `kSlot`. -/
def Masks (s : State) : Prop :=
  s.gpr kb = s.gpr sb + BitVec.ofNat 64 (8 * kSlot) ∧ KsAt s.mem (s.gpr kb)

/-- The masks are kept by what keeps `a5`, `a3` and the memory outside the
working area. -/
theorem Masks.frame {s s' : State} (h : Masks s) (hsb : s'.gpr sb = s.gpr sb)
    (hkb : s'.gpr kb = s.gpr kb) (hf : Frame [workR s] s.mem s'.mem) : Masks s' := by
  refine ⟨by rw [hkb, hsb]; exact h.1, fun j v hj => ?_⟩
  have hlt : j < 13 := gKs_lt _ hj
  rw [hkb, hf.readW (r := ⟨wordAddr (s.gpr kb) j, 8⟩) (by simp [Region.Contains])
    (fun r hr => ?_) (by decide)]
  · exact h.2 j v hj
  · simp only [List.mem_singleton] at hr; subst hr
    simp only [workR, wordAddr, h.1]
    rw [Offset.add_add]
    exact Offset.disjoint_base _ (by unfold kSlot; omega) (by unfold kSlot; omega)

/-- The masks' slots. -/
def masksR (s : State) : Region := ⟨s.gpr sb + BitVec.ofNat 64 (8 * kSlot), 8 * 13⟩

/-- The masks are kept by what keeps `a5`, `a3` and the memory outside regions
apart from them. -/
theorem Masks.frame' {s s' : State} {rs : List Region} (h : Masks s) (hsb : s'.gpr sb = s.gpr sb)
    (hkb : s'.gpr kb = s.gpr kb) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (masksR s) r) : Masks s' := by
  refine ⟨by rw [hkb, hsb]; exact h.1, fun j v hj => ?_⟩
  have hlt : j < 13 := gKs_lt _ hj
  rw [hkb, hf.readW (r := ⟨Straight.wordAddr (s.gpr kb) j, 8⟩) (by simp [Region.Contains])
    (fun r hr => ?_) (by decide)]
  · exact h.2 j v hj
  · refine (hd r hr).sub_left ?_
    simp only [masksR, Straight.wordAddr, h.1]
    rw [Offset.add_add]
    exact Offset.sub _ (by unfold kSlot; omega) (by unfold kSlot; omega)

theorem masksR_sub (s : State) : Region.Sub (masksR s) (scratchR s) :=
  Offset.sub_base _ (by unfold kSlot scratchSlots; omega)

theorem masksR_workR (s : State) : Region.Disjoint (masksR s) (workR s) :=
  Offset.disjoint_base _ (by unfold kSlot; omega) (by unfold kSlot; omega)

theorem room_ok_gCfg {s : State} (h : Room s) (hm : Masks s) : Ok gCfg s where
  slotIn k hk := h.wr (Offset.contains_base _ (by simp [gCfg, scratchSlots] at hk ⊢; omega)
    (by simp [gCfg] at hk; omega))
  extIn j hj := by
    show InRegions (s.rd ++ s.wr) (wordAddr (s.gpr kb) j) 8
    simp only [wordAddr, hm.1]
    rw [Offset.add_add]
    exact h.rw (Offset.contains_base _ (by simp [gCfg] at hj; unfold kSlot scratchSlots; omega)
      (by simp [gCfg] at hj; unfold kSlot; omega))
  baseAl _ := h.1
  extAl _ := by
    show (s.gpr kb).toNat % 8 = 0
    rw [hm.1]
    exact wordAddr_al h.1 kSlot (by unfold kSlot; omega)
  slots := by decide
  sep k hk j hj := by
    show Mem.Sep (wordAddr (s.gpr sb) k) 8 (wordAddr (s.gpr kb) j) 8
    simp only [wordAddr, hm.1]
    rw [Offset.add_add]
    simp [gCfg] at hk hj
    exact Offset.sep _ (by unfold kSlot; omega) (by omega) (by unfold kSlot; omega)

/-- `g16` on the lanes: `G` of `G`'s words, the other arrays kept. -/
theorem g16_lanes {s : State} (h : Room s) (hm : Masks s) :
    ∃ s', runBlock isa g16 s = some s' ∧
      (∀ w < 16, lv s' (tSlot 0) w = Spec.Seed.g (lv s (tSlot 0) w)) ∧
      (∀ k ∈ arrays, k ≠ tSlot 0 → ∀ b < 16, lv s' k b = lv s k b) ∧
      Room s' ∧ Masks s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ∉ g16Writes → s'.gpr r = s.gpr r) ∧ Frame [workR s] s.mem s'.mem := by
  obtain ⟨s', hs', hg, hrd, hwr, hsp, hregs, hfr⟩ := g16_ok (room_ok_gCfg h hm) hm.1 hm.2
  have hsb : s'.gpr sb = s.gpr sb := hregs _ (by decide)
  have hkb : s'.gpr kb = s.gpr kb := hregs _ (by decide)
  have hfw : Frame [workR s] s.mem s'.mem := by
    refine hfr.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨workR s, List.mem_singleton_self _, Region.sub_prefix (by simp [gCfg])⟩
  refine ⟨s', hs', fun w hw => ?_, fun k hk hkt b hb => ?_, room_congr h hsb hwr,
    hm.frame hsb hkb hfw, hrd, hwr, hsp, hregs, hfw⟩
  · rw [← wordQ_lv, ← wordQ_lv]; exact hg w hw
  · have hb' := arrays_bound k hk
    have hk48 : 48 ≤ k := by
      simp only [arrays, List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hkt | decide
    simp only [lv, laneA, hsb]
    refine hfr.readW (r := ⟨s.gpr sb + BitVec.ofNat 64 (8 * k + 4 * b), 4⟩)
      (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base (s.gpr sb) (d := 8 * k + 4 * b) (n := 4) (k := 8 * 48)
      (by omega) (by omega)

/-! ## The round -/

/-- Lane `b` of the blocks' state: `(L0, L1, R0, R1)`. -/
def quad (s : State) (b : Nat) : Spec.Seed.Word × Spec.Seed.Word × Spec.Seed.Word × Spec.Seed.Word :=
  (lv s (arrSlot 0) b, lv s (arrSlot 1) b, lv s (arrSlot 2) b, lv s (arrSlot 3) b)

theorem reads1 (k0 k1 : BitVec 32) : ReadsArrays (sp1 k0 k1) := by
  intro kv hkv x y h
  simp only [sp1, List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl <;> simp only [h _ mem_R0, h _ mem_R1]

theorem reads2 : ReadsArrays sp2 := by
  intro kv hkv x y h
  simp only [sp2, List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl <;> simp only [h _ mem_tA, h _ mem_aA]

theorem reads3 : ReadsArrays sp3 := by
  intro kv hkv x y h
  simp only [sp3, List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl <;> simp only [h _ mem_tA, h _ mem_cA]

theorem reads4 : ReadsArrays sp4 := by
  intro kv hkv x y h
  simp only [sp4, List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl <;> simp only [h _ mem_tA, h _ mem_dA, h _ mem_L0, h _ mem_L1]

theorem dests1 (k0 k1 : BitVec 32) : ∀ kv ∈ sp1 k0 k1, kv.1 ∈ arrays := by
  intro kv hkv; simp only [sp1, List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl
  · exact mem_aA
  · exact mem_tA
theorem dests2 : ∀ kv ∈ sp2, kv.1 ∈ arrays := by
  intro kv hkv; simp only [sp2, List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl <;> decide
theorem dests3 : ∀ kv ∈ sp3, kv.1 ∈ arrays := by
  intro kv hkv; simp only [sp3, List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl <;> decide
theorem dests4 : ∀ kv ∈ sp4, kv.1 ∈ arrays := by
  intro kv hkv; simp only [sp4, List.mem_cons, List.mem_nil_iff, or_false] at hkv
  rcases hkv with rfl | rfl <;> decide

/-- A step on all sixteen lanes, from a state where the scratch buffer is writable. -/
theorem lanes16_room {f : Nat → List Instr} {sp : LaneSpec} (hsp : ∀ kv ∈ sp, kv.1 ∈ arrays)
    (hd : ReadsArrays sp) (hf : ∀ b < 16, ∀ s, Room s → ∃ s', runBlock isa (f b) s = some s' ∧ LaneOk s s' sp b)
    {s : State} (h : Room s) :
    ∃ s', runBlock isa (lanes16 f) s = some s' ∧ Room s' ∧
      (∀ k ∈ arrays, ∀ b < 16, lv s' k b = newVal sp k (fun k' => lv s k' b)) ∧
      Frame [arraysR s] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .t0 → r ≠ .t1 → s'.gpr r = s.gpr r) := by
  obtain ⟨s', hs', hP, hv, rest⟩ := lanes_ok hsp hd (P := Room)
    (fun _ s s' hP hok => room_congr hP (hok.regs _ (by decide) (by decide)) hok.wr) hf h 16 (Nat.le_refl _)
  exact ⟨s', hs', hP, fun k hk b hb => by rw [hv k hk b hb, ite_eq_left hb], rest⟩

theorem scratch_of_arrays {s s' : State} (hfr : Frame [arraysR s] s.mem s'.mem) :
    Frame [workR s] s.mem s'.mem :=
  hfr.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨workR s, List.mem_singleton_self _, Offset.sub_base _ (by omega)⟩

/-- The step of the key pointer. -/
def stepW : Spec.Seed.Direction → BitVec 64
  | .encrypt => 8
  | .decrypt => -8

theorem exec_keyNext (d : Spec.Seed.Direction) (s : State) :
    exec (keyNext d) s = some (s.write .a0 (s.gpr .a0 + stepW d)) := by
  cases d
  · rw [keyNext, exec_addi (by decide)]; rfl
  · rw [keyNext, exec_addi (by decide)]; rfl

theorem exec_dec (s : State) (r : Reg) :
    exec (.addi r r (-1)) s = some (s.write r (s.gpr r - 1)) := by
  rw [exec_addi (by decide), show (-1 : Int) = -((1 : Nat) : Int) from rfl, RISCV64.Steps.add_ofInt_neg]
  rfl

theorem runBlock_trans {a b : List Instr} {s s' s'' : State} (h1 : runBlock isa a s = some s')
    (h2 : runBlock isa b s' = some s'') : runBlock isa (a ++ b) s = some s'' := by
  rw [runBlock_append, h1, Option.bind_some, h2]

theorem runBlock_sp {is : List Instr} {s s' : State} (h : runBlock isa is s = some s') : s'.sp = s.sp := by
  induction is generalizing s with
  | nil => rw [runBlock_nil] at h; cases h; rfl
  | cons i is ih =>
    rw [runBlock_cons] at h
    cases he : exec i s with
    | none => rw [he] at h; cases h
    | some s₁ => rw [he, runStep_some] at h; exact (ih h).trans (exec_sp he)

/-- The registers a round keeps or only steps. -/
def roundKeep : List Reg := [.ra, .a0, .a1, .a2, .a3, .a4, .a5]

theorem keepRegs : ∀ r ∈ roundKeep, r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t5 ∧ r ≠ .t6 := by decide

theorem notG16 : ∀ r ∈ roundKeep, r ∉ g16Writes := by decide

/-- The round key's two words, little-endian, from `a0`. -/
theorem keyLoad_ok {s : State} (hk0 : InRegions (s.rd ++ s.wr) (s.gpr .a0) 4)
    (hk1 : InRegions (s.rd ++ s.wr) (s.gpr .a0 + 4) 4) :
    ∃ s', runBlock isa (Impl.Words.RISCV64.loadLE32 k0R Impl.Aes.RISCV64.t0 .a0 0 ++
        Impl.Words.RISCV64.loadLE32 k1R Impl.Aes.RISCV64.t0 .a0 4) s = some s' ∧
      (s'.gpr .t5).setWidth 32 = s.mem.readW (s.gpr .a0) 32 ∧
      (s'.gpr .t6).setWidth 32 = s.mem.readW (s.gpr .a0 + 4) 32 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .t0 → r ≠ .t5 → r ≠ .t6 → s'.gpr r = s.gpr r) := by
  have h0 : InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 0) 4 := by
    simpa using hk0
  obtain ⟨s₁, hs₁, e₁⟩ := run_of_wp (ByteLoad.loadLE32_ok (s := s) (d := k0R) (tmp := .t0) (n := .a0)
    (off := 0) (by decide) (by decide) (by decide) (by decide) h0)
  have a1 : s₁.gpr .a0 = s.gpr .a0 := by
    rw [e₁, gpr_write_of_ne _ _ (by decide), gpr_write_of_ne _ _ (by decide)]
  have m1 : s₁.mem = s.mem := by rw [e₁]; rfl
  have rd1 : s₁.rd = s.rd := by rw [e₁]; rfl
  have wr1 : s₁.wr = s.wr := by rw [e₁]; rfl
  have sp1 : s₁.sp = s.sp := by rw [e₁]; rfl
  have k1 : (s₁.gpr .t5).setWidth 32 = s.mem.readW (s.gpr .a0) 32 := by
    rw [e₁, show Reg.t5 = k0R from rfl, gpr_write_self, lo32_ext]; simp
  have o1 : ∀ r, r ≠ .t0 → r ≠ .t5 → s₁.gpr r = s.gpr r := fun r h1 h2 => by
    rw [e₁, gpr_write_of_ne _ _ (show ¬ r = k0R from h2), gpr_write_of_ne _ _ h1]
  have h1 : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .a0 + BitVec.ofNat 64 4) 4 := by
    rw [rd1, wr1, a1]; exact hk1
  obtain ⟨s₂, hs₂, e₂⟩ := run_of_wp (ByteLoad.loadLE32_ok (d := k1R) (tmp := .t0) (n := .a0)
    (off := 4) (by decide) (by decide) (by decide) (by decide) h1)
  refine ⟨s₂, runBlock_trans hs₁ hs₂, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_⟩
  · rw [e₂, gpr_write_of_ne _ _ (show ¬ Reg.t5 = k1R by decide),
      gpr_write_of_ne _ _ (show ¬ Reg.t5 = .t0 by decide)]
    exact k1
  · rw [e₂, show Reg.t6 = k1R from rfl, gpr_write_self, lo32_ext]
    simp only [a1, m1]; rfl
  · rw [e₂]; exact m1
  · rw [e₂]; exact rd1
  · rw [e₂]; exact wr1
  · rw [e₂]; exact sp1
  · rw [e₂, gpr_write_of_ne _ _ (show ¬ r = k1R from h3), gpr_write_of_ne _ _ h1]
    exact o1 r h1 h2

theorem round_ok (d : Spec.Seed.Direction) {s : State} (h : Room s) (hm : Masks s)
    (hk0 : InRegions (s.rd ++ s.wr) (s.gpr .a0) 4)
    (hk1 : InRegions (s.rd ++ s.wr) (s.gpr .a0 + 4) 4) :
    ∃ s', runBlock isa (round d) s = some s' ∧
      (∀ b < 16, quad s' b =
        Spec.Seed.round (s.mem.readW (s.gpr .a0) 32, s.mem.readW (s.gpr .a0 + 4) 32) (quad s b)) ∧
      Room s' ∧ Masks s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.gpr .a0 = s.gpr .a0 + stepW d ∧ s'.gpr .a4 = s.gpr .a4 - 1 ∧
      s'.gpr .a1 = s.gpr .a1 ∧ s'.gpr .a2 = s.gpr .a2 ∧ s'.gpr .a3 = s.gpr .a3 ∧
      s'.gpr .a5 = s.gpr .a5 ∧ s'.gpr .ra = s.gpr .ra ∧
      Frame [workR s] s.mem s'.mem := by
  let K0 := s.mem.readW (s.gpr .a0) 32
  let K1 := s.mem.readW (s.gpr .a0 + 4) 32
  -- The round key.
  obtain ⟨s2, hrun2, hK0, hK1, m2, rd2, wr2, spp2, g2⟩ := keyLoad_ok hk0 hk1
  have hkeys : KeysIn K0 K1 s2 :=
    ⟨room_congr h (g2 _ (by decide) (by decide) (by decide)) wr2, hK0, hK1⟩
  have lv2 : ∀ k b, lv s2 k b = lv s k b := fun k b => by
    simp only [lv, laneA, m2, g2 sb (by decide) (by decide) (by decide)]
  have hm2 : Masks s2 := Masks.frame (s' := s2) hm (g2 _ (by decide) (by decide) (by decide))
    (g2 _ (by decide) (by decide) (by decide)) (by rw [m2]; exact Frame.refl _ _)
  -- The steps.
  obtain ⟨s3, hs3, hP3, hv3, fr3, rd3, wr3, spp3, rg3⟩ := lanes_ok (dests1 K0 K1) (reads1 K0 K1)
    (P := KeysIn K0 K1)
    (fun _ s s' hP hok => ⟨room_congr hP.1 (hok.regs _ (by decide) (by decide)) hok.wr,
      by rw [hok.regs _ (by decide) (by decide)]; exact hP.2.1,
      by rw [hok.regs _ (by decide) (by decide)]; exact hP.2.2⟩)
    (fun b hb s hs => step1_ok K0 K1 hb s hs) hkeys 16 (Nat.le_refl _)
  have hm3 : Masks s3 := hm2.frame (rg3 _ (by decide) (by decide)) (rg3 _ (by decide) (by decide))
    (scratch_of_arrays fr3)
  obtain ⟨s4, hs4, hg4, hk4, h4, hm4, rd4, wr4, spp4, rg4, fr4⟩ := g16_lanes hP3.1 hm3
  obtain ⟨s5, hs5, h5, hv5, fr5, rd5, wr5, spp5, rg5⟩ :=
    lanes16_room dests2 reads2 (fun b hb s hs => step2_ok hb s hs) h4
  have hm5 : Masks s5 := hm4.frame (rg5 _ (by decide) (by decide)) (rg5 _ (by decide) (by decide))
    (scratch_of_arrays fr5)
  obtain ⟨s6, hs6, hg6, hk6, h6, hm6, rd6, wr6, spp6, rg6, fr6⟩ := g16_lanes h5 hm5
  obtain ⟨s7, hs7, h7, hv7, fr7, rd7, wr7, spp7, rg7⟩ :=
    lanes16_room dests3 reads3 (fun b hb s hs => step3_ok hb s hs) h6
  have hm7 : Masks s7 := hm6.frame (rg7 _ (by decide) (by decide)) (rg7 _ (by decide) (by decide))
    (scratch_of_arrays fr7)
  obtain ⟨s8, hs8, hg8, hk8, h8, hm8, rd8, wr8, spp8, rg8, fr8⟩ := g16_lanes h7 hm7
  obtain ⟨s9, hs9, h9, hv9, fr9, rd9, wr9, spp9, rg9⟩ :=
    lanes16_room dests4 reads4 (fun b hb s hs => step4_ok hb s hs) h8
  obtain ⟨s10, hs10, hsw, hlow, rd10, wr10, spp10, rg10, fr10⟩ := swap_ok h9
  let s11 := s10.write .a0 (s10.gpr .a0 + stepW d)
  let s12 := s11.write .a4 (s11.gpr .a4 - 1)
  have hrun : runBlock isa [keyNext d, .addi .a4 .a4 (-1)] s10 = some s12 := by
    rw [runBlock_cons, exec_keyNext, runStep_some, runBlock_cons, exec_dec _ .a4, runStep_some,
      runBlock_nil]
  -- Registers through the steps.
  have keep : ∀ r ∈ roundKeep, s10.gpr r = s.gpr r := by
    intro r hr
    have hg := notG16 r hr
    obtain ⟨h1, h2, h3, h4⟩ := keepRegs r hr
    rw [rg10 r h1 h2, rg9 r h1 h2, rg8 r hg, rg7 r h1 h2, rg6 r hg, rg5 r h1 h2, rg4 r hg,
      rg3 r h1 h2, g2 r h1 h3 h4]
  have sb10 : s10.gpr sb = s.gpr sb := keep _ (by decide)
  have g12 : ∀ r, r ≠ .a0 → r ≠ .a4 → s12.gpr r = s10.gpr r := fun r a b => by
    simp [s12, s11, gpr_write, a, b]
  have sb12 : s12.gpr sb = s.gpr sb := by rw [g12 _ (by decide) (by decide), sb10]
  have lv12 : ∀ k b, lv s12 k b = lv s10 k b := fun k b => by
    simp only [lv, laneA, s12, s11, mem_write, sb12, sb10]
  -- The frames, all in the working area.
  have fc : ∀ {t : State} {m m' : Mem}, t.gpr sb = s.gpr sb → Frame [workR t] m m' →
      Frame [workR s] m m' := fun ht hf => by simpa [workR, ht] using hf
  have sb3 : s3.gpr sb = s.gpr sb := by
    rw [rg3 _ (by decide) (by decide), g2 _ (by decide) (by decide) (by decide)]
  have sb4 : s4.gpr sb = s.gpr sb := by rw [rg4 _ (by decide), sb3]
  have sb5 : s5.gpr sb = s.gpr sb := by rw [rg5 _ (by decide) (by decide), sb4]
  have sb6 : s6.gpr sb = s.gpr sb := by rw [rg6 _ (by decide), sb5]
  have sb7 : s7.gpr sb = s.gpr sb := by rw [rg7 _ (by decide) (by decide), sb6]
  have sb8 : s8.gpr sb = s.gpr sb := by rw [rg8 _ (by decide), sb7]
  have sb9 : s9.gpr sb = s.gpr sb := by rw [rg9 _ (by decide) (by decide), sb8]
  have fr : Frame [workR s] s.mem s12.mem := by
    simp only [s12, s11, mem_write]
    refine (fc rfl (show Frame [workR s] s.mem s2.mem by rw [m2]; exact Frame.refl _ _)).trans ?_
    refine (fc (g2 _ (by decide) (by decide) (by decide)) (scratch_of_arrays fr3)).trans ?_
    refine (fc sb3 fr4).trans ?_
    refine (fc sb4 (scratch_of_arrays fr5)).trans ?_
    refine (fc sb5 fr6).trans ?_
    refine (fc sb6 (scratch_of_arrays fr7)).trans ?_
    refine (fc sb7 fr8).trans ?_
    refine (fc sb8 (scratch_of_arrays fr9)).trans ?_
    exact fc sb9 fr10
  have wr12 : s12.wr = s.wr := by
    simp only [s12, s11, wr_write, wr10, wr9, wr8, wr7, wr6, wr5, wr4, wr3, wr2]
  refine ⟨s12, ?_, fun b hb => ?_, room_congr h sb12 wr12, ?_, ?_, wr12, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, fr⟩
  · exact runBlock_trans (runBlock_trans (runBlock_trans (runBlock_trans (runBlock_trans
      (runBlock_trans (runBlock_trans (runBlock_trans (runBlock_trans hrun2 hs3) hs4) hs5) hs6)
      hs7) hs8) hs9) hs10) hrun
  · -- The values, stage by stage.
    have t3 : lv s3 (tSlot 0) b = (lv s (arrSlot 2) b ^^^ K0) ^^^ (lv s (arrSlot 3) b ^^^ K1) := by
      rw [hv3 _ mem_tA b hb, ite_eq_left hb]
      simp [newVal, sp1, lv2, tSlot, aSlot, arrSlot, BitVec.xor_assoc]
    have a3 : lv s3 aSlot b = lv s (arrSlot 2) b ^^^ K0 := by
      rw [hv3 _ mem_aA b hb, ite_eq_left hb]
      simp [newVal, sp1, lv2, tSlot, aSlot, arrSlot]
    have o3 : ∀ k ∈ [arrSlot 0, arrSlot 1, arrSlot 2, arrSlot 3], lv s3 k b = lv s k b := by
      intro k hk
      have hk' : k ∈ arrays := by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> decide
      rw [hv3 _ hk' b hb, ite_eq_left hb]
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> simp [newVal, sp1, lv2, tSlot, aSlot, arrSlot]
    -- c
    have t4 : lv s4 (tSlot 0) b = Spec.Seed.g (lv s3 (tSlot 0) b) := hg4 b hb
    have k4 : ∀ k ∈ arrays, k ≠ tSlot 0 → lv s4 k b = lv s3 k b := fun k hk hkt => hk4 k hk hkt b hb
    have t5 : lv s5 (tSlot 0) b = lv s4 (tSlot 0) b + lv s4 aSlot b := by
      rw [hv5 _ mem_tA b hb]; simp [newVal, sp2, tSlot, aSlot, cSlot]
    have c5 : lv s5 cSlot b = lv s4 (tSlot 0) b := by
      rw [hv5 _ mem_cA b hb]; simp [newVal, sp2, tSlot, aSlot, cSlot]
    have o5 : ∀ k ∈ arrays, k ≠ tSlot 0 → k ≠ cSlot → lv s5 k b = lv s4 k b := by
      intro k hk h1 h2; rw [hv5 _ hk b hb]; simp [newVal, sp2, Ne.symm h1, Ne.symm h2]
    -- d
    have t6 : lv s6 (tSlot 0) b = Spec.Seed.g (lv s5 (tSlot 0) b) := hg6 b hb
    have k6 : ∀ k ∈ arrays, k ≠ tSlot 0 → lv s6 k b = lv s5 k b := fun k hk hkt => hk6 k hk hkt b hb
    have t7 : lv s7 (tSlot 0) b = lv s6 (tSlot 0) b + lv s6 cSlot b := by
      rw [hv7 _ mem_tA b hb]; simp [newVal, sp3, tSlot, dSlot, cSlot]
    have d7 : lv s7 dSlot b = lv s6 (tSlot 0) b := by
      rw [hv7 _ mem_dA b hb]; simp [newVal, sp3, tSlot, dSlot, cSlot]
    have o7 : ∀ k ∈ arrays, k ≠ tSlot 0 → k ≠ dSlot → lv s7 k b = lv s6 k b := by
      intro k hk h1 h2; rw [hv7 _ hk b hb]; simp [newVal, sp3, Ne.symm h1, Ne.symm h2]
    -- e
    have t8 : lv s8 (tSlot 0) b = Spec.Seed.g (lv s7 (tSlot 0) b) := hg8 b hb
    have k8 : ∀ k ∈ arrays, k ≠ tSlot 0 → lv s8 k b = lv s7 k b := fun k hk hkt => hk8 k hk hkt b hb
    have l0_9 : lv s9 (arrSlot 0) b = (lv s8 (tSlot 0) b + lv s8 dSlot b) ^^^ lv s8 (arrSlot 0) b := by
      rw [hv9 _ mem_L0 b hb]; simp [newVal, sp4, arrSlot]
    have l1_9 : lv s9 (arrSlot 1) b = lv s8 (arrSlot 1) b ^^^ lv s8 (tSlot 0) b := by
      rw [hv9 _ mem_L1 b hb]; simp [newVal, sp4, arrSlot]
    have r0_9 : lv s9 (arrSlot 2) b = lv s8 (arrSlot 2) b := by
      rw [hv9 _ mem_R0 b hb]; simp [newVal, sp4, arrSlot]
    have r1_9 : lv s9 (arrSlot 3) b = lv s8 (arrSlot 3) b := by
      rw [hv9 _ mem_R1 b hb]; simp [newVal, sp4, arrSlot]
    -- The arrays other than `G`'s words, through the `G`s and the steps that do not write them.
    have xs : ∀ k ∈ [arrSlot 0, arrSlot 1, arrSlot 2, arrSlot 3],
        lv s8 k b = lv s k b := by
      intro k hk
      have hk' : k ∈ arrays := by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> decide
      have hkt : k ≠ tSlot 0 := by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> decide
      have hkc : k ≠ cSlot := by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> decide
      have hkd : k ≠ dSlot := by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl <;> decide
      rw [k8 k hk' hkt, o7 k hk' hkt hkd, k6 k hk' hkt, o5 k hk' hkt hkc, k4 k hk' hkt, o3 k hk]
    have a4 : lv s4 aSlot b = lv s3 aSlot b := k4 _ mem_aA (by decide)
    have c6 : lv s6 cSlot b = lv s5 cSlot b := k6 _ mem_cA (by decide)
    have d8 : lv s8 dSlot b = lv s7 dSlot b := k8 _ mem_dA (by decide)
    simp only [quad, lv12, hsw 0 (by decide) b hb, hsw 1 (by decide) b hb, hsw 2 (by decide) b hb,
      hsw 3 (by decide) b hb]
    simp only [show (0 + 2) % 4 = 2 from rfl, show (1 + 2) % 4 = 3 from rfl,
      show (2 + 2) % 4 = 0 from rfl, show (3 + 2) % 4 = 1 from rfl]
    simp only [r0_9, r1_9, l0_9, l1_9]
    simp only [xs (arrSlot 0) (by simp), xs (arrSlot 1) (by simp), xs (arrSlot 2) (by simp),
      xs (arrSlot 3) (by simp), d8, d7, t8, t7, c6, c5, t6, t5, t4, a4, a3, t3]
    simp only [Spec.Seed.round, Spec.Seed.f, K0, K1, BitVec.xor_comm (lv s (arrSlot 0) b),
      BitVec.xor_comm (lv s (arrSlot 1) b)]
  · exact hm.frame sb12 (by rw [g12 _ (by decide) (by decide), keep _ (by decide)]) fr
  · simp only [s12, s11, rd_write, rd10, rd9, rd8, rd7, rd6, rd5, rd4, rd3, rd2]
  · simp only [s12, s11, sp_write, spp10, spp9, spp8, spp7, spp6, spp5, spp4, spp3, spp2]
  · simp [s12, s11, gpr_write, keep _ (show Reg.a0 ∈ roundKeep by decide)]
  · simp [s12, s11, gpr_write, keep _ (show Reg.a4 ∈ roundKeep by decide)]
  · rw [g12 _ (by decide) (by decide), keep _ (by decide)]
  · rw [g12 _ (by decide) (by decide), keep _ (by decide)]
  · rw [g12 _ (by decide) (by decide), keep _ (by decide)]
  · rw [g12 _ (by decide) (by decide), keep _ (by decide)]
  · rw [g12 _ (by decide) (by decide), keep _ (by decide)]

end VG.Proof.Seed.RISCV64
