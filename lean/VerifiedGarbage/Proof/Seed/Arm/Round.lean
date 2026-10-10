import VerifiedGarbage.Proof.Seed.Arm.Steps

/-!
# A round on ARMv7

`g8_lanes` restates `g8_ok` on the lanes of the arrays, and `round_ok` puts
the steps of a round together: on every lane, `round l r`, with `L` at `l`
and `R` at `r`, does RFC 4269 §2's round (`Spec.Seed.round`, which then
exchanges the halves) to `(L0, L1, R0, R1)`, with the round key in the
slots `k` and `k + 1`, at `kp`: the new `L` is the old `R`, at `r`, and the
new `R` is at `l` (`quadAt`).
-/

namespace VG.Proof.Seed.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Seed.Arm
open VG.Impl.Aes.Arm (sb t0 t1 u7 kp ldS stS eorR)
open VG.Arm.Straight (wordAddr Ok slotRegion add_ofNat_ofNat)
open VG.Proof.Aes.Arm (layerWrites)

theorem room_ok_gCfg {s : State} (h : Room s) : Ok gCfg s where
  slotIn k hk := ⟨_, h.mem, slot_in h (by simp [gCfg] at hk; rw [slots_eq]; omega)⟩
  extIn k hk := by simp [gCfg] at hk
  slots := by have := h.fit; simp [gCfg, slots_eq] at this ⊢; omega
  sep k _ j hj := by simp [gCfg] at hj

/-- `g8` on the lanes: `G` of `G`'s words, the other arrays and the slots
from the arrays' kept. -/
theorem g8_lanes {s : State} (h : Room s) :
    ∃ s', runBlock isa g8 s = some s' ∧
      (∀ w < 8, lv s' (tSlot 0) w = Spec.Seed.g (lv s (tSlot 0) w)) ∧
      (∀ k, 56 ≤ k → k < slots → slotW s' k = slotW s k) ∧
      Room s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧ Frame [workR s] s.mem s'.mem := by
  obtain ⟨s', hs', hg, hrd, hwr, hsp, hregs, hfr⟩ := g8_ok (room_ok_gCfg h)
  have hsb : s'.gpr sb = s.gpr sb := hregs _ (by decide)
  have hf := h.fit; rw [slots_eq] at hf
  have := toNat_addr (s.gpr sb)
  refine ⟨s', hs', fun w hw => ?_, fun k hk1 hk2 => ?_, h.congr hsb hwr, hrd, hwr, hsp, hregs, ?_⟩
  · rw [lv, lv, ← tSlot_lane]; exact hg w hw
  · rw [slots_eq] at hk2
    simp only [slotW, hsb]
    refine hfr.readW (r := ⟨wordAddr (s.gpr sb) k, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    rw [slot_addr (by omega)]
    exact Offset.disjoint_base _ (by simp [gCfg]; omega) (by omega)
  · refine hfr.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨workR s, List.mem_singleton_self _, Region.sub_prefix (by simp [gCfg, tailSlot])⟩

/-! ## The round -/

/-- Lane `b` of the blocks' state, `L` at `l` and `R` at `r`: `(L0, L1, R0, R1)`. -/
def quadAt (s : State) (l r b : Nat) :
    Spec.Seed.Word × Spec.Seed.Word × Spec.Seed.Word × Spec.Seed.Word :=
  (lv s l b, lv s (l + 8) b, lv s r b, lv s (r + 8) b)

theorem reads1 {r : Nat} (hr : r ∈ halves) (k0 k1 : BitVec 32) : ReadsArrays (sp1 r k0 k1) := by
  obtain ⟨hR, hR8, -⟩ := half_mem hr
  intro kv hkv x y h
  simp only [sp1, List.mem_cons, List.not_mem_nil, or_false] at hkv
  rcases hkv with rfl | rfl <;> simp only [h _ hR, h _ hR8]

theorem reads2 : ReadsArrays sp2 := by
  intro kv hkv x y h
  simp only [sp2, List.mem_cons, List.not_mem_nil, or_false] at hkv
  rcases hkv with rfl | rfl <;> simp only [h _ mem_tA, h _ mem_aA]

theorem reads3 : ReadsArrays sp3 := by
  intro kv hkv x y h
  simp only [sp3, List.mem_cons, List.not_mem_nil, or_false] at hkv
  rcases hkv with rfl | rfl <;> simp only [h _ mem_tA, h _ mem_cA]

theorem reads4 {l : Nat} (hl : l ∈ halves) : ReadsArrays (sp4 l) := by
  obtain ⟨hL, hL8, -⟩ := half_mem hl
  intro kv hkv x y h
  simp only [sp4, List.mem_cons, List.not_mem_nil, or_false] at hkv
  rcases hkv with rfl | rfl <;> simp only [h _ mem_tA, h _ mem_dA, h _ hL, h _ hL8]

theorem dests1 {r : Nat} (k0 k1 : BitVec 32) : ∀ kv ∈ sp1 r k0 k1, kv.1 ∈ arrays := by
  intro kv hkv; simp only [sp1, List.mem_cons, List.not_mem_nil, or_false] at hkv
  rcases hkv with rfl | rfl
  · exact mem_aA
  · exact mem_tA
theorem dests2 : ∀ kv ∈ sp2, kv.1 ∈ arrays := by
  intro kv hkv; simp only [sp2, List.mem_cons, List.not_mem_nil, or_false] at hkv
  rcases hkv with rfl | rfl <;> decide
theorem dests3 : ∀ kv ∈ sp3, kv.1 ∈ arrays := by
  intro kv hkv; simp only [sp3, List.mem_cons, List.not_mem_nil, or_false] at hkv
  rcases hkv with rfl | rfl <;> decide
theorem dests4 {l : Nat} (hl : l ∈ halves) : ∀ kv ∈ sp4 l, kv.1 ∈ arrays := by
  obtain ⟨hL, hL8, -⟩ := half_mem hl
  intro kv hkv; simp only [sp4, List.mem_cons, List.not_mem_nil, or_false] at hkv
  rcases hkv with rfl | rfl
  · exact hL8
  · exact hL

/-- A step on all eight lanes, from a state where the scratch buffer is writable. -/
theorem lanes8_room {f : Nat → List Instr} {sp : LaneSpec} (hsp : ∀ kv ∈ sp, kv.1 ∈ arrays)
    (hd : ReadsArrays sp)
    (hf : ∀ b < 8, ∀ s, Room s → ∃ s', runBlock isa (f b) s = some s' ∧ LaneOk s s' sp b)
    {s : State} (h : Room s) :
    ∃ s', runBlock isa (lanes8 f) s = some s' ∧ Room s' ∧
      (∀ k ∈ arrays, ∀ b < 8, lv s' k b = newVal sp k (fun k' => lv s k' b)) ∧
      Frame [arraysR s] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) := by
  obtain ⟨s', hs', hP, hv, rest⟩ := lanes_ok hsp hd (P := Room)
    (fun _ s s' hP hok => hP.congr (hok.regs _ (by decide) (by decide)) hok.wr) (fun _ h => h) hf h 8
    (Nat.le_refl _)
  exact ⟨s', hs', hP, fun k hk b hb => by rw [hv k hk b hb, ite_eq_left hb], rest⟩

theorem work_of_arrays {s s' : State} (hfr : Frame [arraysR s] s.mem s'.mem) :
    Frame [workR s] s.mem s'.mem :=
  hfr.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨workR s, List.mem_singleton_self _, arraysR_sub_work s⟩

theorem runBlock_trans {a b : List Instr} {s s' s'' : State} (h1 : runBlock isa a s = some s')
    (h2 : runBlock isa b s' = some s'') : runBlock isa (a ++ b) s = some s'' := by
  rw [runBlock_append, h1, Option.bind_some, h2]

/-- A slot from the arrays' end on is kept by a frame of the working area. -/
theorem slot_keep_work {s s' : State} (h : Room s) (hfr : Frame [workR s] s.mem s'.mem)
    (hsb : s'.gpr sb = s.gpr sb) {k : Nat} (hk1 : tailSlot ≤ k) (hk2 : k < slots) :
    slotW s' k = slotW s k := by
  have hf := h.fit; rw [slots_eq] at hf hk2
  have := toNat_addr (s.gpr sb)
  simp only [slotW, hsb]
  refine hfr.readW (r := ⟨wordAddr (s.gpr sb) k, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  rw [slot_addr (by omega)]
  exact Offset.disjoint_base _ (by simp [tailSlot] at hk1 ⊢; omega) (by omega)

theorem keepRegs : ∀ r ∈ [Reg.r8, .r9], r ≠ t0 ∧ r ≠ t1 ∧ r ∉ layerWrites := by decide

/-- The round key at `kp`, slots `k` and `k + 1`. -/
def KeyAt (s : State) (k : Nat) : Prop := s.gpr kp = s.gpr sb + BitVec.ofNat 32 (4 * k)

theorem round_ok {l r : Nat} (hl : l ∈ halves) (hr : r ∈ halves) (hlr : l ≠ r) {s : State} (h : Room s)
    {k : Nat} (hk2 : k + 1 < slots) (hkp : KeyAt s k) :
    ∃ s', runBlock isa (round l r) s = some s' ∧
      (∀ b < 8, quadAt s' r l b = Spec.Seed.round (slotW s k, slotW s (k + 1)) (quadAt s l r b)) ∧
      Room s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.gpr kp = s.gpr kp + 8 ∧ s'.gpr sb = s.gpr sb ∧
      (∀ j, tailSlot ≤ j → j < slots → slotW s' j = slotW s j) ∧
      Frame [workR s] s.mem s'.mem := by
  have hf := h.fit; rw [slots_eq] at hf hk2
  have hT : tailSlot = 112 := rfl
  let K0 := slotW s k
  let K1 := slotW s (k + 1)
  obtain ⟨hL, hL8, hLt, hLa, hLc, hLd, hL8t, hL8a, hL8c, hL8d, hLL⟩ := half_mem hl
  obtain ⟨hR, hR8, hRt, hRa, hRc, hRd, hR8t, hR8a, hR8c, hR8d, hRR⟩ := half_mem hr
  have hlr8 : l ≠ r + 8 ∧ l + 8 ≠ r ∧ l + 8 ≠ r + 8 := by
    simp only [halves, List.mem_cons, List.not_mem_nil, or_false] at hl hr
    rcases hl with rfl | rfl <;> rcases hr with rfl | rfl <;> first | exact absurd rfl hlr | decide
  -- The round key.
  have ek : ∀ d, d = 0 ∨ d = 4 → s.gpr kp + BitVec.ofNat 32 d = s.gpr sb + BitVec.ofNat 32 (4 * (k + d / 4)) := by
    intro d hd
    rw [hkp, add_ofNat_ofNat]; rcases hd with rfl | rfl <;> rfl
  have e1 : exec (.ldr u7 kp 0) s = some (s.setReg u7 K0) := by
    rw [exec_ldr (by decide) (by rw [ek 0 (.inl rfl)]; exact ⟨_, List.mem_append_right _ h.mem,
      slot_in h (by rw [slots_eq]; omega)⟩), ek 0 (.inl rfl)]; rfl
  have e2 : exec (.ldr .lr kp 4) (s.setReg u7 K0) = some ((s.setReg u7 K0).setReg .lr K1) := by
    rw [exec_ldr (by decide) (by
      rw [gpr_setReg_of_ne _ _ (by decide), ek 4 (.inr rfl), rd_setReg, wr_setReg]
      exact ⟨_, List.mem_append_right _ h.mem, slot_in h (by rw [slots_eq]; omega)⟩),
      gpr_setReg_of_ne _ _ (by decide), ek 4 (.inr rfl), mem_setReg]; rfl
  let s2 := (s.setReg u7 K0).setReg .lr K1
  have hrun2 : runBlock isa [.ldr u7 kp 0, .ldr .lr kp 4] s = some s2 := by
    rw [runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_nil]
  have g2 : ∀ r, r ≠ u7 → r ≠ .lr → s2.gpr r = s.gpr r := fun r h1 h2 => by
    simp only [s2, gpr_setReg_of_ne _ _ h1, gpr_setReg_of_ne _ _ h2]
  have h2 : Room s2 := room_setReg (room_setReg h (by decide) _) (by decide) _
  have hkeys : KeysIn K0 K1 s2 := ⟨h2, by
      show ((s.setReg u7 K0).setReg .lr K1).gpr u7 = K0
      rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_self], gpr_setReg_self _ _ _⟩
  have lv2 : ∀ k b, lv s2 k b = lv s k b := fun k b => by
    simp only [lv, s2, slotW_setReg _ (show (Reg.lr) ≠ sb by decide), slotW_setReg _ (show u7 ≠ sb by decide)]
  -- The steps.
  obtain ⟨s3, hs3, hP3, hv3, fr3, rd3, wr3, spp3, rg3⟩ := lanes_ok (dests1 (r := r) K0 K1) (reads1 hr K0 K1)
    (P := KeysIn K0 K1)
    (fun _ s s' hP hok => ⟨hP.1.congr (hok.regs _ (by decide) (by decide)) hok.wr,
      by rw [hok.regs _ (by decide) (by decide)]; exact hP.2.1,
      by rw [hok.regs _ (by decide) (by decide)]; exact hP.2.2⟩)
    (fun _ h => h.1) (fun b hb s hs => step1_ok hr K0 K1 hb s hs) hkeys 8 (Nat.le_refl _)
  obtain ⟨s4, hs4, hg4, hk4, h4, rd4, wr4, spp4, rg4, fr4⟩ := g8_lanes hP3.1
  obtain ⟨s5, hs5, h5, hv5, fr5, rd5, wr5, spp5, rg5⟩ :=
    lanes8_room dests2 reads2 (fun b hb s hs => step2_ok hb s hs) h4
  obtain ⟨s6, hs6, hg6, hk6, h6, rd6, wr6, spp6, rg6, fr6⟩ := g8_lanes h5
  obtain ⟨s7, hs7, h7, hv7, fr7, rd7, wr7, spp7, rg7⟩ :=
    lanes8_room dests3 reads3 (fun b hb s hs => step3_ok hb s hs) h6
  obtain ⟨s8, hs8, hg8, hk8, h8, rd8, wr8, spp8, rg8, fr8⟩ := g8_lanes h7
  obtain ⟨s9, hs9, h9, hv9, fr9, rd9, wr9, spp9, rg9⟩ :=
    lanes8_room (dests4 hl) (reads4 hl) (fun b hb s hs => step4_ok hl hb s hs) h8
  let s10 := s9.setReg kp (s9.gpr kp + 8)
  have hrun : runBlock isa [.dp .add kp kp (.imm 8)] s9 = some s10 := by
    rw [runBlock_cons, show exec (.dp .add kp kp (.imm 8)) s9 = some s10 by simp [exec, Op2.eval, s10]; decide,
      runStep_some, runBlock_nil]
  -- Registers through the steps.
  have keep : ∀ r ∈ [Reg.r8, .r9], s9.gpr r = s.gpr r := by
    intro r hr
    obtain ⟨h1, h2, hg⟩ := keepRegs r hr
    have h3 : r ≠ u7 ∧ r ≠ .lr := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> decide
    rw [rg9 r h1 h2, rg8 r hg, rg7 r h1 h2, rg6 r hg, rg5 r h1 h2, rg4 r hg, rg3 r h1 h2, g2 r h3.1 h3.2]
  have sb9 : s9.gpr sb = s.gpr sb := keep _ (by decide)
  have sb10 : s10.gpr sb = s.gpr sb := by rw [gpr_setReg_of_ne _ _ (by decide), sb9]
  have lv10 : ∀ k b, lv s10 k b = lv s9 k b := fun k b => slotW_setReg _ (by decide) _ _
  -- The working area's frames.
  have fc : ∀ {t : State} {m m' : Mem}, t.gpr sb = s.gpr sb → Frame [workR t] m m' →
      Frame [workR s] m m' := fun ht hf => by simpa [workR, ht] using hf
  have sb3 : s3.gpr sb = s.gpr sb := by rw [rg3 _ (by decide) (by decide), g2 _ (by decide) (by decide)]
  have sb4 : s4.gpr sb = s.gpr sb := by rw [rg4 _ (by decide), sb3]
  have sb5 : s5.gpr sb = s.gpr sb := by rw [rg5 _ (by decide) (by decide), sb4]
  have sb6 : s6.gpr sb = s.gpr sb := by rw [rg6 _ (by decide), sb5]
  have sb7 : s7.gpr sb = s.gpr sb := by rw [rg7 _ (by decide) (by decide), sb6]
  have sb8 : s8.gpr sb = s.gpr sb := by rw [rg8 _ (by decide), sb7]
  have frame : Frame [workR s] s.mem s10.mem := by
    simp only [s10, mem_setReg]
    refine (fc (g2 _ (by decide) (by decide)) (work_of_arrays fr3)).trans ?_
    refine (fc sb3 fr4).trans ?_
    refine (fc sb4 (work_of_arrays fr5)).trans ?_
    refine (fc sb5 fr6).trans ?_
    refine (fc sb6 (work_of_arrays fr7)).trans ?_
    refine (fc sb7 fr8).trans ?_
    exact fc sb8 (work_of_arrays fr9)
  refine ⟨s10, ?_, fun b hb => ?_, h9.congr (gpr_setReg_of_ne _ _ (by decide)) rfl, ?_, ?_, ?_, ?_, sb10, fun j hj1 hj2 => ?_, frame⟩
  · exact runBlock_trans (runBlock_trans (runBlock_trans (runBlock_trans (runBlock_trans
      (runBlock_trans (runBlock_trans (runBlock_trans hrun2 hs3) hs4) hs5) hs6) hs7) hs8) hs9) hrun
  · -- The values, stage by stage.
    have t3 : lv s3 (tSlot 0) b = (lv s r b ^^^ K0) ^^^ (lv s (r + 8) b ^^^ K1) := by
      rw [hv3 _ mem_tA b hb, ite_eq_left hb]
      simp [newVal, sp1, lv2, tSlot, aSlot, BitVec.xor_assoc]
    have a3 : lv s3 aSlot b = lv s r b ^^^ K0 := by
      rw [hv3 _ mem_aA b hb, ite_eq_left hb]
      simp [newVal, sp1, lv2, tSlot, aSlot]
    have o3 : ∀ k ∈ [l, l + 8, r, r + 8], lv s3 k b = lv s k b := by
      intro k hk
      have hk' : k ∈ arrays ∧ k ≠ aSlot ∧ k ≠ tSlot 0 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl
        exacts [⟨hL, hLa, hLt⟩, ⟨hL8, hL8a, hL8t⟩, ⟨hR, hRa, hRt⟩, ⟨hR8, hR8a, hR8t⟩]
      rw [hv3 _ hk'.1 b hb, ite_eq_left hb]
      simp [newVal, sp1, lv2, Ne.symm hk'.2.1, Ne.symm hk'.2.2]
    -- c
    have k4 : ∀ k ∈ arrays, k ≠ tSlot 0 → lv s4 k b = lv s3 k b := fun k hk hkt => by
      have := arrays_bound k hk
      have hk56 : 56 ≤ k := by
        simp only [arrays, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hkt | decide
      exact hk4 _ (by omega) (by rw [slots_eq]; omega)
    have t5 : lv s5 (tSlot 0) b = lv s4 (tSlot 0) b + lv s4 aSlot b := by
      rw [hv5 _ mem_tA b hb]; simp [newVal, sp2, tSlot, cSlot]
    have c5 : lv s5 cSlot b = lv s4 (tSlot 0) b := by
      rw [hv5 _ mem_cA b hb]; simp [newVal, sp2, tSlot, cSlot]
    have o5 : ∀ k ∈ arrays, k ≠ tSlot 0 → k ≠ cSlot → lv s5 k b = lv s4 k b := by
      intro k hk h1 h2; rw [hv5 _ hk b hb]; simp [newVal, sp2, Ne.symm h1, Ne.symm h2]
    -- d
    have k6 : ∀ k ∈ arrays, k ≠ tSlot 0 → lv s6 k b = lv s5 k b := fun k hk hkt => by
      have := arrays_bound k hk
      have hk56 : 56 ≤ k := by
        simp only [arrays, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hkt | decide
      exact hk6 _ (by omega) (by rw [slots_eq]; omega)
    have t7 : lv s7 (tSlot 0) b = lv s6 (tSlot 0) b + lv s6 cSlot b := by
      rw [hv7 _ mem_tA b hb]; simp [newVal, sp3, tSlot, dSlot]
    have d7 : lv s7 dSlot b = lv s6 (tSlot 0) b := by
      rw [hv7 _ mem_dA b hb]; simp [newVal, sp3, tSlot, dSlot]
    have o7 : ∀ k ∈ arrays, k ≠ tSlot 0 → k ≠ dSlot → lv s7 k b = lv s6 k b := by
      intro k hk h1 h2; rw [hv7 _ hk b hb]; simp [newVal, sp3, Ne.symm h1, Ne.symm h2]
    -- e
    have k8 : ∀ k ∈ arrays, k ≠ tSlot 0 → lv s8 k b = lv s7 k b := fun k hk hkt => by
      have := arrays_bound k hk
      have hk56 : 56 ≤ k := by
        simp only [arrays, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hkt | decide
      exact hk8 _ (by omega) (by rw [slots_eq]; omega)
    have l0_9 : lv s9 l b = (lv s8 (tSlot 0) b + lv s8 dSlot b) ^^^ lv s8 l b := by
      rw [hv9 _ hL b hb]; simp [newVal, sp4]
    have l1_9 : lv s9 (l + 8) b = lv s8 (l + 8) b ^^^ lv s8 (tSlot 0) b := by
      rw [hv9 _ hL8 b hb]; simp [newVal, sp4]
    have r0_9 : lv s9 r b = lv s8 r b := by
      rw [hv9 _ hR b hb]; simp [newVal, sp4, hlr, hlr8.2.1]
    have r1_9 : lv s9 (r + 8) b = lv s8 (r + 8) b := by
      rw [hv9 _ hR8 b hb]; simp [newVal, sp4, hlr8.1, hlr]
    -- The halves, through the `G`s and the steps that do not write them.
    have xs : ∀ k ∈ [l, l + 8, r, r + 8], lv s8 k b = lv s k b := by
      intro k hk
      have hk' : k ∈ arrays ∧ k ≠ tSlot 0 ∧ k ≠ cSlot ∧ k ≠ dSlot := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl
        exacts [⟨hL, hLt, hLc, hLd⟩, ⟨hL8, hL8t, hL8c, hL8d⟩, ⟨hR, hRt, hRc, hRd⟩, ⟨hR8, hR8t, hR8c, hR8d⟩]
      rw [k8 k hk'.1 hk'.2.1, o7 k hk'.1 hk'.2.1 hk'.2.2.2, k6 k hk'.1 hk'.2.1, o5 k hk'.1 hk'.2.1 hk'.2.2.1,
        k4 k hk'.1 hk'.2.1, o3 k hk]
    have t4 : lv s4 (tSlot 0) b = Spec.Seed.g (lv s3 (tSlot 0) b) := hg4 b hb
    have t6 : lv s6 (tSlot 0) b = Spec.Seed.g (lv s5 (tSlot 0) b) := hg6 b hb
    have t8 : lv s8 (tSlot 0) b = Spec.Seed.g (lv s7 (tSlot 0) b) := hg8 b hb
    have a4 : lv s4 aSlot b = lv s3 aSlot b := k4 _ mem_aA (by decide)
    have c6 : lv s6 cSlot b = lv s5 cSlot b := k6 _ mem_cA (by decide)
    have d8 : lv s8 dSlot b = lv s7 dSlot b := k8 _ mem_dA (by decide)
    simp only [quadAt, lv10, r0_9, r1_9, l0_9, l1_9]
    simp only [xs l (by simp), xs (l + 8) (by simp), xs r (by simp), xs (r + 8) (by simp), d8, d7, t8, t7,
      c6, c5, t6, t5, t4, a4, a3, t3]
    simp only [Spec.Seed.round, Spec.Seed.f, K0, K1, BitVec.xor_comm (lv s l b),
      BitVec.xor_comm (lv s (l + 8) b)]
  · simp only [s10, rd_setReg, rd9, rd8, rd7, rd6, rd5, rd4, rd3]; rfl
  · simp only [s10, wr_setReg, wr9, wr8, wr7, wr6, wr5, wr4, wr3]; rfl
  · simp only [s10, sp_setReg, spp9, spp8, spp7, spp6, spp5, spp4, spp3]; rfl
  · rw [show s10.gpr kp = s9.gpr kp + 8 from gpr_setReg_self _ _ _, show s9.gpr kp = s.gpr kp from keep _ (by decide)]
  · rw [show slotW s10 j = slotW s9 j from slotW_setReg _ (by decide) _ _]
    exact slot_keep_work h (by simpa only [s10, mem_setReg] using frame) sb9 hj1 hj2

end VG.Proof.Seed.Arm
