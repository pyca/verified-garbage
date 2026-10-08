import VerifiedGarbage.Proof.Seed.X86_64.Swap

/-!
# A round on x86-64

`g16_lanes` restates `g16_ok` on the lanes of the arrays, and `round_ok`
puts the steps of a round together: on every lane, the round's code does
RFC 4269 §2's round (`Spec.Seed.round`) to the arrays of `L0`, `L1`, `R0`,
`R1`, with the round key at `rdi`.
-/

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.X86_64.RegUpd VG.Impl.Seed.X86_64

theorem room_ok_gCfg {s : State} (h : Room s) : Ok gCfg s := ok_of_room h rfl (by decide) rfl

theorem sb_eq : Impl.Aes.X86_64.sb = .r9 := rfl

/-- `g16` on the lanes: `G` of `G`'s words, the other arrays kept. -/
theorem g16_lanes {s : State} (h : Room s) (hm : MasksIn s) :
    ∃ s', runBlock isa g16 s = some s' ∧
      (∀ w < 16, lv s' (tSlot 0) w = Spec.Seed.g (lv s (tSlot 0) w)) ∧
      (∀ k ∈ arrays, k ≠ tSlot 0 → ∀ b < 16, lv s' k b = lv s k b) ∧
      MasksIn s' ∧ Room s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ∉ g16Writes → s'.gpr r = s.gpr r) ∧ Frame [workR s] s.mem s'.mem := by
  obtain ⟨s', hs', hg, hm', hrd, hwr, hregs, hfr⟩ := g16_ok (room_ok_gCfg h) hm
  have hr9 : s'.gpr .r9 = s.gpr .r9 := hregs _ (by decide)
  refine ⟨s', hs', fun w hw => ?_, fun k hk hkt b hb => ?_, hm', room_congr h hr9 hwr, hrd, hwr,
    hregs, ?_⟩
  · rw [← wordQ_lv, ← wordQ_lv]; exact hg w hw
  · have hb' := arrays_bound k hk
    have hk69 : 69 ≤ k := by
      simp only [arrays, List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hkt | decide
    simp only [lv, laneA, hr9]
    refine hfr.readW (r := ⟨s.gpr .r9 + BitVec.ofNat 64 (8 * k + 4 * b), 4⟩)
      (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base (s.gpr .r9) (d := 8 * k + 4 * b) (n := 4) (k := 8 * 69)
      (by omega) (by omega)
  · refine hfr.sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨workR s, List.mem_singleton_self _, Region.sub_prefix (by simp [gCfg])⟩

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
      Frame [arraysR s] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r) := by
  obtain ⟨s', hs', hP, hv, rest⟩ := lanes_ok hsp hd (P := Room)
    (fun _ s s' hP hok => room_congr hP (hok.regs _ (by decide) (by decide)) hok.wr) hf h 16 (Nat.le_refl _)
  exact ⟨s', hs', hP, fun k hk b hb => by rw [hv k hk b hb, ite_eq_left hb], rest⟩

/-- The masks are outside the arrays. -/
theorem masks_of_arrays {s s' : State} (hm : MasksIn s) (hr9 : s'.gpr .r9 = s.gpr .r9)
    (hfr : Frame [arraysR s] s.mem s'.mem) : MasksIn s' := by
  intro kv hkv
  have hlt := maskSlots_lt kv hkv
  rw [← hm kv hkv]
  show s'.mem.readW (wordAddr (s'.gpr .r9) kv.1) 64 = s.mem.readW (wordAddr (s.gpr .r9) kv.1) 64
  rw [hr9]
  refine hfr.readW (r := ⟨wordAddr (s.gpr .r9) kv.1, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint _ (Or.inl (by omega)) (by omega) (by omega)

theorem scratch_of_arrays {s s' : State} (hfr : Frame [arraysR s] s.mem s'.mem) :
    Frame [workR s] s.mem s'.mem :=
  hfr.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨workR s, List.mem_singleton_self _, Offset.sub_base _ (by omega)⟩

theorem exec_add_imm (s : State) (d : Reg) (v : BitVec 32) :
    ∃ t, exec (.alu .add d (.imm v)) s = some t ∧ t.gpr d = s.gpr d + v.signExtend 64 ∧
      (∀ r, r ≠ d → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  ⟨_, rfl, by simp [gpr_setReg], fun r h => by simp [gpr_setReg, h, gpr_arithFlags], rfl, rfl, rfl⟩

theorem exec_sub_imm (s : State) (d : Reg) (v : BitVec 32) :
    ∃ t, exec (.alu .sub d (.imm v)) s = some t ∧ t.gpr d = s.gpr d - v.signExtend 64 ∧
      t.zf = some (s.gpr d - v.signExtend 64 == 0) ∧
      (∀ r, r ≠ d → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  ⟨_, rfl, by simp [gpr_setReg], rfl, fun r h => by simp [gpr_setReg, h, gpr_arithFlags], rfl, rfl, rfl⟩

theorem runBlock_trans {a b : List Instr} {s s' s'' : State} (h1 : runBlock isa a s = some s')
    (h2 : runBlock isa b s' = some s'') : runBlock isa (a ++ b) s = some s'' := by
  rw [runBlock_append, h1, Option.bind_some, h2]

theorem keepRegs : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .r8, .r9, .rsp],
    r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .r11 ∧ r ≠ .r12 := by decide

theorem notG16 : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .r8, .r9, .rsp], r ∉ g16Writes := by decide

theorem round_ok (d : Spec.Seed.Direction) {s : State} (h : Room s) (hm : MasksIn s)
    (hk0 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 4)
    (hk1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi + 4) 4) :
    ∃ s', runBlock isa (round d) s = some s' ∧
      (∀ b < 16, quad s' b =
        Spec.Seed.round (s.mem.readW (s.gpr .rdi) 32, s.mem.readW (s.gpr .rdi + 4) 32) (quad s b)) ∧
      MasksIn s' ∧ Room s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.gpr .rdi = s.gpr .rdi + (BitVec.ofInt 32 (keyStep d)).signExtend 64 ∧
      s'.gpr .r8 = s.gpr .r8 - (1 : BitVec 32).signExtend 64 ∧
      s'.zf = some (s.gpr .r8 - (1 : BitVec 32).signExtend 64 == 0) ∧
      s'.gpr .rsi = s.gpr .rsi ∧ s'.gpr .rdx = s.gpr .rdx ∧ s'.gpr .r9 = s.gpr .r9 ∧
      s'.gpr .rsp = s.gpr .rsp ∧ Frame [workR s] s.mem s'.mem := by
  let K0 := s.mem.readW (s.gpr .rdi) 32
  let K1 := s.mem.readW (s.gpr .rdi + 4) 32
  -- The round key.
  have ea0 : s.ea { base := .rdi, disp := 0 } = s.gpr .rdi := by simp [State.ea]
  have ea4 : (s.setReg32 .r11 K0).ea { base := .rdi, disp := 4 } = s.gpr .rdi + 4 := by
    simp [State.ea, State.setReg32, gpr_setReg]
  have e1 : exec (.mov32 .r11 (.mem { base := .rdi, disp := 0 })) s = some (s.setReg32 .r11 K0) := by
    rw [exec_mov32_mem (by rw [ea0]; exact hk0), ea0]
  have e2 : exec (.mov32 .r12 (.mem { base := .rdi, disp := 4 })) (s.setReg32 .r11 K0) =
      some ((s.setReg32 .r11 K0).setReg32 .r12 K1) := by
    rw [exec_mov32_mem (by rw [ea4]; exact hk1), ea4]; rfl
  let s2 := (s.setReg32 .r11 K0).setReg32 .r12 K1
  have hrun2 : runBlock isa [.mov32 .r11 (.mem { base := .rdi, disp := 0 }),
      .mov32 .r12 (.mem { base := .rdi, disp := 4 })] s = some s2 := by
    rw [runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_nil]
  have hkeys : KeysIn K0 K1 s2 := by
    refine ⟨room_congr h rfl rfl, ?_, ?_⟩ <;>
      simp [s2, State.setReg32, gpr_setReg]
  have lv2 : ∀ k b, lv s2 k b = lv s k b := fun k b => by
    simp only [s2, State.setReg32, lv_setReg _ _ (show ¬ Reg.r9 = .r12 by decide),
      lv_setReg _ _ (show ¬ Reg.r9 = .r11 by decide)]
  have g2 : ∀ r, r ≠ .r11 → r ≠ .r12 → s2.gpr r = s.gpr r := fun r h1 h2 => by
    simp [s2, State.setReg32, gpr_setReg, h1, h2]
  -- The steps.
  obtain ⟨s3, hs3, hP3, hv3, fr3, rd3, wr3, rg3⟩ := lanes_ok (dests1 K0 K1) (reads1 K0 K1)
    (P := KeysIn K0 K1)
    (fun _ s s' hP hok => ⟨room_congr hP.1 (hok.regs _ (by decide) (by decide)) hok.wr,
      by rw [hok.regs _ (by decide) (by decide)]; exact hP.2.1,
      by rw [hok.regs _ (by decide) (by decide)]; exact hP.2.2⟩)
    (fun b hb s hs => step1_ok K0 K1 hb s hs) hkeys 16 (Nat.le_refl _)
  have r93 : s3.gpr .r9 = s2.gpr .r9 := rg3 _ (by decide) (by decide)
  have hm3 : MasksIn s3 := masks_of_arrays (masks_of_arrays hm rfl (Frame.refl _ _)) r93 fr3
  obtain ⟨s4, hs4, hg4, hk4, hm4, h4, rd4, wr4, rg4, fr4⟩ := g16_lanes hP3.1 hm3
  obtain ⟨s5, hs5, h5, hv5, fr5, rd5, wr5, rg5⟩ := lanes16_room dests2 reads2 (fun b hb s hs => step2_ok hb s hs) h4
  have hm5 : MasksIn s5 := masks_of_arrays hm4 (rg5 _ (by decide) (by decide)) fr5
  obtain ⟨s6, hs6, hg6, hk6, hm6, h6, rd6, wr6, rg6, fr6⟩ := g16_lanes h5 hm5
  obtain ⟨s7, hs7, h7, hv7, fr7, rd7, wr7, rg7⟩ := lanes16_room dests3 reads3 (fun b hb s hs => step3_ok hb s hs) h6
  have hm7 : MasksIn s7 := masks_of_arrays hm6 (rg7 _ (by decide) (by decide)) fr7
  obtain ⟨s8, hs8, hg8, hk8, hm8, h8, rd8, wr8, rg8, fr8⟩ := g16_lanes h7 hm7
  obtain ⟨s9, hs9, h9, hv9, fr9, rd9, wr9, rg9⟩ := lanes16_room dests4 reads4 (fun b hb s hs => step4_ok hb s hs) h8
  have hm9 : MasksIn s9 := masks_of_arrays hm8 (rg9 _ (by decide) (by decide)) fr9
  obtain ⟨s10, hs10, hsw, hlow, rd10, wr10, rg10, fr10⟩ := swap_ok h9
  obtain ⟨s11, e11, rdi11, rg11, mem11, rd11, wr11⟩ :=
    exec_add_imm s10 .rdi (BitVec.ofInt 32 (keyStep d))
  obtain ⟨s12, e12, r812, zf12, rg12, mem12, rd12, wr12⟩ := exec_sub_imm s11 .r8 1
  have hrun : runBlock isa [.alu .add .rdi (.imm (BitVec.ofInt 32 (keyStep d))), .alu .sub .r8 (.imm 1)]
      s10 = some s12 := by
    rw [runBlock_cons, e11, runStep_some, runBlock_cons, e12, runStep_some, runBlock_nil]
  -- Registers through the steps.
  have keep : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .r8, .r9, .rsp], s10.gpr r = s.gpr r := by
    intro r hr
    have hg := notG16 r hr
    obtain ⟨h1, h2, h3, h4⟩ := keepRegs r hr
    rw [rg10 r h1 h2, rg9 r h1 h2, rg8 r hg, rg7 r h1 h2, rg6 r hg, rg5 r h1 h2, rg4 r hg,
      rg3 r h1 h2, g2 r h3 h4]
  have r9_10 : s10.gpr .r9 = s.gpr .r9 := keep _ (by decide)
  have r9_12 : s12.gpr .r9 = s.gpr .r9 := by
    rw [rg12 _ (by decide), rg11 _ (by decide), r9_10]
  have lv12 : ∀ k b, lv s12 k b = lv s10 k b := fun k b => by
    simp only [lv, laneA, mem12, mem11, r9_12, r9_10]
  refine ⟨s12, ?_, fun b hb => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact runBlock_trans (runBlock_trans (runBlock_trans (runBlock_trans (runBlock_trans
      (runBlock_trans (runBlock_trans (runBlock_trans (runBlock_trans hrun2 hs3) hs4) hs5) hs6)
      hs7) hs8) hs9) hs10) hrun
  · -- The values, stage by stage.
    have ar : ∀ k ∈ arrays, k ∈ arrays := fun _ h => h
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
  · intro kv hkv
    have hlt := maskSlots_lt kv hkv
    rw [← hm9 kv hkv]
    show s12.mem.readW (wordAddr (s12.gpr .r9) kv.1) 64 = s9.mem.readW (wordAddr (s9.gpr .r9) kv.1) 64
    rw [mem12, mem11, r9_12, ← r9_10]
    exact hlow kv.1 (by omega)
  · exact room_congr h r9_12 (by rw [wr12, wr11, wr10, wr9, wr8, wr7, wr6, wr5, wr4, wr3]; rfl)
  · rw [rd12, rd11, rd10, rd9, rd8, rd7, rd6, rd5, rd4, rd3]; rfl
  · rw [wr12, wr11, wr10, wr9, wr8, wr7, wr6, wr5, wr4, wr3]; rfl
  · rw [rg12 _ (by decide), rdi11, keep _ (by decide)]
  · rw [r812, rg11 _ (by decide), keep _ (by decide)]
  · rw [zf12, rg11 _ (by decide), keep _ (by decide)]
  · rw [rg12 _ (by decide), rg11 _ (by decide), keep _ (by decide)]
  · rw [rg12 _ (by decide), rg11 _ (by decide), keep _ (by decide)]
  · exact r9_12
  · rw [rg12 _ (by decide), rg11 _ (by decide), keep _ (by decide)]
  · -- The frames, all in the scratch buffer.
    have fc : ∀ {t : State} {m m' : Mem}, t.gpr .r9 = s.gpr .r9 → Frame [workR t] m m' →
        Frame [workR s] m m' := fun ht hf => by simpa [workR, ht] using hf
    rw [mem12, mem11]
    refine (fc rfl (scratch_of_arrays fr3)).trans ?_
    refine (fc (rg3 _ (by decide) (by decide)) fr4).trans ?_
    refine (fc ?_ (scratch_of_arrays fr5)).trans ?_
    · rw [rg4 _ (by decide), rg3 _ (by decide) (by decide)]; rfl
    refine (fc ?_ fr6).trans ?_
    · rw [rg5 _ (by decide) (by decide), rg4 _ (by decide), rg3 _ (by decide) (by decide)]; rfl
    refine (fc ?_ (scratch_of_arrays fr7)).trans ?_
    · rw [rg6 _ (by decide), rg5 _ (by decide) (by decide), rg4 _ (by decide),
        rg3 _ (by decide) (by decide)]; rfl
    refine (fc ?_ fr8).trans ?_
    · rw [rg7 _ (by decide) (by decide), rg6 _ (by decide), rg5 _ (by decide) (by decide),
        rg4 _ (by decide), rg3 _ (by decide) (by decide)]; rfl
    refine (fc ?_ (scratch_of_arrays fr9)).trans ?_
    · rw [rg8 _ (by decide), rg7 _ (by decide) (by decide), rg6 _ (by decide),
        rg5 _ (by decide) (by decide), rg4 _ (by decide), rg3 _ (by decide) (by decide)]; rfl
    refine fc ?_ fr10
    rw [rg9 _ (by decide) (by decide), rg8 _ (by decide), rg7 _ (by decide) (by decide),
      rg6 _ (by decide), rg5 _ (by decide) (by decide), rg4 _ (by decide),
      rg3 _ (by decide) (by decide)]; rfl

end VG.Proof.Seed.X86_64
