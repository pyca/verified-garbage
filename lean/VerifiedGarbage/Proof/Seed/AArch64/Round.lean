import VerifiedGarbage.Proof.Seed.AArch64.Swap

/-!
# A round on AArch64

`g16_lanes` restates `g16_ok` on the lanes of the arrays, and `round_ok`
puts the steps of a round together: on every lane, the round's code does
RFC 4269 §2's round (`Spec.Seed.round`) to the arrays of `L0`, `L1`, `R0`,
`R1`, with the round key at `x0`.
-/

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.Seed.AArch64
open VG.Proof.Aes.AArch64 (layerWrites)

theorem room_ok_gCfg {s : State} (h : Room s) : Ok gCfg s := ok_of_room h rfl (by decide) rfl

/-- `g16` on the lanes: `G` of `G`'s words, the other arrays kept. -/
theorem g16_lanes {s : State} (h : Room s) :
    ∃ s', runBlock isa g16 s = some s' ∧
      (∀ w < 16, lv s' (tSlot 0) w = Spec.Seed.g (lv s (tSlot 0) w)) ∧
      (∀ k ∈ arrays, k ≠ tSlot 0 → ∀ b < 16, lv s' k b = lv s k b) ∧
      Room s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r) ∧ Frame [workR s] s.mem s'.mem := by
  obtain ⟨s', hs', hg, hrd, hwr, hsp, hregs, hfr⟩ := g16_ok (room_ok_gCfg h)
  have hr9 : s'.gpr .x5 = s.gpr .x5 := hregs _ (by decide)
  refine ⟨s', hs', fun w hw => ?_, fun k hk hkt b hb => ?_, room_congr h hr9 hwr, hrd, hwr, hsp,
    hregs, ?_⟩
  · rw [← wordQ_lv, ← wordQ_lv]; exact hg w hw
  · have hb' := arrays_bound k hk
    have hk56 : 56 ≤ k := by
      simp only [arrays, List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hkt | decide
    simp only [lv, laneA, hr9]
    refine hfr.readW (r := ⟨s.gpr .x5 + BitVec.ofNat 64 (8 * k + 4 * b), 4⟩)
      (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base (s.gpr .x5) (d := 8 * k + 4 * b) (n := 4) (k := 8 * 56)
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
      (∀ r, r ≠ .x14 → r ≠ .x15 → s'.gpr r = s.gpr r) := by
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
    exec (keyNext d) s = some (s.write .x .x0 (s.gpr .x0 + stepW d)) := by
  cases d
  · rw [keyNext, exec_addImm_x (by decide), read_x]; rfl
  · rw [keyNext, exec_subImm_x (by decide), read_x, BitVec.sub_eq_add_neg]; rfl

theorem exec_dec (s : State) (r : Reg) :
    exec (.subImm .x r r 1) s = some (s.write .x r (s.gpr r - 1)) := by
  rw [exec_subImm_x (by decide), read_x]; rfl

theorem runBlock_sp {is : List Instr} {s s' : State} (h : runBlock isa is s = some s') :
    s'.sp = s.sp := by
  induction is generalizing s with
  | nil => cases h; rfl
  | cons i is ih =>
    rw [runBlock_cons] at h
    cases h₁ : exec i s with
    | none => rw [h₁] at h; cases h
    | some s₁ =>
      rw [h₁, runStep_some] at h
      rw [ih h]; exact exec_sp h₁

theorem runBlock_trans {a b : List Instr} {s s' s'' : State} (h1 : runBlock isa a s = some s')
    (h2 : runBlock isa b s' = some s'') : runBlock isa (a ++ b) s = some s'' := by
  rw [runBlock_append, h1, Option.bind_some, h2]

theorem keepRegs : ∀ r ∈ [Reg.x0, .x1, .x2, .x4, .x5],
    r ≠ .x14 ∧ r ≠ .x15 ∧ r ≠ .x16 ∧ r ≠ .x17 := by decide

theorem notG16 : ∀ r ∈ [Reg.x0, .x1, .x2, .x4, .x5], r ∉ layerWrites := by decide

theorem round_ok (d : Spec.Seed.Direction) {s : State} (h : Room s)
    (hk0 : InRegions (s.rd ++ s.wr) (s.gpr .x0) 4)
    (hk1 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + 4) 4) :
    ∃ s', runBlock isa (round d) s = some s' ∧
      (∀ b < 16, quad s' b =
        Spec.Seed.round (s.mem.readW (s.gpr .x0) 32, s.mem.readW (s.gpr .x0 + 4) 32) (quad s b)) ∧
      Room s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.gpr .x0 = s.gpr .x0 + stepW d ∧ s'.gpr .x4 = s.gpr .x4 - 1 ∧
      s'.gpr .x1 = s.gpr .x1 ∧ s'.gpr .x2 = s.gpr .x2 ∧ s'.gpr .x5 = s.gpr .x5 ∧
      Frame [workR s] s.mem s'.mem := by
  let K0 := s.mem.readW (s.gpr .x0) 32
  let K1 := s.mem.readW (s.gpr .x0 + 4) 32
  -- The round key.
  have e1 : exec (.ldr .w .x16 .x0 0) s = some (s.write .w .x16 K0) := by
    rw [exec_ldr_w (by decide) (by simpa using hk0)]; simp [K0]
  have e2 : exec (.ldr .w .x17 .x0 4) (s.write .w .x16 K0) =
      some ((s.write .w .x16 K0).write .w .x17 K1) := by
    rw [exec_ldr_w (by decide) (by rw [rd_write, wr_write, gpr_write_of_ne _ _ _ (by decide)]; exact hk1)]
    rw [gpr_write_of_ne _ _ _ (by decide), mem_write]; rfl
  let s2 := (s.write .w .x16 K0).write .w .x17 K1
  have hrun2 : runBlock isa [.ldr .w .x16 .x0 0, .ldr .w .x17 .x0 4] s = some s2 := by
    rw [runBlock_cons, e1, runStep_some, runBlock_cons, e2, runStep_some, runBlock_nil]
  have hkeys : KeysIn K0 K1 s2 := by
    refine ⟨room_congr h rfl rfl, ?_, ?_⟩ <;>
      simp [s2, gpr_write]
  have lv2 : ∀ k b, lv s2 k b = lv s k b := fun k b => by
    simp only [s2, lv_write _ _ _ (show ¬ Reg.x5 = .x17 by decide),
      lv_write _ _ _ (show ¬ Reg.x5 = .x16 by decide)]
  have g2 : ∀ r, r ≠ .x16 → r ≠ .x17 → s2.gpr r = s.gpr r := fun r h1 h2 => by
    simp [s2, gpr_write, h1, h2]
  -- The steps.
  obtain ⟨s3, hs3, hP3, hv3, fr3, rd3, wr3, rg3⟩ := lanes_ok (dests1 K0 K1) (reads1 K0 K1)
    (P := KeysIn K0 K1)
    (fun _ s s' hP hok => ⟨room_congr hP.1 (hok.regs _ (by decide) (by decide)) hok.wr,
      by rw [hok.regs _ (by decide) (by decide)]; exact hP.2.1,
      by rw [hok.regs _ (by decide) (by decide)]; exact hP.2.2⟩)
    (fun b hb s hs => step1_ok K0 K1 hb s hs) hkeys 16 (Nat.le_refl _)
  obtain ⟨s4, hs4, hg4, hk4, h4, rd4, wr4, spp4, rg4, fr4⟩ := g16_lanes hP3.1
  obtain ⟨s5, hs5, h5, hv5, fr5, rd5, wr5, rg5⟩ := lanes16_room dests2 reads2 (fun b hb s hs => step2_ok hb s hs) h4
  obtain ⟨s6, hs6, hg6, hk6, h6, rd6, wr6, spp6, rg6, fr6⟩ := g16_lanes h5
  obtain ⟨s7, hs7, h7, hv7, fr7, rd7, wr7, rg7⟩ := lanes16_room dests3 reads3 (fun b hb s hs => step3_ok hb s hs) h6
  obtain ⟨s8, hs8, hg8, hk8, h8, rd8, wr8, spp8, rg8, fr8⟩ := g16_lanes h7
  obtain ⟨s9, hs9, h9, hv9, fr9, rd9, wr9, rg9⟩ := lanes16_room dests4 reads4 (fun b hb s hs => step4_ok hb s hs) h8
  obtain ⟨s10, hs10, hsw, hlow, rd10, wr10, spp10, rg10, fr10⟩ := swap_ok h9
  let s11 := s10.write .x .x0 (s10.gpr .x0 + stepW d)
  let s12 := s11.write .x .x4 (s11.gpr .x4 - 1)
  have hrun : runBlock isa [keyNext d, .subImm .x .x4 .x4 1] s10 = some s12 := by
    rw [runBlock_cons, exec_keyNext, runStep_some, runBlock_cons, exec_dec, runStep_some, runBlock_nil]
  -- Registers through the steps.
  have keep : ∀ r ∈ [Reg.x0, .x1, .x2, .x4, .x5], s10.gpr r = s.gpr r := by
    intro r hr
    have hg := notG16 r hr
    obtain ⟨h1, h2, h3, h4⟩ := keepRegs r hr
    rw [rg10 r h1 h2, rg9 r h1 h2, rg8 r hg, rg7 r h1 h2, rg6 r hg, rg5 r h1 h2, rg4 r hg,
      rg3 r h1 h2, g2 r h3 h4]
  have r9_10 : s10.gpr .x5 = s.gpr .x5 := keep _ (by decide)
  have g12 : ∀ r, r ≠ .x0 → r ≠ .x4 → s12.gpr r = s10.gpr r := fun r a b => by
    simp [s12, s11, gpr_write, a, b]
  have r9_12 : s12.gpr .x5 = s.gpr .x5 := by rw [g12 _ (by decide) (by decide), r9_10]
  have lv12 : ∀ k b, lv s12 k b = lv s10 k b := fun k b => by
    simp only [lv, laneA, s12, s11, mem_write, r9_12, r9_10]
  refine ⟨s12, ?_, fun b hb => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · exact room_congr h r9_12 (by simp only [s12, s11, wr_write, wr10, wr9, wr8, wr7, wr6, wr5, wr4, wr3]; rfl)
  · simp only [s12, s11, rd_write, rd10, rd9, rd8, rd7, rd6, rd5, rd4, rd3]; rfl
  · simp only [s12, s11, wr_write, wr10, wr9, wr8, wr7, wr6, wr5, wr4, wr3]; rfl
  · simp only [s12, s11, sp_write, spp10]
    rw [runBlock_sp hs9, spp8, runBlock_sp hs7, spp6, runBlock_sp hs5, spp4, runBlock_sp hs3,
      runBlock_sp hrun2]
  · simp [s12, s11, gpr_write, keep _ (show Reg.x0 ∈ [Reg.x0, .x1, .x2, .x4, .x5] by decide)]
  · simp [s12, s11, gpr_write, keep _ (show Reg.x4 ∈ [Reg.x0, .x1, .x2, .x4, .x5] by decide)]
  · rw [g12 _ (by decide) (by decide), keep _ (by decide)]
  · rw [g12 _ (by decide) (by decide), keep _ (by decide)]
  · exact r9_12
  · -- The frames, all in the scratch buffer.
    have fc : ∀ {t : State} {m m' : Mem}, t.gpr .x5 = s.gpr .x5 → Frame [workR t] m m' →
        Frame [workR s] m m' := fun ht hf => by simpa [workR, ht] using hf
    simp only [s12, s11, mem_write]
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

end VG.Proof.Seed.AArch64
