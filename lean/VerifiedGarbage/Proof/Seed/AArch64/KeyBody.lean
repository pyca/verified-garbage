import VerifiedGarbage.Proof.Seed.AArch64.KeyStore
import VerifiedGarbage.Proof.Seed.AArch64.Batch

/-!
# The key schedule's computation on AArch64

`keyBody_ok`: from `x3 = Key0 || Key1` and `x4 = Key2 || Key3`, the rounds,
the two `g16`s and the copies write `G` of the 32 inputs (`gInput`) to the
schedule.
-/

namespace VG.Proof.Seed.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.Seed.AArch64 VG.Proof.Seed
open VG.Proof.Aes.AArch64 (layerWrites)

/-- The key schedule's computation, between loading the key and restoring the registers. -/
def keyBody : List Instr :=
  (List.range 16).flatMap keyRound ++ g16 ++ keyStore 0 ++ keyMove ++ g16 ++ keyStore 16

theorem gSlot_lo {i : Nat} (hi : i < 16) : gSlot i = tSlot 0 := by simp [gSlot, hi]
theorem gSlot_hi {w : Nat} (hw : w < 16) : gSlot (16 + w) = uSlot := by
  simp [gSlot, show ¬ 16 + w < 16 by omega]

theorem schedR_sep {s : State} {k : Nat} (hk : k + 64 ≤ 128)
    (h : (⟨s.gpr .x1, 128⟩ : Region).Disjoint (scratchR s)) : (outR s (k / 4)).Disjoint (scratchR s) := by
  refine h.sub_left ?_
  exact Offset.sub_base _ (by omega)

theorem lane_sub_work {s : State} {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) :
    Region.Sub ⟨laneA s k b, 4⟩ (workR s) := by
  have := arrays_bound k hk
  exact Offset.sub_base _ (by omega)

/-- A lane after a frame over regions apart from the scratch buffer. -/
theorem lv_frame {s s' : State} {R : Region} (hx5 : s'.gpr .x5 = s.gpr .x5) (hf : Frame [R] s.mem s'.mem)
    (hd : R.Disjoint (scratchR s)) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) : lv s' k b = lv s k b := by
  simp only [lv, laneA, hx5]
  refine hf.readW (r := ⟨s.gpr .x5 + BitVec.ofNat 64 (8 * k + 4 * b), 4⟩) (Region.contains_self _ _) ?_
    (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact (hd.sub_right (lane_in hk hb s |> fun _ => by
    have := arrays_bound k hk
    exact Offset.sub_base _ (by unfold scratchSlots; omega))).symm

theorem keyBody_ok (key : Spec.Seed.Block) {s : State} (h : Room s)
    (h3 : s.gpr .x3 = kx (keyWords key 0)) (h4 : s.gpr .x4 = ky (keyWords key 0))
    (hin : (⟨s.gpr .x1, 128⟩ : Region) ∈ s.wr)
    (hsep : (⟨s.gpr .x1, 128⟩ : Region).Disjoint (scratchR s)) :
    ∃ s', runBlock isa keyBody s = some s' ∧
      (∀ i < 32, s'.mem.readW (s.gpr .x1 + BitVec.ofNat 64 (4 * i)) 32 = Spec.Seed.g (gInput key i)) ∧
      (∀ r ∈ [Reg.x5, .x1], s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [workR s, ⟨s.gpr .x1, 128⟩] s.mem s'.mem := by
  have hw : ∀ k, k ≤ 16 → ∀ w < 16, InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (4 * (k + w))) 4 :=
    fun k hk w hw => ⟨_, hin, Offset.contains_base _ (by omega) (by omega)⟩
  -- the rounds
  obtain ⟨s1, e1, inv⟩ := keyRounds_ok key h h3 h4 16 (Nat.le_refl _)
  have x5_1 : s1.gpr .x5 = s.gpr .x5 := inv.regs _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have room1 : Room s1 := room_congr h x5_1 inv.wr
  -- `G` of the first sixteen
  obtain ⟨s2, e2, g2, keep2, room2, rd2, wr2, -, regs2, f2⟩ := g16_lanes room1
  have x5_2 : s2.gpr .x5 = s.gpr .x5 := (regs2 _ (by decide)).trans x5_1
  have x1_2 : s2.gpr .x1 = s.gpr .x1 :=
    (regs2 _ (by decide)).trans (inv.regs _ (by decide) (by decide) (by decide) (by decide) (by decide))
  have scr2 : scratchR s2 = scratchR s := by simp only [scratchR, x5_2]
  have lo2 : ∀ w < 16, lv s2 (tSlot 0) w = Spec.Seed.g (gInput key w) := fun w hw => by
    rw [g2 w hw, ← inv.lanes w (by omega), gSlot_lo hw, Nat.mod_eq_of_lt hw]
  have hi2 : ∀ w < 16, lv s2 uSlot w = gInput key (16 + w) := fun w hw => by
    rw [keep2 uSlot (by decide) (by decide) w hw, ← inv.lanes (16 + w) (by omega), gSlot_hi hw,
      show (16 + w) % 16 = w by omega]
  -- the first copy
  obtain ⟨s3, e3, v3, g3, rd3, wr3, f3⟩ := keyStore_ok 0 (by decide) room2 (by rw [x1_2, wr2, inv.wr]; exact hw 0 (by decide))
    (by rw [scr2]; simp only [outR, x1_2, Nat.mul_zero]; rw [BitVec.add_zero]
        exact hsep.sub_left (Region.sub_prefix (by decide))) 16 (Nat.le_refl _)
  have x5_3 : s3.gpr .x5 = s.gpr .x5 := (g3 _ (by decide)).trans x5_2
  have x1_3 : s3.gpr .x1 = s.gpr .x1 := (g3 _ (by decide)).trans x1_2
  have out0 : (outR s2 0).Disjoint (scratchR s2) := by
    rw [scr2]; simp only [outR, x1_2, Nat.mul_zero]; rw [BitVec.add_zero]
    exact hsep.sub_left (Region.sub_prefix (by decide))
  have room3 : Room s3 := room_congr h x5_3 (by rw [wr3, wr2, inv.wr])
  -- the second sixteen inputs
  obtain ⟨s4, e4, room4, v4, f4, rd4, wr4, g4⟩ := keyMove_ok room3
  have x5_4 : s4.gpr .x5 = s.gpr .x5 := (g4 _ (by decide) (by decide)).trans x5_3
  have lo4 : ∀ w < 16, lv s4 (tSlot 0) w = gInput key (16 + w) := fun w hw => by
    rw [v4 _ (by decide) w hw, show newVal spMove (tSlot 0) (fun k' => lv s3 k' w) = lv s3 uSlot w from rfl,
      lv_frame (g3 _ (by decide)) f3 out0 (by decide) hw, hi2 w hw]
  obtain ⟨s5, e5, g5, -, room5, rd5, wr5, -, regs5, f5⟩ := g16_lanes room4
  have x5_5 : s5.gpr .x5 = s.gpr .x5 := (regs5 _ (by decide)).trans x5_4
  have x1_5 : s5.gpr .x1 = s.gpr .x1 :=
    (regs5 _ (by decide)).trans ((g4 _ (by decide) (by decide)).trans x1_3)
  have scr5 : scratchR s5 = scratchR s := by simp only [scratchR, x5_5]
  -- the second copy
  obtain ⟨s6, e6, v6, g6, rd6, wr6, f6⟩ := keyStore_ok 16 (by decide) room5
    (by rw [x1_5, wr5, wr4, wr3, wr2, inv.wr]; exact hw 16 (by decide))
    (by rw [scr5]; simp only [outR, x1_5]; exact hsep.sub_left (Offset.sub_base _ (by decide)))
    16 (Nat.le_refl _)
  have workS : ∀ t : State, t.gpr .x5 = s.gpr .x5 → workR t = workR s := fun t ht => by simp only [workR, ht]
  have schedWork : (⟨s.gpr .x1, 128⟩ : Region).Disjoint (workR s) :=
    hsep.sub_right (Region.sub_prefix (by unfold scratchSlots; omega))
  refine ⟨s6, ?_, fun i hi => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · show runBlock isa ((List.range 16).flatMap keyRound ++ g16 ++ keyStore 0 ++ keyMove ++ g16 ++ keyStore 16) s =
      some s6
    exact runBlock_trans (runBlock_trans (runBlock_trans (runBlock_trans (runBlock_trans e1 e2) e3) e4) e5) e6
  · by_cases hi16 : i < 16
    · have hd : ∀ (t t' : State) (rs : List Region), Frame rs t.mem t'.mem →
          (∀ r ∈ rs, (⟨s.gpr .x1 + BitVec.ofNat 64 (4 * i), 4⟩ : Region).Disjoint r) →
          t'.mem.readW (s.gpr .x1 + BitVec.ofNat 64 (4 * i)) 32 =
            t.mem.readW (s.gpr .x1 + BitVec.ofNat 64 (4 * i)) 32 :=
        fun t t' rs hf hd => hf.readW (Region.contains_self _ _) hd (by decide)
      have hsw : (⟨s.gpr .x1 + BitVec.ofNat 64 (4 * i), 4⟩ : Region).Disjoint (workR s) :=
        schedWork.sub_left (Offset.sub_base _ (by omega))
      rw [hd s5 s6 _ f6 (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; simp only [outR, x1_5]
          exact Offset.disjoint _ (Or.inl (by omega)) (by omega) (by omega)),
        hd s4 s5 _ f5 (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [workS s4 x5_4]; exact hsw),
        hd s3 s4 _ f4 (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hsw.sub_right (by simp only [arraysR, workR, x5_3]; exact arraysR_sub_work s)),
        show 4 * i = 4 * (0 + i) by omega, ← x1_2, v3 i hi16, lo2 i hi16]
    · obtain ⟨w, rfl⟩ : ∃ w, i = 16 + w := ⟨i - 16, by omega⟩
      rw [← x1_5, show 4 * (16 + w) = 4 * (16 + w) from rfl, v6 w (by omega), g5 w (by omega),
        lo4 w (by omega)]
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    · rw [g6 _ (by decide), x5_5]
    · rw [g6 _ (by decide), x1_5]
  · rw [rd6, rd5, rd4, rd3, rd2, inv.rd]
  · rw [wr6, wr5, wr4, wr3, wr2, inv.wr]
  · have sw : ∀ r ∈ [workR s], ∃ r' ∈ [workR s, (⟨s.gpr .x1, 128⟩ : Region)], Region.Sub r r' :=
      fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self, fun _ h => h⟩
    have ss : ∀ t : State, t.gpr .x1 = s.gpr .x1 → ∀ k, k + 64 ≤ 128 →
        ∀ r ∈ [outR t (k / 4)], ∃ r' ∈ [workR s, (⟨s.gpr .x1, 128⟩ : Region)], Region.Sub r r' :=
      fun t ht k hk r hr => ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; simp only [outR, ht]
        exact Offset.sub_base _ (by omega)⟩
    refine (((((inv.frame.sub ?_).trans (f2.sub ?_)).trans (f3.sub (ss s2 x1_2 0 (by decide)))).trans
      (f4.sub ?_)).trans (f5.sub ?_)).trans (f6.sub (ss s5 x1_5 64 (by decide)))
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s, List.mem_cons_self, arraysR_sub_work s⟩
    · rw [workS s1 x5_1]; exact sw
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      refine ⟨workR s, List.mem_cons_self, ?_⟩
      rw [← workS s3 x5_3]; exact arraysR_sub_work s3
    · rw [workS s4 x5_4]; exact sw

end VG.Proof.Seed.AArch64
