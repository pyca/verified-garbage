module

public import VerifiedGarbage.Proof.Seed.RISCV64.KeyStore
public import VerifiedGarbage.Proof.Seed.RISCV64.KeyRounds
import VerifiedGarbage.Proof.Seed.RISCV64.Batch
public import VerifiedGarbage.Proof.Seed.RISCV64.Round
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The key schedule's computation on RISC-V

As on PPC64LE (`Proof/Seed/PPC64LE/KeyBody.lean`): from `t5 = Key0 || Key1`
and `t6 = Key2 || Key3`, the rounds (`keyPre_ok`), the two `g16`s and the
copies (`keyHalves_wp`) write `G` of the 32 inputs (`gInput`) to the
schedule.
-/

@[expose] public section

namespace VG.Proof.Seed.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Seed.RISCV64 VG.Proof.Seed
open VG.Impl.Aes.RISCV64 (sb)

/-- The rounds and the count of halves, between loading the key and the loop. -/
def keyPre : List Instr := (List.range 16).flatMap keyRound ++ [.li .a4 2]

theorem gSlot_lo {i : Nat} (hi : i < 16) : gSlot i = tSlot 0 := by simp [gSlot, hi]
theorem gSlot_hi {w : Nat} (hw : w < 16) : gSlot (16 + w) = uSlot := by
  simp [gSlot, show ¬ 16 + w < 16 by omega]

theorem schedR_sep {s : State} {k : Nat} (hk : k + 64 ≤ 128)
    (h : (⟨s.gpr .a1, 128⟩ : Region).Disjoint (scratchR s)) : (outR s (k / 4)).Disjoint (scratchR s) := by
  refine h.sub_left ?_
  exact Offset.sub_base _ (by omega)

theorem lane_sub_work {s : State} {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) :
    Region.Sub ⟨laneA s k b, 4⟩ (workR s) := by
  have := arrays_bound k hk
  exact Offset.sub_base _ (by omega)

/-- A lane after a frame over regions apart from the scratch buffer. -/
theorem lv_frame {s s' : State} {R : Region} (hx5 : s'.gpr sb = s.gpr sb) (hf : Frame [R] s.mem s'.mem)
    (hd : R.Disjoint (scratchR s)) {k b : Nat} (hk : k ∈ arrays) (hb : b < 16) : lv s' k b = lv s k b := by
  simp only [lv, laneA, hx5]
  refine hf.readW (r := ⟨s.gpr sb + BitVec.ofNat 64 (8 * k + 4 * b), 4⟩) (Region.contains_self _ _) ?_
    (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact (hd.sub_right (lane_in hk hb s |> fun _ => by
    have := arrays_bound k hk
    exact Offset.sub_base _ (by unfold scratchSlots; omega))).symm

theorem keyPre_ok (key : Spec.Seed.Block) {s : State} (h : Room s)
    (h3 : s.gpr .t5 = kx (keyWords key 0)) (h4 : s.gpr .t6 = ky (keyWords key 0)) :
    ∃ s', runBlock isa keyPre s = some s' ∧ Room s' ∧
      (∀ w < 16, lv s' (tSlot 0) w = gInput key w) ∧ (∀ w < 16, lv s' uSlot w = gInput key (16 + w)) ∧
      s'.gpr .a4 = BitVec.ofNat 64 2 ∧
      (∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → r ≠ .t5 → r ≠ .t6 → r ≠ .a4 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [arraysR s] s.mem s'.mem := by
  obtain ⟨s1, e1, inv⟩ := keyRounds_ok key h h3 h4 16 (Nat.le_refl _)
  let s2 := s1.write .a4 (BitVec.ofNat 64 2)
  have e2 : runBlock isa [.li .a4 2] s1 = some s2 := by
    rw [runBlock_cons, exec_li (by decide), runStep_some, runBlock_nil]; rfl
  have g2 : ∀ r, r ≠ .a4 → s2.gpr r = s1.gpr r := fun r hr => gpr_write_of_ne _ _ hr
  have sb_1 : s1.gpr sb = s.gpr sb := inv.regs _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have sb_2 : s2.gpr sb = s.gpr sb := (g2 _ (by decide)).trans sb_1
  have lv2 : ∀ k b, lv s2 k b = lv s1 k b := fun k b => by
    simp only [lv, laneA, g2 _ (show sb ≠ .a4 by decide)]; rfl
  refine ⟨s2, runBlock_trans e1 e2, room_congr h sb_2 inv.wr, fun w hw => ?_, fun w hw => ?_,
    by simp [s2, gpr_write], fun r a b c d e f => ?_, inv.rd, inv.wr, inv.sp, inv.frame⟩
  · rw [lv2, ← inv.lanes w (by omega), gSlot_lo hw, Nat.mod_eq_of_lt hw]
  · rw [lv2, ← inv.lanes (16 + w) (by omega), gSlot_hi hw, show (16 + w) % 16 = w by omega]
  · rw [g2 _ f, inv.regs _ a b c d e]

/-- `addi a1, a1, 64; addi a4, a4, -1`. -/
theorem halfTail_ok (t : State) :
    ∃ t', runBlock isa [.addi .a1 .a1 64, .addi .a4 .a4 (-1)] t = some t' ∧
      t'.gpr .a1 = t.gpr .a1 + BitVec.ofNat 64 64 ∧ t'.gpr .a4 = t.gpr .a4 - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .a1 → r ≠ .a4 → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      t'.sp = t.sp := by
  refine ⟨_, by
    rw [runBlock_cons, exec_addi (by decide), runStep_some, runBlock_cons, exec_dec _ .a4,
      runStep_some, runBlock_nil], ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  simp [gpr_write, h1, h2]

/-- After `c` of the two halves: `a1` at the schedule's word `16 c`, `a4` the
halves left, `G`'s words holding the next sixteen inputs, the schedule's
words before `16 c` done. -/
structure HalfInv (key : Spec.Seed.Block) (s : State) (S : Addr) (c : Nat) (t : State) : Prop where
  room : Room t
  masks : Masks t
  sb : t.gpr sb = s.gpr sb
  a1 : t.gpr .a1 = S + BitVec.ofNat 64 (64 * c)
  a4 : t.gpr .a4 = BitVec.ofNat 64 (2 - c)
  regs : ∀ r ∈ [Reg.ra, .a0, .a2, .a3, .a5], t.gpr r = s.gpr r
  cur : ∀ w < 16, lv t (tSlot 0) w = gInput key (16 * c + w)
  next : c = 0 → ∀ w < 16, lv t uSlot w = gInput key (16 + w)
  done : ∀ i < 16 * c, t.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = Spec.Seed.g (gInput key i)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [workR s, ⟨S, 128⟩] s.mem t.mem

theorem keyHalves_wp (key : Spec.Seed.Block) {s : State} {S : Addr} (hin : (⟨S, 128⟩ : Region) ∈ s.wr)
    (hsep : (⟨S, 128⟩ : Region).Disjoint (scratchR s)) (h0 : HalfInv key s S 0 s) {Q : State → Prop}
    (hQ : ∀ t, (∀ i < 32, t.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = Spec.Seed.g (gInput key i)) →
      (∀ r ∈ [Reg.ra, .a0, .a2, .a3, .a5], t.gpr r = s.gpr r) → t.rd = s.rd → t.wr = s.wr →
      t.sp = s.sp → Frame [workR s, ⟨S, 128⟩] s.mem t.mem → Q t) :
    WP isa (.loop keyHalf (.nonzero .a4)) s Q := by
  refine WP.loop (M := isa) (fun n t => ∃ c, c < 2 ∧ n = 2 - c ∧ HalfInv key s S c t) (fun n t ht => ?_) 2 s
    ⟨0, by decide, rfl, h0⟩
  obtain ⟨c, hc, rfl, hi⟩ := ht
  have scrS : ∀ t : State, t.gpr sb = s.gpr sb → scratchR t = scratchR s := fun t h => by simp only [scratchR, h]
  have workS : ∀ t : State, t.gpr sb = s.gpr sb → workR t = workR s := fun t h => by simp only [workR, h]
  have schedWork : (⟨S, 128⟩ : Region).Disjoint (workR s) :=
    hsep.sub_right (Region.sub_prefix (by unfold scratchSlots; omega))
  -- `G` of the sixteen
  obtain ⟨t2, e2, g2, keep2, room2, masks2, rd2, wr2, sp2, regs2, f2⟩ := g16_lanes hi.room hi.masks
  have sb_2 : t2.gpr sb = s.gpr sb := (regs2 _ (by decide)).trans hi.sb
  have a1_2 : t2.gpr .a1 = S + BitVec.ofNat 64 (64 * c) := (regs2 _ (by decide)).trans hi.a1
  have out2 : (outR t2 0).Disjoint (scratchR t2) := by
    rw [scrS t2 sb_2]; simp only [outR, a1_2, Nat.mul_zero]; rw [BitVec.add_zero]
    exact hsep.sub_left (Offset.sub_base _ (by omega))
  -- the copy
  obtain ⟨t3, e3, v3, g3, rd3, wr3, sp3, f3⟩ := keyStore_ok 0 (by decide) room2
    (fun w hw => by
      rw [a1_2, wr2, hi.wr, Offset.add_add]
      exact ⟨_, hin, Offset.contains_base _ (by omega) (by omega)⟩) out2 16 (Nat.le_refl _)
  obtain ⟨t4, e4, a1_4', a4_4', g4, m4, rd4, wr4, sp4⟩ := halfTail_ok t3
  have G4 : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .a1 → r ≠ .a4 → t4.gpr r = t2.gpr r := fun r a b c' d =>
    by rw [g4 r c' d, g3 r a b]
  have sb_4 : t4.gpr sb = s.gpr sb := by rw [G4 _ (by decide) (by decide) (by decide) (by decide), sb_2]
  have a4_4 : t4.gpr .a4 = BitVec.ofNat 64 (2 - (c + 1)) := by
    rw [a4_4', g3 _ (by decide) (by decide), regs2 _ (by decide), hi.a4, Offset.ofNat_sub_ofNat (by omega)]
    congr 1
  have a1_4 : t4.gpr .a1 = S + BitVec.ofNat 64 (64 * (c + 1)) := by
    rw [a1_4', g3 _ (by decide) (by decide), a1_2, Offset.add_add, show 64 * c + 64 = 64 * (c + 1) by omega]
  have ev4 : isa.eval (.nonzero .a4) t4 = some (decide (c = 0)) := by
    rw [RISCV64.Steps.eval_nonzero, a4_4]
    congr 1
    rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> decide
  -- the schedule's words so far
  have lvS : ∀ (t t' : State) (rs : List Region), Frame rs t.mem t'.mem →
      ∀ i, (∀ r ∈ rs, (⟨S + BitVec.ofNat 64 (4 * i), 4⟩ : Region).Disjoint r) →
      t'.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = t.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 :=
    fun t t' rs hf i hd => hf.readW (Region.contains_self _ _) hd (by decide)
  have done4 : ∀ i < 16 * (c + 1), t4.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = Spec.Seed.g (gInput key i) := by
    intro i hi'
    rw [m4]
    by_cases hlo : i < 16 * c
    · rw [lvS t2 t3 _ f3 i (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; simp only [outR, a1_2, Nat.mul_zero]
          rw [BitVec.add_zero]
          exact Offset.disjoint _ (Or.inl (by omega)) (by omega) (by omega)),
        lvS t t2 _ f2 i (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [workS t hi.sb]
          exact schedWork.sub_left (Offset.sub_base _ (by omega))), hi.done i hlo]
    · obtain ⟨w, rfl⟩ : ∃ w, i = 16 * c + w := ⟨i - 16 * c, by omega⟩
      have := v3 w (by omega)
      rw [a1_2, Offset.add_add, show 64 * c + 4 * (0 + w) = 4 * (16 * c + w) by omega] at this
      rw [this, g2 w (by omega), hi.cur w (by omega)]
  have frame4 : Frame [workR s, ⟨S, 128⟩] s.mem t4.mem := by
    rw [m4]
    refine (hi.frame.trans (f2.sub ?_)).trans (f3.sub ?_)
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s, List.mem_cons_self, by rw [workS t hi.sb]; exact fun _ h => h⟩
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      simp only [outR, a1_2, Nat.mul_zero]; rw [BitVec.add_zero]
      exact Offset.sub_base _ (by omega)
  have room4 : Room t4 := room_congr hi.room (sb_4.trans hi.sb.symm) (by rw [wr4, wr3, wr2, hi.wr])
  have masks4 : Masks t4 := by
    refine masks2.frame' (by rw [G4 _ (by decide) (by decide) (by decide) (by decide)])
      (G4 _ (by decide) (by decide) (by decide) (by decide)) (by rw [m4]; exact f3) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact (out2.sub_right (masksR_sub t2)).symm
  have regs4 : ∀ r ∈ [Reg.ra, .a0, .a2, .a3, .a5], t4.gpr r = s.gpr r := by
    intro r hr
    have hn : r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .a1 ∧ r ≠ .a4 ∧ r ∉ g16Writes := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [G4 r hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1, regs2 r hn.2.2.2.2, hi.regs r hr]
  refine WP.seq (WP.of_runBlock ⟨t4, runBlock_trans (runBlock_trans e2 e3) e4, ?_⟩)
  refine WP.ite (decide (c = 0)) ev4 (fun hb => ?_) (fun hb => ?_)
  · -- the second sixteen inputs
    have hc0 : c = 0 := by simpa using hb
    subst hc0
    obtain ⟨t5, e5, room5, v5, f5, rd5, wr5, sp5, g5⟩ := keyMove_ok room4
    refine WP.of_runBlock ⟨t5, e5, .inr ⟨?_, 1, by omega, 1, by omega, rfl, ?_⟩⟩
    · rw [RISCV64.Steps.eval_nonzero, g5 _ (by decide) (by decide), a4_4]
      decide
    have sb_5 : t5.gpr sb = s.gpr sb := (g5 _ (by decide) (by decide)).trans sb_4
    have workF : Frame [workR s] t4.mem t5.mem := by
      refine f5.sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨workR s, List.mem_cons_self, by rw [← workS t4 sb_4]; exact arraysR_sub_work t4⟩
    refine ⟨room5, masks4.frame (g5 _ (by decide) (by decide)) (g5 _ (by decide) (by decide))
        (by rw [workS t4 sb_4]; exact workF), sb_5,
      by rw [g5 _ (by decide) (by decide), a1_4], by rw [g5 _ (by decide) (by decide), a4_4],
      fun r hr => by
        rw [g5 r (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
                     rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
          (by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
              rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide), regs4 r hr],
      fun w hw => ?_, fun h => absurd h (by decide), fun i hi' => ?_, by rw [rd5, rd4, rd3, rd2, hi.rd],
      by rw [wr5, wr4, wr3, wr2, hi.wr], by rw [sp5, sp4, sp3, sp2, hi.sp],
      frame4.trans (workF.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)⟩
    · rw [v5 _ (by decide) w hw, show newVal spMove (tSlot 0) (fun k' => lv t4 k' w) = lv t4 uSlot w from rfl,
        show lv t4 uSlot w = lv t3 uSlot w by
          simp only [lv, laneA, m4, g4 _ (show sb ≠ .a1 by decide) (show sb ≠ .a4 by decide)],
        lv_frame (g3 _ (by decide) (by decide)) f3 out2 (by decide) hw, keep2 uSlot (by decide) (by decide) w hw,
        hi.next rfl w hw]
    · rw [lvS t4 t5 _ workF i (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact schedWork.sub_left (Offset.sub_base _ (by omega)))]
      exact done4 i hi'
  · -- the end
    have hc1 : c = 1 := by simp at hb; omega
    subst hc1
    refine WP.block_nil (.inl ⟨?_, hQ t4 done4 regs4 (by rw [rd4, rd3, rd2, hi.rd])
      (by rw [wr4, wr3, wr2, hi.wr]) (by rw [sp4, sp3, sp2, hi.sp]) frame4⟩)
    rw [RISCV64.Steps.eval_nonzero, a4_4]
    decide

end VG.Proof.Seed.RISCV64
