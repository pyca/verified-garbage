module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.EcbLoop
public import VerifiedGarbage.Proof.Modes.RISCV64.Seq
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.RISCV64.BigFrame
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.TripleDes.RISCV64.ModeCore

/-!
# Triple DES ECB on RISC-V

`ecb_wp`: in the modes' frame of 80 slots below the stack pointer, the
caller's `s1`–`s4` saved (`saves_wp`), the schedules copied
(`Mode.prepare_wp`), the blocks (`loop_ok`), the registers restored
(`restore_wp`) and the frame zeroed (`wipe_wp`).
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Ecb

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.TripleDes.RISCV64 VG.Impl.TripleDes.RISCV64.Ecb
open VG.Proof.Modes.RISCV64 (slotA kept Fb Saves saves_wp scrIn_of' restore_wp wipe_wp coreRegion
  ScrIn)
open VG.Impl.Modes.RISCV64 (Core)
open VG.Spec.TripleDes (Direction Schedule)
open VG.Proof.TripleDes (blockAt_eq_of_frame scheduleAt_eq_of_frame)

/-- What ECB may assume: the schedule readable, the `n` blocks writable,
apart from each other and from the 640 bytes below the stack pointer, the
blocks not wrapping around. -/
structure EcbPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a0, 384⟩]
  wr : s.wr = [⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩]
  keyData : (⟨s.gpr .a0, 384⟩ : Region).Disjoint ⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩
  fit : (s.gpr .a1).toNat + 8 * (s.gpr .a2).toNat ≤ 2 ^ 64
  al : s.sp.toNat % 16 = 0
  sp : 640 ≤ s.sp.toNat
  stackKey : (⟨s.sp - 640, 640⟩ : Region).Disjoint ⟨s.gpr .a0, 384⟩
  stackData : (⟨s.sp - 640, 640⟩ : Region).Disjoint ⟨s.gpr .a1, 8 * (s.gpr .a2).toNat⟩

theorem ecb_wp (d : Direction) {s : State} (h : EcbPre s) :
    WP isa (Ecb.ecb d) s fun s' => abiPreserved s s' ∧ ∀ b < (s.gpr .a2).toNat,
      Spec.TripleDes.blockAt s'.mem (wAt (s.gpr .a1) b) =
        blockResult (Spec.TripleDes.scheduleAt s.mem (s.gpr .a0)) d
          (Spec.TripleDes.blockAt s.mem (wAt (s.gpr .a1) b)) := by
  have fit := h.fit
  let c := dirCore d
  let D := s.gpr .a1
  let n := (s.gpr .a2).toNat
  let k := Spec.TripleDes.scheduleAt s.mem (s.gpr .a0)
  have hL := Mode.layout d
  have htot : c.total = 80 := rfl
  have hB : Fb s c = s.sp - 640 := rfl
  unfold Ecb.ecb
  refine WP.ite (s.gpr .a2 == 0) (by rw [eval_zero]) (fun hz => ?_) (fun hz => ?_)
  · have hn : (s.gpr .a2).toNat = 0 := by simp only [beq_iff_eq] at hz; simp [hz]
    exact WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl⟩, fun b hb => absurd hb (by omega)⟩
  have hn : 0 < n := by
    have : s.gpr .a2 ≠ 0 := by simpa using hz
    have : (s.gpr .a2).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq e)
    omega
  have hBnat : (Fb s c).toNat = s.sp.toNat - 640 := Proof.Modes.RISCV64.fb_toNat' (c := c) h.sp
  refine bigFrame_wp (n := 8 * c.total) (by rw [htot]) (by rw [htot]; exact h.sp) fun t ht => ?_
  have hS : ScrIn t (Fb s c) c.total := scrIn_of' h.al h.sp hL ht
  obtain ⟨ws, hws⟩ := ht.wr
  have hframeR : (⟨Fb s c, 640⟩ : Region) ∈ t.wr := hS.low
  have hdataR : (⟨D, 8 * n⟩ : Region) ∈ t.wr := by rw [hws, h.wr]; simp [D, n]
  have sepDF : (⟨D, 8 * n⟩ : Region).Disjoint ⟨Fb s c, 640⟩ := by rw [hB]; exact h.stackData.symm
  -- The entry.
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (saves_wp hL hS ht) fun s₁ h₁ => wp_mv fun s₂ u₂ => WP.block_nil ?_
  have b₂ : s₂.gpr sb = Fb s c := by rw [u₂.other _ (by decide)]; exact h₁.b
  have a0₂ : s₂.gpr .a0 = s.gpr .a0 :=
    by rw [u₂.other _ (by decide), h₁.other _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  have s2₂ : s₂.gpr .s2 = D := by rw [u₂.other _ (by decide), h₁.s2]
  have s3₂ : s₂.gpr .s3 = s.gpr .a2 := by
    rw [u₂.gpr, h₁.other _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  have keep₂ : ∀ r ∈ kept, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → s₂.gpr r = s.gpr r :=
    fun r hr h1 h2 h3 h4 => by
      rw [u₂.other r h3, h₁.other r (Proof.Modes.RISCV64.kept_ne_entry r hr).1 h1 h2 h3 h4]
  have rd₂ : s₂.rd = s.rd := by rw [u₂.rd, h₁.rd]
  have wr₂ : s₂.wr = t.wr := by rw [u₂.wr, h₁.wr]
  have m₂ : s₂.mem = s₁.mem := u₂.mem
  -- The schedules copied.
  let rs : List Region := [⟨Fb s c, 8 * c.total⟩, ⟨D, 8 * n⟩]
  have hk : Mode.KeyArgs s₂ rs k := by
    refine ⟨?_, by simp only [Mode.keyR, rd₂, a0₂, h.rd]; simp, fun r hr => ?_⟩
    · rw [a0₂, m₂, scheduleAt_eq_of_frame _ h₁.frame fun r hr => ?_]
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.stackKey.symm.sub_right (Region.sub_prefix (by decide)))
    · simp only [rs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [Mode.keyR, a0₂, htot, hB]; exact h.stackKey.symm
      · simp only [Mode.keyR, a0₂]; exact h.keyData
  apply WP.seq
  refine WP.mono (Mode.prepare_wp d b₂ (hS.congr wr₂) List.mem_cons_self hk)
    fun s₃ ⟨⟨ready₃, _⟩, b₃, kept₃, f₃, rd₃, wr₃⟩ => ?_
  have sv₃ : ∀ i < 4, s₃.mem.readW (slotA (Fb s c) i) 64 = s.gpr (Core.savedRegs.getD i .s1) := by
    intro i hi
    have e := h₁.saved i hi
    rw [← m₂] at e
    rw [← e]
    exact f₃.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by simp only [Impl.Modes.RISCV64.coreSlot]; omega)) (by omega)
        (by cases d <;> decide)) (by decide)
  have data₃ : ∀ b < n, Spec.TripleDes.blockAt s₃.mem (wAt D b) = Spec.TripleDes.blockAt s.mem (wAt D b) := by
    intro b hb
    have hsub : Region.Sub ⟨wAt D b, 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega)
    rw [blockAt_eq_of_frame _ f₃ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (sepDF.sub_left hsub).sub_right (Offset.sub_base _ (by cases d <;> decide)),
      m₂, blockAt_eq_of_frame _ h₁.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (sepDF.sub_left hsub).sub_right (Region.sub_prefix (by decide))]
  -- The blocks.
  have E : Env (Fb s c) D n s₃.wr :=
    ⟨hS.al, by have := hS.fit; simpa [htot] using this, by rw [wr₃, wr₂]; exact hframeR,
      by rw [wr₃, wr₂]; exact hdataR, fit, sepDF⟩
  have p₃ : s₃.gpr .s2 = wAt D 0 := by
    rw [kept₃ _ (by decide), s2₂]; exact (BitVec.add_zero _).symm
  have c₃ : s₃.gpr .s3 = BitVec.ofNat 64 (n - 0) := by
    rw [kept₃ _ (by decide), s3₂]; simp [n]
  have I0 : EInv k d (Fb s c) D n s₃ 0 s₃ :=
    ⟨by omega, p₃, c₃, b₃, ready₃, fun _ _ _ _ => rfl, rfl, rfl, rfl,
      fun _ _ => rfl, fun b hb => absurd hb (by omega), fun _ _ _ => rfl⟩
  apply WP.seq
  refine WP.mono (loop_ok E hn I0) fun s₄ I => ?_
  -- The registers restored and the frame zeroed.
  have sv₄ : ∀ i < 4, s₄.mem.readW (slotA (Fb s c) (Core.savedSlot i)) 64 =
      s.gpr (Core.savedRegs.getD i .s1) := fun i hi => (I.saved i hi).trans (sv₃ i hi)
  have hS₄ : ScrIn s₄ (Fb s c) c.total := hS.congr (by rw [I.wr, wr₃, wr₂])
  apply WP.seq
  rw [← List.append_nil Core.restore]
  refine restore_wp hL hS₄ I.b sv₄ fun u g1 g2 g3 g4 g3' g mu rdu wru => WP.block_nil ?_
  refine WP.mono (wipe_wp hL (hS₄.congr wru) g3') fun s' ⟨_, f', g', _, _⟩ => ⟨?_, fun b hb => ?_⟩
  · refine ⟨fun r hr => ?_, rfl, ?_⟩
    · show s'.gpr r = s.gpr r
      have h0 : r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t3 := by revert hr; decide +revert
      rw [g' r h0.1 h0.2.1 h0.2.2.1]
      by_cases e1 : r = .s1
      · subst e1; exact g1
      by_cases e2 : r = .s2
      · subst e2; exact g2
      by_cases e3 : r = .s3
      · subst e3; exact g3
      by_cases e4 : r = .s4
      · subst e4; exact g4
      have hk : r ∈ kept := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)
      rw [g r e1 e2 e3 e4 h0.2.2.2, I.keep r hk e2 e3, kept₃ r hk, keep₂ r hk e1 e2 e3 e4]
    · show s'.gpr .ra = s.gpr .ra
      rw [g' _ (by decide) (by decide) (by decide), g _ (by decide) (by decide) (by decide) (by decide)
        (by decide), I.keep _ (by decide) (by decide) (by decide), kept₃ _ (by decide),
        keep₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · show Spec.TripleDes.blockAt s'.mem (wAt D b) = _
    have hsub : Region.Sub ⟨wAt D b, 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega)
    rw [blockAt_eq_of_frame _ f' fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (sepDF.sub_left hsub).sub_right (Region.sub_prefix (by cases d <;> decide)),
      mu, I.done b hb, data₃ b hb]

end VG.Proof.TripleDes.RISCV64.Ecb
