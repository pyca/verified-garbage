module

import VerifiedGarbage.Proof.TripleDes.PPC64LE.KeySteps
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Key.Load
public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Write
import VerifiedGarbage.Proof.TripleDes.KeySchedule
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.ExpandKey
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Spec.TripleDes
public import VerifiedGarbage.TCB.PPC64LE.Isa

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE.Key

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE

structure RotatePost (c d : BitVec 28) (n : Nat) (s s' : State) : Prop where
  c : s'.gpr .r0 = (c.rotateLeft n).setWidth 64
  d : s'.gpr .r7 = (d.rotateLeft n).setWidth 64
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r, r ≠ .r8 → r ≠ .r0 → r ≠ .r7 → s'.gpr r = s.gpr r

theorem rotate_ok (s : State) (c d : BitVec 28)
    (hc : s.gpr .r0 = c.setWidth 64) (hd : s.gpr .r7 = d.setWidth 64)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 28) :
    WP isa (Impl.TripleDes.PPC64LE.Key.rotate n) s (RotatePost c d n s) := by
  rw [Impl.TripleDes.PPC64LE.Key.rotate, WP.block_append_iff]
  obtain ⟨s₁, run₁, c₁, mem₁, rd₁, wr₁, reg₁⟩ := rotate28_ok s .r0 (by decide) c hc n hn hn'
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have d₁ : s₁.gpr .r7 = d.setWidth 64 := (reg₁ .r7 (by decide) (by decide)).trans hd
  obtain ⟨s₂, run₂, d₂, mem₂, rd₂, wr₂, reg₂⟩ := rotate28_ok s₁ .r7 (by decide) d d₁ n hn hn'
  refine WP.of_runBlock ⟨s₂, run₂, ⟨(reg₂ .r0 (by decide) (by decide)).trans c₁, d₂,
    mem₂.trans mem₁, rd₂.trans rd₁, wr₂.trans wr₁, ?_⟩⟩
  intro r ha hc hd
  exact (reg₂ r hd ha).trans (reg₁ r hc ha)

theorem comparison_values : ∀ j < 16, ∀ k < 16,
    ((BitVec.ofNat 64 j >>> 1) == (0 : BitVec 64)) = decide (j < 2) ∧
    ((BitVec.ofNat 64 j - BitVec.ofNat 64 k) == (0 : BitVec 64)) = decide (j = k) := by
  decide

theorem write_keep (s : State) (v : BitVec 64) : Kept [.r8] s (s.write .r8 v) := by
  refine ⟨?_, rfl, rfl, rfl⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  exact gpr_write_of_ne _ _ hr

theorem lowTest_ok (s : State) (j : Nat) (hj : j < 16)
    (hv : s.gpr .r12 = BitVec.ofNat 64 j) :
    ∃ s', runBlock isa [.lsr .d .r8 .r12 1] s = some s' ∧
      isa.eval (.zero .d .r8) s' = some (decide (j < 2)) ∧ Kept [.r8] s s' := by
  refine ⟨s.write .r8 (s.gpr .r12 >>> 1), ?_, ?_, write_keep _ _⟩
  · rw [runBlock_cons, exec_lsr_d (by decide), runStep_some, runBlock_nil]
  · change VG.PPC64LE.eval (.zero .d .r8) _ = _
    simp only [VG.PPC64LE.eval, State.read, Size.bits, gpr_write_self, BitVec.setWidth_eq, hv]
    exact congrArg some (comparison_values j hj 0 (by decide)).1

theorem eqTest_ok (s : State) (j k : Nat) (hj : j < 16) (hk : k < 16)
    (hv : s.gpr .r12 = BitVec.ofNat 64 j) :
    ∃ s', runBlock isa [.subi .r8 .r12 k] s = some s' ∧
      isa.eval (.zero .d .r8) s' = some (decide (j = k)) ∧ Kept [.r8] s s' := by
  refine ⟨s.write .r8 (s.gpr .r12 - BitVec.ofNat 64 k), ?_, ?_, write_keep _ _⟩
  · rw [runBlock_cons, exec_subi (by decide) (by omega), runStep_some, runBlock_nil]
  · change VG.PPC64LE.eval (.zero .d .r8) _ = _
    simp only [VG.PPC64LE.eval, State.read, Size.bits, gpr_write_self, BitVec.setWidth_eq, hv]
    exact congrArg some (comparison_values j hj k hk).2

theorem rotation_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .r0 = c.setWidth 64) (hd : s.gpr .r7 = d.setWidth 64)
    (hjreg : s.gpr .r12 = BitVec.ofNat 64 j) :
    WP isa Impl.TripleDes.PPC64LE.Key.rotation s
      (RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
  rw [Impl.TripleDes.PPC64LE.Key.rotation]
  apply WP.seq
  obtain ⟨s₁, run₁, cond₁, keep₁⟩ := lowTest_ok s j hj hjreg
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have hrot (s' : State) (h : Kept [.r8] s s') (n : Nat) (hn : 1 ≤ n) (hn' : n < 28)
      (hv : Spec.TripleDes.rotations.getD j 0 = n) :
      WP isa (Impl.TripleDes.PPC64LE.Key.rotate n) s' (RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
    apply WP.mono (rotate_ok s' c d ((h.reg .r0 (by simp)).trans hc)
      ((h.reg .r7 (by simp)).trans hd) n hn hn')
    intro t ht
    rw [hv]
    exact ⟨ht.c, ht.d, ht.mem.trans h.mem, ht.rd.trans h.rd, ht.wr.trans h.wr,
      fun r ha hc hd => (ht.reg r ha hc hd).trans (h.reg r (by simpa only [List.mem_singleton] using ha))⟩
  have combine {a b : State} (ha : Kept [.r8] s a) (hb : Kept [.r8] a b) : Kept [.r8] s b :=
    ⟨fun r hr => (hb.reg r hr).trans (ha.reg r hr), hb.mem.trans ha.mem,
      hb.rd.trans ha.rd, hb.wr.trans ha.wr⟩
  by_cases h2 : j < 2
  · apply WP.ite true (by simpa only [h2, decide_true] using cond₁)
    · intro _
      exact hrot s₁ keep₁ 1 (by decide) (by decide)
        (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inl h2)])
    · simp
  · apply WP.ite false (by simpa only [h2, decide_false] using cond₁)
    · simp
    · intro _
      apply WP.seq
      obtain ⟨s₂, run₂, cond₂, keep₂⟩ := eqTest_ok s₁ j 8 hj (by decide)
        ((keep₁.reg .r12 (by simp)).trans hjreg)
      refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
      have keep₂' := combine keep₁ keep₂
      by_cases h8 : j = 8
      · apply WP.ite true (by simpa only [h8, decide_true] using cond₂)
        · intro _
          exact hrot s₂ keep₂' 1 (by decide) (by decide)
            (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inr (Or.inl h8))])
        · simp
      · apply WP.ite false (by simpa only [h8, decide_false] using cond₂)
        · simp
        · intro _
          apply WP.seq
          obtain ⟨s₃, run₃, cond₃, keep₃⟩ := eqTest_ok s₂ j 15 hj (by decide)
            ((keep₂'.reg .r12 (by simp)).trans hjreg)
          refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
          have keep₃' := combine keep₂' keep₃
          by_cases h15 : j = 15
          · apply WP.ite true (by simpa only [h15, decide_true] using cond₃)
            · intro _
              exact hrot s₃ keep₃' 1 (by decide) (by decide)
                (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inr (Or.inr h15))])
            · simp
          · apply WP.ite false (by simpa only [h15, decide_false] using cond₃)
            · simp
            · intro _
              exact hrot s₃ keep₃' 2 (by decide) (by decide)
                (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_right (by simp only [h2, h8, h15, or_self, not_false_eq_true])])

end VG.Proof.TripleDes.PPC64LE.Key
