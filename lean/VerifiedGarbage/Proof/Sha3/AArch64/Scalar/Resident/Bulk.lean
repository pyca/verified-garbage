import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Resident.Loop

/-!
# The scalar resident absorber: whole blocks

`bulk_correct`: from where the resident absorber of `Sha3.Vector.Resident`
runs its bulk (`BulkPre`), `bulk` consumes the whole blocks and leaves the
state in memory and the arguments as that absorber's contract for it says
(`BulkPost`), which `Sha3.Vector.Resident.correct` completes with the
ordinary streaming absorb.
-/

namespace VG.Proof.Sha3.AArch64.Scalar.Resident

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar
open VG.Impl.Sha3.AArch64.Scalar.Resident
open VG.Proof.Sha3.AArch64.Scalar.Boundary
open VG.Proof.Sha3.AArch64.Sha3.Vector.Resident (BulkPre BulkPost BulkResult rate st data len
  stateR scratchR)
open VG.Spec.Sha3 (stateAt bytesAt)

theorem setup_ok (b : State) (hp : BulkPre b) :
    WP isa (.block setup) b (Loop b 0 (stateAt b.mem (st b))) := by
  unfold setup
  rw [WP.block_append_iff, WP.block_append_iff]
  refine (save_ok b).mono fun s₁ ⟨hk₁, hg₁, hm₁, hs₁, hp₁, hv₁⟩ => ?_
  unfold keep
  refine WP.cons rfl (WP.cons rfl (WP.cons rfl (wp_nil ?_)))
  let s₂ := ((s₁.setV .v19 (ofVDwords (s₁.gpr .x3) (s₁.gpr .x3))).setV .v20
    (ofVDwords (s₁.gpr .x4) (s₁.gpr .x4))).setV .v21 (ofVDwords (s₁.gpr .x6) (s₁.gpr .x6))
  change WP isa (.block Boundary.load) s₂ _
  have hv₂ : ∀ q, q ≠ .v19 → q ≠ .v20 → q ≠ .v21 → s₂.v q = s₁.v q := fun q a c d => by
    simp only [s₂, RegUpd.v_setV, a, c, d, ite_false]
  have hin : ∀ i < 25, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x0 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    change InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x0 + BitVec.ofNat 64 (8 * i)) 8
    rw [hk₁.rd, hk₁.wr, hg₁, hp.wr]
    exact ⟨stateR b, by simp, VG.Proof.Sha3.lane_contains _ hi⟩
  refine (load_ok s₂ hin).mono fun s₃ ⟨hk₃, hm₃, hv₃, hl₃⟩ => ?_
  have hst : stateAt s₂.mem (s₂.gpr .x0) = stateAt b.mem (st b) := by
    change stateAt s₁.mem (s₁.gpr .x0) = _
    rw [hm₁, hg₁]
  rw [hst] at hl₃
  have hvb : ∀ q, q ≠ .v19 → q ≠ .v20 → q ≠ .v21 → s₃.v q = s₁.v q := fun q a c d => by
    rw [hv₃]; exact hv₂ q a c d
  have hkv : ∀ q ∈ [VReg.v19, .v20, .v21], ∀ x : Reg, q = .v19 ∧ x = .x3 ∨ q = .v20 ∧ x = .x4 ∨
      q = .v21 ∧ x = .x6 → vdword (s₃.v q) 0 = b.gpr x := by
    intro q _ x hx
    rw [hv₃]
    rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [s₂, RegUpd.v_setV, reduceCtorEq, ite_true, ite_false, vdword_ofVDwords_0, hg₁]
  refine ⟨Nat.zero_le _, Nat.zero_mod _, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, hl₃⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact hk₃.rd.trans hk₁.rd
  · exact hk₃.wr.trans hk₁.wr
  · exact hk₃.sp.trans hk₁.sp
  · simpa only [Ptrs, hvb .v30 (by decide) (by decide) (by decide),
      hvb .v31 (by decide) (by decide) (by decide)] using hp₁
  · intro i hi
    have hn : ∀ i < 11, Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v19 ∧
        Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v20 ∧
        Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v21 := by decide
    change vdword (s₃.v _) 0 = _
    rw [hvb _ (hn i hi).1 (hn i hi).2.1 (hn i hi).2.2]
    exact hs₁ i hi
  · intro q hq
    have hn : ∀ q ∈ preservedV, q ≠ .v19 ∧ q ≠ .v20 ∧ q ≠ .v21 := by decide
    rw [hvb q (hn q hq).1 (hn q hq).2.1 (hn q hq).2.2]
    exact hv₁ q hq
  · exact hm₃.trans hm₁
  · rw [hkv .v19 (by simp) .x3 (.inl ⟨rfl, rfl⟩), BitVec.add_zero]
  · rw [hkv .v20 (by simp) .x4 (.inr (.inl ⟨rfl, rfl⟩)), Nat.sub_zero, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  · rw [hkv .v21 (by simp) .x6 (.inr (.inr ⟨rfl, rfl⟩)), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro msg hm _
    simpa only [bytesAt, List.range_zero, List.map_nil, List.append_nil] using hm

theorem finish_ok (b : State) (hp : BulkPre b) (c : Nat) (A : Spec.Sha3.State) (s : State)
    (h : Loop b c A s) :
    WP isa (.block finish) s (BulkPost b) := by
  unfold finish
  rw [WP.block_append_iff, WP.block_append_iff]
  have hout : ∀ i < 25, InRegions s.wr (b.gpr .x0 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [h.core.keep.wr, hp.wr]
    exact ⟨stateR b, by simp, VG.Proof.Sha3.lane_contains _ hi⟩
  refine (store_ok s (b.gpr .x0) A h.core.lanes h.core.ptrs.1 hout).mono
    fun t ⟨hkt, hvt, hft, hat⟩ => ?_
  have hst : SavedVector b t := by simpa only [SavedVector, hvt] using h.core.saved
  refine (restore_ok b t hst).mono fun u ⟨hku, hmu, hvu, hgu⟩ => ?_
  have hv : u.v = s.v := hvu.trans hvt
  refine WP.cons (Sha3.Vector.exec_umov_low _ .x0 .v30) (WP.cons (Sha3.Vector.exec_umov_low _ .x1 .v31)
    (WP.cons (Sha3.Vector.exec_umov_low _ .x3 .v19) (WP.cons (Sha3.Vector.exec_umov_low _ .x4 .v20)
      (WP.cons (Sha3.Vector.exec_umov_low _ .x6 .v21) (WP.cons (exec_addImm_x (by decide))
        (WP.cons rfl (wp_nil ?_)))))))
  refine ⟨c, h.c_le, h.aligned, ⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · have hn : ∀ r ∈ preserved, r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x5 ∧
        r ≠ .x6 := by decide
    obtain ⟨n0, n1, n2, n3, n4, n5, n6⟩ := hn r hr
    simp only [RegUpd.gpr_write, n0, n1, n2, n3, n4, n5, n6, ite_false]
    exact hgu r hr
  · exact hku.sp.trans (hkt.sp.trans h.core.keep.sp)
  · simp only [RegUpd.v_write, hv, h.core.vec r hr]
  · exact hku.rd.trans (hkt.rd.trans h.core.keep.rd)
  · exact hku.wr.trans (hkt.wr.trans h.core.keep.wr)
  · simp only [RegUpd.mem_write, hmu]
    rw [← h.mem]
    exact hft.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, Size.bits, BitVec.setWidth_eq,
      RegUpd.v_write, hv]
    exact h.core.ptrs.1
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, Size.bits, BitVec.setWidth_eq,
      RegUpd.v_write, hv]
    exact h.core.ptrs.2
  · simp only [RegUpd.gpr_write_self, Size.bits, BitVec.setWidth_eq]
    exact hp.x2.symm
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, Size.bits, BitVec.setWidth_eq,
      RegUpd.v_write, hv]
    exact h.dp
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, Size.bits, BitVec.setWidth_eq,
      RegUpd.v_write, hv]
    exact h.left
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, Size.bits, BitVec.setWidth_eq,
      RegUpd.v_write, hv, State.read, BitVec.add_zero]
    rw [h.core.ptrs.2, hp.x5]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, Size.bits, BitVec.setWidth_eq,
      RegUpd.v_write, hv, h.rt, BitVec.ofNat_toNat]
  · intro msg hm hal
    simp only [RegUpd.mem_write, hmu]
    rw [hat]
    exact h.repr msg hm hal

theorem functional (b : State) (hp : BulkPre b) : WP isa bulk b (BulkPost b) := by
  unfold bulk
  rw [WP.seq_iff]
  refine (setup_ok b hp).mono fun s₀ h₀ => ?_
  rw [WP.seq_iff]
  refine (loop_ok b hp _ s₀ h₀).mono fun s ⟨c, A, h⟩ => ?_
  exact finish_ok b hp c A s h

#assert_standard_axioms functional

end VG.Proof.Sha3.AArch64.Scalar.Resident
