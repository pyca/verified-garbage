import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Unrolled
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Control
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Wrap
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.ScheduleFacts
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.VectorCoreExec
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.UnrolledLit
import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint

/-!
# The unrolled scalar permutation: correctness

Each unrolled round is the vector-slot core (`vector_core_ok`), the round
constant built from immediates (`Control.constant_ok`) and its XOR into lane
0; together they keep `Boundary.CoreState`, the middle's contract in
`wrap_correct`.
-/

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar
open VG.Proof.Sha3.AArch64.Scalar.Boundary

theorem savedVec_not_temps : ∀ i < 11, Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v24 ∧
    Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v25 ∧
    Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v28 ∧
    Impl.Sha3.AArch64.Scalar.Boundary.savedVec i ≠ .v29 := by decide

theorem preservedV_not_temps : ∀ r ∈ preservedV, r ≠ .v24 ∧ r ≠ .v25 ∧ r ≠ .v28 ∧ r ≠ .v29 := by
  decide

/-- What the rounds keep besides the boundary's invariant: memory, and the
AdvSIMD registers other than the core's temporaries. -/
structure RoundKeep (s t : State) : Prop where
  mem : t.mem = s.mem
  v : ∀ v, v ≠ .v24 → v ≠ .v25 → v ≠ .v28 → v ≠ .v29 → t.v v = s.v v

theorem RoundKeep.refl (s : State) : RoundKeep s s := ⟨rfl, fun _ _ _ _ _ => rfl⟩

theorem RoundKeep.trans {s t u : State} (h : RoundKeep s t) (k : RoundKeep t u) : RoundKeep s u :=
  ⟨k.mem.trans h.mem, fun v a b c d => (k.v v a b c d).trans (h.v v a b c d)⟩

/-- One unrolled round computes `Rnd` and keeps the boundary's invariant. -/
theorem unrolled_round_ok (orig : State) (A : Spec.Sha3.State) (r : Nat) (hr : r < 24)
    (s : State) (hs : CoreState orig A s) :
    WP isa (.block (unrolledRound r)) s fun t =>
      CoreState orig (Spec.Sha3.rnd A r) t ∧ RoundKeep s t := by
  obtain ⟨t, ht, hl, hm, hrd, hwr, hsp, hv⟩ := vector_core_ok A s hs.lanes
  unfold unrolledRound
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨t, ht, ?_⟩
  rw [WP.block_append_iff]
  refine (Control.constant_ok (Spec.Sha3.RC r) t).mono fun u ⟨hk, hu⟩ => ?_
  rw [Sha3.Vector.constantLow_RC r hr] at hu
  refine WP.cons rfl (wp_nil ?_)
  have hvu : ∀ v, v ≠ .v24 → v ≠ .v25 → v ≠ .v28 → v ≠ .v29 → u.v v = s.v v :=
    fun v h24 h25 h28 h29 => (congrFun hk.vec v).trans (hv v h24 h25 h28 h29)
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ⟨hk.mem.trans hm, fun v a b c d => by
    rw [RegUpd.v_write]; exact hvu v a b c d⟩⟩
  · exact (hk.rd.trans hrd).trans hs.keep.rd
  · exact (hk.wr.trans hwr).trans hs.keep.wr
  · exact (hk.sp.trans hsp).trans hs.keep.sp
  · simp only [Ptrs, RegUpd.v_write]
    rw [hvu .v30 (by decide) (by decide) (by decide) (by decide),
      hvu .v31 (by decide) (by decide) (by decide) (by decide)]
    exact hs.ptrs
  · intro i hi
    have hn := savedVec_not_temps i hi
    change vdword ((u.write .x .x0 _).v _) 0 = _
    rw [RegUpd.v_write, hvu _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2]
    exact hs.saved i hi
  · intro q hq
    have hn := preservedV_not_temps q hq
    rw [RegUpd.v_write, hvu q hn.1 hn.2.1 hn.2.2.1 hn.2.2.2]
    exact hs.vec q hq
  · intro i hi
    have h26 := scratch_not_lane .x26 (by simp) i hi
    have h0 : u.gpr .x0 = (Spec.Sha3.chi (Spec.Sha3.pi (Spec.Sha3.rho (Spec.Sha3.theta A))))[0] :=
      (hk.gpr .x0 (by decide)).trans (hl 0 (by decide))
    simp only [RegUpd.gpr_write, State.read, Size.bits, BitVec.setWidth_eq]
    by_cases hz : i = 0
    · subst i
      simp only [Impl.Sha3.AArch64.Scalar.laneReg, ite_true, h0, hu, Spec.Sha3.rnd, Spec.Sha3.iota,
        Vector.getElem_set_self]
    · have hr0 : Impl.Sha3.AArch64.Scalar.laneReg i ≠ .x0 := by
        intro he; exact hz ((laneReg_zero i hi).mp he)
      simp only [hr0, ite_false, hk.gpr _ h26, hl i hi, Spec.Sha3.rnd, Spec.Sha3.iota,
        Vector.getElem_set, Ne.symm hz]

theorem unrolled_rounds_list_ok (rs : List Nat) (hrs : ∀ r ∈ rs, r < 24)
    (orig : State) (A : Spec.Sha3.State) (s : State) (hs : CoreState orig A s) :
    WP isa (.block (rs.flatMap unrolledRound)) s fun t =>
      CoreState orig (rs.foldl Spec.Sha3.rnd A) t ∧ RoundKeep s t := by
  induction rs generalizing A s with
  | nil => exact wp_nil ⟨hs, RoundKeep.refl s⟩
  | cons r rs ih =>
    rw [List.flatMap_cons, List.foldl_cons, WP.block_append_iff]
    exact (unrolled_round_ok orig A r (hrs r (by simp)) s hs).mono fun t ht =>
      (ih (fun q hq => hrs q (by simp only [List.mem_cons]; exact Or.inr hq)) _ t ht.1).mono
        fun u hu => ⟨hu.1, ht.2.trans hu.2⟩

theorem unrolled_rounds_ok (orig : State) (A : Spec.Sha3.State) (s : State)
    (hs : CoreState orig A s) :
    WP isa (.block unrolledRounds) s fun t =>
      CoreState orig (Spec.Sha3.keccakF A) t ∧ RoundKeep s t :=
  unrolled_rounds_list_ok (List.range 24) (fun _ h => List.mem_range.mp h) orig A s hs

/-- The unrolled permutation has the public permutation contract. -/
theorem unrolled_permute_correct (s : State) (hs : VG.Proof.Sha3.permuteAArch64.pre s) :
    ∃ t s', Exec isa unrolledPermute s t s' ∧ abiPreserved s s' ∧
      VG.Proof.Sha3.permuteAArch64.post s s' :=
  Boundary.wrap_correct (.block unrolledRounds) (fun orig A s _ hs => (unrolled_rounds_ok orig A s hs).mono fun _ h => h.1)
    s (VG.Proof.Sha3.AArch64.pre_of s hs)

theorem unrolled_permute_noCalls : unrolledPermute.noCalls = true := by lit_decide
theorem unrolled_permute_noFrames : unrolledPermute.noFrames = true := by lit_decide

theorem unrolled_permute_ct : ConstantTime isa VG.Proof.Sha3.permuteAArch64.pre
    VG.Proof.Sha3.permuteAArch64.pub unrolledPermute := by
  refine VG.Taint.constantTime (A := VectorTaint.taint) (VectorTaint.ofRegs [.x0, .x1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, hsp⟩
  refine ⟨⟨hsp, fun r hr => ?_⟩, ?_⟩
  · simp only [VectorTaint.ofRegs, Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption
  · intro r hr
    simp [VectorTaint.ofRegs, RegSet.mem_ofList] at hr

theorem unrolled_permute_verified :
    Verified AArch64.target unrolledPermute (Spec.Sha3.permuteContract AArch64.abi) :=
  Verified.of_correct unrolled_permute_correct unrolled_permute_ct (by
    sig_implies [Spec.Sha3.permuteContract, Spec.Sha3.permuteSig, VG.Proof.Sha3.permuteAArch64,
      AArch64.abi, AArch64.argRegs] [VG.Proof.Sha3.AArch64.satState]
      using VG.Proof.Sha3.AArch64.satState)

#assert_standard_axioms unrolled_permute_correct
#assert_standard_axioms unrolled_permute_ct
#assert_standard_axioms unrolled_permute_verified

end VG.Proof.Sha3.AArch64.Scalar
