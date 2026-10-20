module

public import VerifiedGarbage.Impl.Sha3.AArch64.Hybrid.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRound
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.MemCoreExec
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Control
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.ScheduleFacts
public import VerifiedGarbage.Proof.Sha3.AArch64.Hybrid.Comm
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Parity
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Sha3.AArch64.Permute
import VerifiedGarbage.Proof.Framework.Contract

/-!
# A round of Keccak-f[1600] on three states

`Hybrid.round off r` (`Impl/Sha3/AArch64/Hybrid/Round.lean`) runs round `r`
on the two states in the vector registers (`Neon.Hw.Pairs`) and on the
state in the general registers (`Scalar.laneReg`), writing no memory but the
scalar round's two temporary words at `[sp, #off]`: the woven cores run as
the vector core and then the scalar one (`Hybrid.indeps`), and iota follows
for all three from the constant in `x26`.
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Hybrid
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.Sha3.AArch64.Neon.Hw
open VG.Proof.Sha3.AArch64.Neon (Pairs vreg_inj pair_xor)
open VG.Proof.Sha3.AArch64.Sha3.Vector (chiWord)
open VG.Proof.MlKem.AArch64 (wp_vop)

abbrev laneReg := VG.Impl.Sha3.AArch64.Scalar.laneReg

theorem vecCore_vecOnly : Impl.Sha3.AArch64.Hybrid.vecCore.all vecOnly = true := by decide

theorem memCore_scalarOnly (off : Nat) :
    (Impl.Sha3.AArch64.Scalar.memCoreInstrs off).all scalarOnly = true := by
  unfold Impl.Sha3.AArch64.Scalar.memCoreInstrs
  rw [List.all_flatMap]
  refine List.all_eq_true.mpr fun op _ => ?_
  cases op <;> rfl

/-- Round `r` on the three states. -/
theorem round_ok {off r : Nat} (hr : r < 24) {s : State} {A B C : Spec.Sha3.State}
    (hp : Pairs s A B) (hl : ∀ i (hi : i < 25), s.gpr (laneReg i) = C[i])
    (ho : Scalar.SlotsOk off s) :
    WP isa (.block (Impl.Sha3.AArch64.Hybrid.round off r)) s fun t =>
      Pairs t (Spec.Sha3.rnd A r) (Spec.Sha3.rnd B r) ∧
      (∀ i (hi : i < 25), t.gpr (laneReg i) = (Spec.Sha3.rnd C r)[i]) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ Frame [⟨s.sp, off + 16⟩] s.mem t.mem := by
  unfold Impl.Sha3.AArch64.Hybrid.round
  rw [List.append_assoc, WP.block_append_iff]
  refine VG.Interleave.WP.weave (P := fun _ => True)
    (indeps vecCore_vecOnly (memCore_scalarOnly off)) trivial ?_
  refine WP.mono (core2_ok hp) fun t ⟨hk, hc⟩ => ?_
  have ho' : Scalar.SlotsOk off t := ⟨ho.align, ho.small, fun k hk' => by
    rw [hk.wr, hk.sp]; exact ho.wr k hk'⟩
  obtain ⟨u, hu, hlu, hf, hrd, hwr, hsp, hv⟩ :=
    Scalar.mem_core_ok C t (fun i hi => by rw [hk.gpr]; exact hl i hi) ho'
  refine WP.of_runBlock ⟨u, hu, ?_⟩
  rw [WP.block_append_iff]
  refine (Scalar.Control.constant_ok (Spec.Sha3.RC r) u).mono fun w ⟨hkw, hw⟩ => ?_
  rw [Sha3.Vector.constantLow_RC r hr] at hw
  unfold Impl.Sha3.AArch64.Hybrid.iota
  refine WP.cons rfl ?_
  refine wp_vop (d := .v26) rfl fun s1 h1 => wp_vop (d := .v0) rfl fun t2 h2 =>
    WP.block_nil_iff.mpr ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The vector states: CPairs after the cores, kept by the scalar code.
    have hcw : CPairs w A B := by
      intro i hi; rw [hkw.vec, hv]; exact hc i hi
    have hrc : (w.write .x .x0 (w.read .x .x0 ^^^ w.read .x .x26)).gpr .x26 = Spec.Sha3.RC r := by
      simp only [RegUpd.gpr_write, State.read, Size.bits, BitVec.setWidth_eq, reduceCtorEq,
        ite_false, hw]
    intro i hi
    rw [← Proof.Sha3.outState_eq A r, ← Proof.Sha3.outState_eq B r, out_word A _ hi, out_word B _ hi]
    by_cases h0 : i = 0
    · subst i
      change t2.v .v0 = ofVDwords (chiWord A 0 ^^^ _) (chiWord B 0 ^^^ _)
      rw [h2.v, h1.get .v0, h1.v, hrc]
      change (w.write .x .x0 _).v .v0 ^^^ ofVDwords (Spec.Sha3.RC r) (Spec.Sha3.RC r) = _
      rw [RegUpd.v_write, show w.v .v0 = _ from hcw 0 (by decide), pair_xor]
    · rw [ite_eq_right h0, ite_eq_right h0, h2.get (vreg i) (by
        change ¬ vreg i = vreg 0
        rw [vreg_inj i (by omega) 0 (by decide)]; exact h0), h1.get (vreg i)
        ((show ∀ i < 25, vreg i ≠ .v26 by decide) i hi), RegUpd.v_write]
      exact hcw i hi
  · -- The scalar state: chi's lanes, then iota on lane 0.
    intro i hi
    have h26 := Scalar.scratch_not_lane .x26 (by simp) i hi
    have h0 : w.gpr .x0 = (Spec.Sha3.chi (Spec.Sha3.pi (Spec.Sha3.rho (Spec.Sha3.theta C))))[0] :=
      (hkw.gpr .x0 (by decide)).trans (hlu 0 (by decide))
    rw [h2.gpr, h1.gpr]
    simp only [RegUpd.gpr_write, State.read, Size.bits, BitVec.setWidth_eq]
    by_cases hz : i = 0
    · subst i
      simp only [Impl.Sha3.AArch64.Scalar.laneReg, ite_true, h0, hw, Spec.Sha3.rnd, Spec.Sha3.iota,
        Vector.getElem_set_self]
    · have hr0 : laneReg i ≠ .x0 := by
        intro he; exact hz ((Scalar.laneReg_zero i hi).mp he)
      simp only [hr0, ite_false, hkw.gpr _ h26, hlu i hi, Spec.Sha3.rnd, Spec.Sha3.iota,
        Vector.getElem_set, Ne.symm hz]
  · rw [h2.sp, h1.sp]; exact (hkw.sp.trans hsp).trans hk.sp
  · rw [h2.rd, h1.rd]; exact (hkw.rd.trans hrd).trans hk.rd
  · rw [h2.wr, h1.wr]; exact (hkw.wr.trans hwr).trans hk.wr
  · rw [h2.mem, h1.mem]
    change Frame _ s.mem w.mem
    rw [hkw.mem, ← hk.mem, ← hk.sp]
    exact hf

/-- Rounds `rs` on the three states. -/
theorem rounds_list_ok {off : Nat} (rs : List Nat) (hrs : ∀ r ∈ rs, r < 24) {s : State}
    {A B C : Spec.Sha3.State} (hp : Pairs s A B) (hl : ∀ i (hi : i < 25), s.gpr (laneReg i) = C[i])
    (ho : Scalar.SlotsOk off s) :
    WP isa (.block (rs.flatMap (Impl.Sha3.AArch64.Hybrid.round off))) s fun t =>
      Pairs t (rs.foldl Spec.Sha3.rnd A) (rs.foldl Spec.Sha3.rnd B) ∧
      (∀ i (hi : i < 25), t.gpr (laneReg i) = (rs.foldl Spec.Sha3.rnd C)[i]) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ Frame [⟨s.sp, off + 16⟩] s.mem t.mem := by
  induction rs generalizing A B C s with
  | nil => exact wp_nil ⟨hp, hl, rfl, rfl, rfl, Frame.refl _ _⟩
  | cons r rs ih =>
    rw [List.flatMap_cons, List.foldl_cons, List.foldl_cons, List.foldl_cons, WP.block_append_iff]
    refine (round_ok (hrs r (by simp)) hp hl ho).mono fun t ⟨hpt, hlt, hsp, hrd, hwr, hf⟩ => ?_
    have ho' : Scalar.SlotsOk off t := ⟨ho.align, ho.small, fun k hk => by
      rw [hwr, hsp]; exact ho.wr k hk⟩
    refine (ih (fun q hq => hrs q (by simp only [List.mem_cons]; exact Or.inr hq)) hpt hlt ho').mono
      fun u ⟨hpu, hlu, hsp', hrd', hwr', hf'⟩ => ⟨hpu, hlu, hsp'.trans hsp, hrd'.trans hrd,
        hwr'.trans hwr, hf.trans (by rw [← hsp]; exact hf')⟩

/-- The 24 rounds: Keccak-f[1600] on each of the three states. -/
theorem rounds_ok {off : Nat} {s : State} {A B C : Spec.Sha3.State} (hp : Pairs s A B)
    (hl : ∀ i (hi : i < 25), s.gpr (laneReg i) = C[i]) (ho : Scalar.SlotsOk off s) :
    WP isa (.block (Impl.Sha3.AArch64.Hybrid.rounds off)) s fun t =>
      Pairs t ((List.range 24).foldl Spec.Sha3.rnd A) ((List.range 24).foldl Spec.Sha3.rnd B) ∧
      (∀ i (hi : i < 25), t.gpr (laneReg i) = ((List.range 24).foldl Spec.Sha3.rnd C)[i]) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ Frame [⟨s.sp, off + 16⟩] s.mem t.mem :=
  rounds_list_ok (List.range 24) (fun _ h => List.mem_range.mp h) hp hl ho

end VG.Proof.Sha3.AArch64.Hybrid
