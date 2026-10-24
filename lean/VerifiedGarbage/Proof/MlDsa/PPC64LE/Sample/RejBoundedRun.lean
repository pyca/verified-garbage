module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sample.RejBoundedBody
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# ML-DSA on PPC64LE: `vg_mldsa_rej_bounded_poly`, correctness

As on 32-bit ARM (`Proof/MlDsa/Arm/Sample/RejBoundedRun.lean`). The function
runs in pieces: the prologue (`J0`, with `η` zero-extended in `r27`), the
sponge, whose output is `H(ρ, 544)` (`J6`), the branch on `η` (`sel_ok`), and
the loop for `η`, iteration `t` of which starts from `Base` with the
coefficients `rbFold` samples from the first `t` bytes of output stored
(`loop_ok`); then the end returns whether there are 256 (`correct`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sample.RejBounded

open VG VG.PPC64LE
open VG.Proof.MlDsa.PPC64LE.Sample
open VG.Impl.MlDsa.PPC64LE.Sample
open VG.Impl.Sha3.PPC64LE.Stream (mov)
open VG.Proof.MlDsa.Sample (Stored stored_nil H_eq rbFold)
open VG.Proof.MlKem.PPC64LE (wp_loop_nz)
open VG.Spec.MlDsa (Zq H)
open VG.Spec.Sha3 (bytesAt)

/-- `J6` and `η` zero-extended in `r27`. -/
structure SJ (σ s : State) : Prop where
  j6 : ∃ s₀, J6 136 544 (spOf σ) σ s₀ s
  r27 : s.gpr .r27 = zx (σ.gpr .r4)

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

/-- The loop's setup, after the sponge. -/
theorem init_ok {s₀ s : State} (h : J6 136 544 (spOf σ) σ s₀ s) :
    WP isa (.block (([.addi .r3 .r31 840, mov .r4 .r30, .li .r5 0, .li .r6 544] : List Instr) ++ loadQ)) s
      (Base σ (X σ) 0 []) := by
  have g30 := h.j0.env.r30
  have g31 := h.j0.env.r31
  have hk : WP isa (.block (([.addi .r3 .r31 840, mov .r4 .r30, .li .r5 0, .li .r6 544] : List Instr) ++ loadQ)) s
      fun s' => s'.gpr .r3 = σ.gpr .r6 + BitVec.ofNat 64 (840 + 0) ∧ s'.gpr .r4 = σ.gpr .r5 ∧
        s'.gpr .r5 = BitVec.ofNat 64 0 ∧ s'.gpr .r6 = BitVec.ofNat 64 (544 - 0) ∧
        s'.gpr .r7 = BitVec.ofNat 64 8380417 ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    prun [loadQ, List.cons_append, List.nil_append, exec_lis, exec_ori, loadQ_val, g30, g31]
    simp only [true_and, and_true]
    pres_tac
  refine WP.mono hk fun s' ⟨g3, g4, g5, g6, g7, gp, m, rd, wr, sp⟩ => ⟨h.j0.env.regs hp m gp rd wr sp,
    by rw [m, h.out]; exact (H_eq _ _).symm, g3, g6, g7, ?_⟩
  exact ⟨by rw [g4]; exact (BitVec.add_zero _).symm, g5, by simp, stored_nil _ _⟩

/-- The loop for `η`. -/
theorem loop_ok {η : Nat} (hη : η = 2 ∨ η = 4) {s₀ s : State} (h : J6 136 544 (spOf σ) σ s₀ s) :
    WP isa (rbLoop η) s (Base σ (X σ) 544 (Lf η (X σ) 544)) :=
  WP.seq (WP.mono (init_ok hp h) fun _ h0 =>
    wp_loop_nz (fun t s => Base σ (X σ) t (Lf η (X σ) t) s) (N := 544) (by decide)
      (fun _ ht _ hs => body_ok hp hη (X_length σ) ht hs) (fun _ h => h) h0)

omit hp in
/-- The test of `η = 2`. -/
theorem eta_test (x : BitVec 64) : (zx x - BitVec.ofNat 64 2 == 0) = decide ((x.setWidth 32).toNat = 2) := by
  have e := zx_toNat x
  by_cases h : (x.setWidth 32).toNat = 2
  · have : zx x - BitVec.ofNat 64 2 = 0 := by bv_omega
    rw [this, decide_eq_true h]; rfl
  · have : zx x - BitVec.ofNat 64 2 ≠ 0 := by bv_omega
    rw [decide_eq_false h]; exact beq_eq_false_iff_ne.mpr this

/-- The test of `η = 2`, which keeps `J6`. -/
theorem cmp_ok {s : State} (h : SJ σ s) :
    WP isa (.block [.subi .r12 .r27 2]) s fun s' => SJ σ s' ∧ s'.gpr .r12 = zx (σ.gpr .r4) - BitVec.ofNat 64 2 := by
  obtain ⟨⟨s₀, j6⟩, e27⟩ := h
  have hk : WP isa (.block [.subi .r12 .r27 2]) s fun s' => s' = s.write .r12 (s.gpr .r27 - BitVec.ofNat 64 2) := by
    prun []
  refine WP.mono hk fun s' e' => ?_
  subst e'
  have gp : ∀ r ∈ preserved, (s.write .r12 (s.gpr .r27 - BitVec.ofNat 64 2)).gpr r = s.gpr r := by pres_tac
  exact ⟨⟨⟨s₀, j6.j0.regs hp rfl gp rfl rfl rfl, fun r hr => (gp r hr).trans (j6.gp r hr), j6.out⟩,
    (gp .r27 (by decide)).trans e27⟩, by rw [RegUpd.gpr_write_self, e27]⟩

/-- The branch on `η`, and the loop for it. -/
theorem sel_ok (hη : etaOf σ = 2 ∨ etaOf σ = 4) {s : State} (h : SJ σ s) :
    WP isa (.seq (.block [.subi .r12 .r27 2]) (.ite (.zero .d .r12) (rbLoop 2) (rbLoop 4))) s
      (Base σ (X σ) 544 (Lf (etaOf σ) (X σ) 544)) := by
  refine WP.seq (WP.mono (cmp_ok hp h) fun s1 ⟨h1, e12⟩ => ?_)
  obtain ⟨⟨s₀, j6⟩, _⟩ := h1
  refine WP.ite _ (by rw [eval_zero, e12, eta_test]) (fun he => ?_) (fun he => ?_)
  · simp only [decide_eq_true_eq] at he
    rw [show etaOf σ = 2 from he]
    exact loop_ok hp (.inl rfl) j6
  · simp only [decide_eq_false_iff_not] at he
    rw [show etaOf σ = 4 from hη.resolve_left he]
    exact loop_ok hp (.inr rfl) j6

/-- The whole function: `r3` whether the loop sampled 256 coefficients, those
stored, and the calling convention. -/
theorem correct (hη : etaOf σ = 2 ∨ etaOf σ = 4) :
    WP isa rejBounded σ fun s' =>
      s'.gpr .r3 = (if (Lf (etaOf σ) (X σ) 544).length = 256 then 1 else 0) ∧
      Stored s'.mem (σ.gpr .r5) (Lf (etaOf σ) (X σ) 544) ∧ abiPreserved σ s' := by
  unfold rejBounded
  refine WP.seq (WP.mono (pro_rb hp rfl rfl rfl rfl) fun s₀ ⟨j0, e27⟩ => ?_)
  refine WP.seq (WP.mono (sponge_ok hp (rate := 136) (outlen := 544) (by decide) (by decide) j0) fun s h => ?_)
  have sj : SJ σ s := ⟨⟨s₀, h⟩, (h.gp .r27 (by decide)).trans e27⟩
  refine WP.seq (WP.mono (sel_ok hp hη sj) fun s3 h3 => ?_)
  exact WP.mono (retEpi_ok hp h3.env h3.at'.r5 h3.at'.len) fun s' ⟨r3, hm, ha⟩ =>
    ⟨r3, by rw [hm]; exact h3.at'.st, ha⟩

end

end VG.Proof.MlDsa.PPC64LE.Sample.RejBounded
