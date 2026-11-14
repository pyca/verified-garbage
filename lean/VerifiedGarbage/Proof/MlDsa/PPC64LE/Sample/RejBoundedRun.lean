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
sponge, whose output is `H(ρ, n)` (`J6`), the branch on `η` (`sel_ok`), and
the loop for `η`, iteration `t` of which starts from `Base` with the
coefficients `rbFold` samples from the first `t` bytes of output stored
(`loop_ok`): a try (`rbTry_ok`), with 272 bytes, then, if it did not sample 256
coefficients (`jtest_ok`), with 544; then the end returns whether there are
256 (`correct`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Sample.RejBounded

open VG VG.PPC64LE
open VG.Proof.MlDsa.PPC64LE.Sample
open VG.Impl.MlDsa.PPC64LE.Sample
open VG.Impl.Sha3.PPC64LE.Stream (mov)
open VG.Proof.MlDsa.Sample (Stored stored_nil H_eq rbFold ifT ifF rbFold_length_le)
open VG.Proof.MlKem.PPC64LE (wp_loop_nz)
open VG.Spec.MlDsa (Zq H)
open VG.Spec.Sha3 (bytesAt)

/-- `J6` for `n` bytes, and `η` zero-extended in `r27`. -/
structure SJ (n : Nat) (σ s : State) : Prop where
  j6 : ∃ s₀, J6 136 n (spOf σ) σ s₀ s
  r27 : s.gpr .r27 = zx (σ.gpr .r4)

section
variable {σ : State} (hp : SpOk (spOf σ) σ)
include hp

/-- The loop's setup, after the sponge. -/
theorem init_ok {n : Nat} (hn : n ≤ 544) {s : State} (h : SJ n σ s) :
    WP isa (.block (([.addi .r3 .r31 840, mov .r4 .r30, .li .r5 0, .li .r6 n] : List Instr) ++ loadQ)) s
      (Base σ (X n σ) 0 []) := by
  obtain ⟨⟨s₀, h⟩, e27⟩ := h
  have g30 := h.j0.env.r30
  have g31 := h.j0.env.r31
  have hn' : n < 32768 := by omega_using [hn]
  have hk : WP isa (.block (([.addi .r3 .r31 840, mov .r4 .r30, .li .r5 0, .li .r6 n] : List Instr) ++ loadQ)) s
      fun s' => s'.gpr .r3 = σ.gpr .r6 + BitVec.ofNat 64 (840 + 0) ∧ s'.gpr .r4 = σ.gpr .r5 ∧
        s'.gpr .r5 = BitVec.ofNat 64 0 ∧ s'.gpr .r6 = BitVec.ofNat 64 n ∧
        s'.gpr .r7 = BitVec.ofNat 64 8380417 ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    prun [loadQ, List.cons_append, List.nil_append, exec_lis, exec_ori, loadQ_val, g30, g31, hn']
    simp only [true_and, and_true]
    pres_tac
  refine WP.mono hk fun s' ⟨g3, g4, g5, g6, g7, gp, m, rd, wr, sp⟩ => ⟨h.j0.env.regs hp m gp rd wr sp,
    by rw [X_length]; exact hn, by rw [m, X_length, h.out]; exact (H_eq _ _).symm, g3, by rw [X_length, Nat.sub_zero]; exact g6, g7,
    (gp _ (by decide)).trans e27, (gp _ (by decide)).trans h.j0.r28, (gp _ (by decide)).trans h.j0.r29, ?_⟩
  exact ⟨by rw [g4]; exact (BitVec.add_zero _).symm, g5, by simp, stored_nil _ _⟩

/-- The loop for `η`, over `n` bytes: it stops after the last byte or once
there are 256 coefficients, which are then those of all `n` bytes. -/
theorem loop_ok {η : Nat} (hη : η = 2 ∨ η = 4) {n : Nat} (hn0 : 0 < n) (hn : n ≤ 544) {s : State}
    (h : SJ n σ s) : WP isa (rbLoop η n) s fun s' => ∃ t, Base σ (X n σ) t (Lf η (X n σ) n) s' := by
  refine WP.seq (WP.mono (init_ok hp hn h) fun s0 h0 => ?_)
  refine WP.loop (M := isa) (c := .nonzero .d .r12) (fun m s => ∃ i, i < n ∧ m = n - i ∧
    Base σ (X n σ) i (Lf η (X n σ) i) s ∧ (Lf η (X n σ) i).length < 256) ?_ n s0
    ⟨0, hn0, rfl, by simpa [Lf, rbFold] using h0, by simp [Lf, rbFold]⟩
  rintro m s ⟨i, hi, rfl, hs, -⟩
  refine WP.mono (body_ok hp hη (X := X n σ) (by rw [X_length]; exact hi) hs) fun s' ⟨hs', hz⟩ => ?_
  rw [X_length] at hz
  have ev : isa.eval (.nonzero .d .r12) s' =
      some (decide (i + 1 ≠ n ∧ (Lf η (X n σ) (i + 1)).length < 256)) := by rw [eval_nonzero, hz]
  by_cases hc : i + 1 ≠ n ∧ (Lf η (X n σ) (i + 1)).length < 256
  · exact .inr ⟨by rw [ev, decide_eq_true hc], n - (i + 1), by omega_using [hi], i + 1, by omega_using [hi, hc], rfl, hs', hc.2⟩
  · refine .inl ⟨by rw [ev, decide_eq_false hc], i + 1, ?_⟩
    have hle := rbFold_length_le (η := η) (a := []) (by simp) ((X n σ).take (i + 1))
    rw [Lf_stop (show i + 1 ≤ n by omega_using [hi]) (by
      by_cases e : i + 1 = n
      · exact .inl e
      · have h1 := not_and.mp hc e
        have hle' : (Lf η (X n σ) (i + 1)).length ≤ 256 := hle
        exact .inr (by omega_using [h1, hle']))]
    exact hs'

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
theorem cmp_ok {n : Nat} {s : State} (h : SJ n σ s) :
    WP isa (.block [.subi .r12 .r27 2]) s fun s' => SJ n σ s' ∧ s'.gpr .r12 = zx (σ.gpr .r4) - BitVec.ofNat 64 2 := by
  obtain ⟨⟨s₀, j6⟩, e27⟩ := h
  have hk : WP isa (.block [.subi .r12 .r27 2]) s fun s' => s' = s.write .r12 (s.gpr .r27 - BitVec.ofNat 64 2) := by
    prun []
  refine WP.mono hk fun s' e' => ?_
  subst e'
  have gp : ∀ r ∈ preserved, (s.write .r12 (s.gpr .r27 - BitVec.ofNat 64 2)).gpr r = s.gpr r := by pres_tac
  exact ⟨⟨⟨s₀, j6.j0.regs hp rfl gp rfl rfl rfl, fun r hr => (gp r hr).trans (j6.gp r hr), j6.out⟩,
    (gp .r27 (by decide)).trans e27⟩, by rw [RegUpd.gpr_write_self, e27]⟩

/-- The branch on `η`, and the loop for it. -/
theorem sel_ok (hη : etaOf σ = 2 ∨ etaOf σ = 4) {n : Nat} (hn0 : 0 < n) (hn : n ≤ 544) {s : State}
    (h : SJ n σ s) :
    WP isa (.seq (.block [.subi .r12 .r27 2]) (.ite (.zero .d .r12) (rbLoop 2 n) (rbLoop 4 n))) s
      fun s' => ∃ t, Base σ (X n σ) t (Lf (etaOf σ) (X n σ) n) s' := by
  refine WP.seq (WP.mono (cmp_ok hp h) fun s1 ⟨h1, e12⟩ => ?_)
  refine WP.ite _ (by rw [eval_zero, e12, eta_test]) (fun he => ?_) (fun he => ?_)
  · simp only [decide_eq_true_eq] at he
    rw [show etaOf σ = 2 from he]
    exact loop_ok hp (.inl rfl) hn0 hn h1
  · simp only [decide_eq_false_iff_not] at he
    rw [show etaOf σ = 4 from hη.resolve_left he]
    exact loop_ok hp (.inr rfl) hn0 hn h1

/-- A try with `n` bytes, from the registers of the sponge's arguments and
`η` in `r27`. -/
theorem rbTry_ok (hη : etaOf σ = 2 ∨ etaOf σ = 4) {n : Nat} (hn0 : 0 < n) (hn : n ≤ 544) {s : State}
    (j0 : J0 (spOf σ) σ s) (e27 : s.gpr .r27 = zx (σ.gpr .r4)) :
    WP isa (rbTry n) s fun s' => ∃ t, Base σ (X n σ) t (Lf (etaOf σ) (X n σ) n) s' :=
  WP.seq (WP.mono (sponge_ok hp (rate := 136) (outlen := n) (by decide) (by omega_using [hn]) j0) fun _ h =>
    sel_ok hp hη hn0 hn ⟨⟨s, h⟩, (h.gp .r27 (by decide)).trans e27⟩)

/-- The test of `j = 256`. -/
theorem jtest_ok {X : List Byte} {t : Nat} {L : List Zq} {s : State} (h : Base σ X t L s) :
    WP isa (.block [.subi .r12 .r5 256]) s fun s' => Base σ X t L s' ∧
      isa.eval (.zero .d .r12) s' = some (decide (L.length = 256)) := by
  have hk : WP isa (.block [.subi .r12 .r5 256]) s fun s' => s' = s.write .r12 (s.gpr .r5 - BitVec.ofNat 64 256) := by
    prun []
  refine WP.mono hk fun s' e' => ?_
  subst e'
  refine ⟨h.keep hp rfl (fun r _ _ _ _ a => RegUpd.gpr_write_of_ne _ _ a) rfl rfl rfl, ?_⟩
  rw [eval_zero, RegUpd.gpr_write_self, h.at'.r5]
  have hl := h.at'.len
  by_cases e : L.length = 256
  · rw [e]; rfl
  · rw [decide_eq_false e]
    exact congrArg some (beq_eq_false_iff_ne.mpr (by bv_omega))

/-- The coefficients the function samples: those of the first 272 bytes if
there are 256 of them, and those of 544 bytes otherwise. -/
abbrev Lr (η : Nat) (σ : State) : List Zq :=
  if (Lf η (X 272 σ) 272).length = 256 then Lf η (X 272 σ) 272 else Lf η (X 544 σ) 544

/-- The whole function: `r3` whether 256 coefficients were sampled, those
stored, and the calling convention. -/
theorem correct (hη : etaOf σ = 2 ∨ etaOf σ = 4) :
    WP isa rejBounded σ fun s' =>
      s'.gpr .r3 = (if (Lr (etaOf σ) σ).length = 256 then 1 else 0) ∧
      Stored s'.mem (σ.gpr .r5) (Lr (etaOf σ) σ) ∧ abiPreserved σ s' := by
  unfold rejBounded
  refine WP.seq (WP.mono (pro_rb hp rfl rfl rfl rfl) fun s₀ ⟨j0, e27⟩ => ?_)
  refine WP.seq (WP.mono (rbTry_ok hp hη (n := 272) (by decide) (by decide) j0 e27) fun s1 ⟨t1, h1⟩ => ?_)
  have fin : ∀ {X t s}, Base σ X t (Lr (etaOf σ) σ) s →
      WP isa (.block (retJ ++ epi)) s fun s' =>
        s'.gpr .r3 = (if (Lr (etaOf σ) σ).length = 256 then 1 else 0) ∧
        Stored s'.mem (σ.gpr .r5) (Lr (etaOf σ) σ) ∧ abiPreserved σ s' := fun h3 =>
    WP.mono (retEpi_ok hp h3.env h3.at'.r5 h3.at'.len) fun s' ⟨r3, hm, ha⟩ =>
      ⟨r3, by rw [hm]; exact h3.at'.st, ha⟩
  refine WP.seq (WP.seq (WP.mono (jtest_ok hp h1) fun s2 ⟨h2, ev⟩ =>
    WP.ite _ ev (fun he => ?_) (fun he => ?_)))
  · simp only [decide_eq_true_eq] at he
    refine WP.block_nil (fin (X := X 272 σ) (t := t1) ?_)
    rw [Lr, ifT he]; exact h2
  · simp only [decide_eq_false_iff_not] at he
    exact WP.mono (rbTry_ok hp hη (n := 544) (by decide) (by decide) ⟨h2.env, h2.r29, h2.r28⟩ h2.r27)
      fun s3 ⟨_, h3⟩ => fin (by rw [Lr, ifF he]; exact h3)

end

end VG.Proof.MlDsa.PPC64LE.Sample.RejBounded
