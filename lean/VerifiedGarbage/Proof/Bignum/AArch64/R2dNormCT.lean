module

public import VerifiedGarbage.Proof.Bignum.AArch64.R2dPubCT
public import VerifiedGarbage.Proof.Bignum.AArch64.R2dNorm
import VerifiedGarbage.Proof.Bignum.AArch64.R2dCT
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.WordStepNorm
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dPubCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dNorm
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
meta import VerifiedGarbage.Proof.Bignum.WordStepNorm
meta import VerifiedGarbage.Proof.Bignum.Words
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Bignum.AArch64.Run
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# `R² mod m` by long division for any top word of a public `m` on AArch64 leaks only `m`

`fastN`'s steps branch on the sign of `t = x 2^64 - q̂ m` (`addBackPub`), as
`fastPub`'s do (`R2dPubCT.lean`), where `q̂` is a function of `m`, `x` and
the normalization's shift `z`, which `m` fixes (`WordStep.norm_unique`). The
relations fix `m`, `x` and `z` (`R2nS`, `R2nSs`); the rest, which the taint
analysis checks, branches on and addresses by the working space's layout
alone (`r2nFast_ct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.R2Div
open VG.Impl.Rsa.AArch64
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-! ## `quotN` -/

/-- `quotN` runs, changing no memory. -/
theorem quotN_runs {t : State} {B : Addr} {Z w : Nat} (hs : Scr t B Z)
    (h11 : t.gpr .x11 = off B (slot w aR2)) (h12 : t.gpr .x12 = BitVec.ofNat 64 w)
    (h6 : t.gpr .x6 = off B (slot w aTmp)) (hw : 3 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 8 ≤ Z) :
    WP isa (.block quotN) t fun t' =>
      t'.mem = t.mem ∧ Keep [.x1, .x2, .x3, .x4, .x5, .x13, .x14, .x15, .x16, .x17] t t' := by
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have lX := sl aR2 (by decide)
  have lT := sl aTmp (by decide)
  have e2 : slot w aR2 + 8 * (w - 3) + 16 = slot w aR2 + 8 * (w - 1) := by omega_arith
  have e1 : slot w aR2 + 8 * (w - 3) + 8 = slot w aR2 + 8 * (w - 2) := by omega_arith
  refine WP.keep [.x1, .x2, .x3, .x4, .x5, .x13, .x14, .x15, .x16, .x17] (Q := fun t' => t'.mem = t.mem) ?_
    (by decide) (by decide) (by decide +kernel)
  brun [h11, h12, h6, r2d_exec_tst, r2d_exec_cselc, CondCode.holds, shl3_sub24 hw (show w < 2 ^ 61 by omega_arith),
    off_add, e2, e1, hs.ld (show slot w aR2 + 8 * (w - 1) + 8 ≤ Z by omega_arith),
    hs.ld (show slot w aR2 + 8 * (w - 2) + 8 ≤ Z by omega_arith), hs.ld (show slot w aR2 + 8 * (w - 3) + 8 ≤ Z by omega_arith),
    hs.ld (show slot w aTmp + 8 + 8 ≤ Z by omega_arith), hs.ld (show slot w aTmp + 16 + 8 ≤ Z by omega_arith),
    hs.ld (show slot w aTmp + 8 ≤ Z by omega_arith), quotN, quotHeadN, quotMG]

/-- The working space with `w ≥ 3`. -/
def R2nG (L : Ws) (s : State) : Prop := R2dGoodS L s ∧ 3 ≤ L.w

/-- After `bases`, with `w ≥ 3`. -/
def R2nR (L : Ws) (s : State) : Prop := R2dStepR L s ∧ 3 ≤ L.w

theorem pins_r2nR : Pins R2nR [.x8, .x9, .x11, .x6, .x12, .x7] :=
  fun L s₁ s₂ h₁ h₂ => pins_r2dStepR L s₁ s₂ h₁.1 h₂.1

theorem r2nBases_ok {L : Ws} {t : State} (h : R2nG L t) : WP isa (.block R2Div.bases) t (R2nR L) :=
  WP.mono (r2dBases_ok h.1) fun _ h' => ⟨h', h.2⟩

theorem quotN_stepR {L : Ws} {t : State} (h : R2nR L t) : WP isa (.block quotN) t (R2dStepR L) := by
  obtain ⟨⟨⟨mi, hg, hw, hw'⟩, hr⟩, hw3⟩ := h
  exact WP.mono (quotN_runs hg.1.scr hr.x11 hr.x12 hr.x6 hw3 hw' hg.2) fun t' ⟨hm, k⟩ =>
    ⟨⟨mi, ⟨hg.1.keep hm k (by decide), hg.2⟩, hw, hw'⟩, hr.keep k⟩

/-! ## A step -/

/-- What a step's branches depend on: `m`, `x` and the shift `z`. -/
structure R2nS where
  L : Ws
  M : Nat
  X : Nat
  z : Nat

/-- `d' = ⌊m 2^z / 2^(64 (w - 1))⌋`. -/
def R2nS.d (p : R2nS) : Nat := p.M * 2 ^ p.z / 2 ^ (64 * (p.L.w - 1))

/-- `q̂` of `x`, `m` and `z`. -/
def R2nS.q (p : R2nS) : Nat := min (p.X * 2 ^ p.z / 2 ^ (64 * (p.L.w - 2)) / p.d) (2 ^ 64 - 1)

/-- `stepN`'s precondition (`r2dStepN_ok`'s), with `m`, `x` and `z`. -/
def R2nSPre (p : R2nS) (s : State) : Prop :=
  R2nG p.L s ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.M ∧ p.z ≤ 63 ∧
    (word s.mem p.L.B (slot p.L.w aTmp + 8)).toNat = 2 ^ p.z ∧
    (word s.mem p.L.B (slot p.L.w aTmp + 16)).toNat = p.d ∧ 2 ^ 63 ≤ p.d ∧
    (word s.mem p.L.B (slot p.L.w aTmp)).toNat = (2 ^ 128 - 1) / p.d - 2 ^ 64 ∧
    wv s.mem p.L.B (slot p.L.w aR2) p.L.w = p.X ∧ p.X < p.M

/-- After a step's first pieces: `t = 2^64 x - q̂ m` with a borrow. -/
def R2nSMid (p : R2nS) (s : State) : Prop :=
  R2dGoodS p.L s ∧ StepRegs s p.L.B p.L.w ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.M ∧
    ∃ b : Bool, wv s.mem p.L.B (slot p.L.w aAcc) (p.L.w + 1) + p.q * p.M =
      2 ^ 64 * p.X + 2 ^ (64 * (p.L.w + 1)) * b.toNat

theorem r2nSPre_mid {p : R2nS} {s : State} (h : R2nSPre p s) :
    WP isa (seqs [.block (R2Div.bases ++ quotN), zeroAcc, mulAddRow, subPass]) s (R2nSMid p) := by
  obtain ⟨⟨⟨mi, ⟨hg, hZ⟩, hw, hw'⟩, hw3⟩, hN, hz, hP, hD, hd, hv, hX, hXM⟩ := h
  have hXd : wv s.mem p.L.B (slot p.L.w aR2) p.L.w * 2 ^ p.z / 2 ^ (64 * (p.L.w - 1)) ≤ p.d := by
    rw [hX]; exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_of_lt hXM))
  refine WP.mono (r2dStepPreN_ok hg hZ hw3 hw' hN hP hz hD hd hv hXd)
    fun t ⟨g, r, hN', ⟨b, hb⟩, _, _⟩ => ⟨⟨mi, ⟨g, hZ⟩, hw, hw'⟩, r, hN', b, ?_⟩
  have hq : r2dQN s.mem p.L.B p.L.w p.z p.d = p.q := by unfold r2dQN R2nS.q; rw [hX]
  rw [hq, hX] at hb; exact hb

/-- Runs with the same `m`, `x` and `z` leave the same `t`. -/
theorem r2nSMid_bind (p : R2nS) (s₁ s₂ : State) (h₁ : R2nSMid p s₁) (h₂ : R2nSMid p s₂) :
    ∃ q, R2pABPre q s₁ ∧ R2pABPre q s₂ := by
  obtain ⟨g₁, r₁, n₁, b₁, e₁⟩ := h₁
  obtain ⟨g₂, r₂, n₂, b₂, e₂⟩ := h₂
  refine ⟨⟨p.L, p.M, wv s₁.mem p.L.B (slot p.L.w aAcc) (p.L.w + 1)⟩, ⟨g₁, r₁, n₁, rfl⟩, ⟨g₂, r₂, n₂, ?_⟩⟩
  show wv s₂.mem p.L.B (slot p.L.w aAcc) (p.L.w + 1) = wv s₁.mem p.L.B (slot p.L.w aAcc) (p.L.w + 1)
  have l₁ := wv_lt s₁.mem p.L.B (slot p.L.w aAcc) (p.L.w + 1)
  have l₂ := wv_lt s₂.mem p.L.B (slot p.L.w aAcc) (p.L.w + 1)
  generalize 2 ^ (64 * (p.L.w + 1)) = W at *
  generalize p.q * p.M = Q at *
  generalize 2 ^ 64 * p.X = X at *
  cases b₁ <;> cases b₂ <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one] at e₁ e₂ <;>
    omega_arith

/-- A step's first pieces leak the same, and leave the same `t`, in runs with
the same `m`, `x` and `z`. -/
theorem r2nStepPre_ct :
    RelCT isa (Two R2nSPre) (seqs [.block (R2Div.bases ++ quotN), zeroAcc, mulAddRow, subPass]) (Two R2pABPre) := by
  have hct : RelCT isa (Two R2nSPre) (seqs [.block (R2Div.bases ++ quotN), zeroAcc, mulAddRow, subPass])
      fun _ _ => True := by
    refine two_map (fun (p : R2nS) => p.L) (fun _ _ h => h.1) ?_
    show RelCT isa (Two R2nG) (.seq (.block (R2Div.bases ++ quotN)) (.seq zeroAcc (.seq mulAddRow subPass))) _
    refine RelCT.seq (RelCT.block_append (RelCT.seq
      (two_piece (Ψ := R2nR) [.x0] (pins_r2dGood id fun _ _ h => h.1) (by taint_decide)
        fun _ _ h => r2nBases_ok h)
      (two_piece (Ψ := R2dStepR) _ pins_r2nR (by taint_decide) fun _ _ h => quotN_stepR h)))
      (two_taint _ pins_r2dStepR (by taint_decide))
  exact (two_post hct fun _ _ h => r2nSPre_mid h).mono (fun _ _ h => h) fun _ _ h => two_bind r2nSMid_bind h

theorem r2nStep_eq : stepN = seqs (([.block (R2Div.bases ++ quotN), zeroAcc, mulAddRow, subPass] : List (Prog isa)) ++
    ([addBackPub, addBackPub, copyBack] : List (Prog isa))) := rfl

/-- `stepN` leaks the same in runs with the same `m`, `x` and `z`. -/
theorem r2nStep_ct : RelCT isa (Two R2nSPre) stepN fun _ _ => True := by
  rw [r2nStep_eq]
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq r2nStepPre_ct ?_)
  show RelCT isa (Two R2pABPre) (.seq addBackPub (.seq addBackPub copyBack)) _
  refine RelCT.seq r2pAddBack_ct (RelCT.seq (r2pAddBack_ct.mono (fun _ _ h => r2p_two_next h) fun _ _ h => r2p_two_next h) ?_)
  exact two_taint _ (pins_r2pABPre.r2pOf fun _ _ h => h) (by taint_decide)

/-! ## The steps -/

/-- What the steps' branches depend on: `m`, the first `x` and `z`. -/
structure R2nSs where
  L : Ws
  M : Nat
  X0 : Nat
  z : Nat

/-- `stepsN`'s precondition (`r2dStepsN_ok`'s, `w + 1` steps), with `m`, the
first `x` and `z`. -/
def R2nSsPre (p : R2nSs) (s : State) : Prop :=
  R2nG p.L s ∧ p.L.w < 2 ^ 30 ∧ s.gpr .x13 = BitVec.ofNat 64 (p.L.w + 1) ∧
    R2nSPre ⟨p.L, p.M, p.X0, p.z⟩ s

/-- After `j` of the `w + 1` steps. -/
def R2nSsAt (p : R2nSs) (j : Nat) (t : State) : Prop :=
  ∃ (σ : State) (mi : BitVec 64), R2dStepsInvN σ p.L.B p.L.Z p.L.w mi p.M p.z p.X0 (p.L.w + 1) j t ∧
    slot p.L.w 8 ≤ p.L.Z ∧ 3 ≤ p.L.w ∧ p.L.w < 2 ^ 30 ∧ p.z ≤ 63 ∧
    2 ^ 63 ≤ p.M * 2 ^ p.z / 2 ^ (64 * (p.L.w - 1)) ∧ 0 < p.M

/-- The step after `j` steps, with its `x`. -/
theorem r2nSsAt_sPre {p : R2nSs} {j : Nat} {t : State} (h : R2nSsAt p j t) :
    R2nSPre ⟨p.L, p.M, p.X0 * 2 ^ (64 * j) % p.M, p.z⟩ t := by
  obtain ⟨_, mi, hI, hZ, hw, hw', hz, hd, hM0⟩ := h
  exact ⟨⟨⟨mi, ⟨hI.g, hZ⟩, by show 2 ≤ p.L.w; omega_arith, by show p.L.w < 2 ^ 31; omega_arith⟩, hw⟩, hI.n, hz, hI.p, hI.d, hd, hI.v, hI.x,
    Nat.mod_lt _ hM0⟩

theorem r2nSteps_eq : stepsN =
    .seq (.block [sth .x13 sCnt]) (.loop (.seq stepN (.block (dblCount sCnt))) (.nonzero .x .x13)) := rfl

/-- `stepsN` leaks the same in runs with the same `m`, first `x` and `z`. -/
theorem r2nSteps_ct : RelCT isa (Two R2nSsPre) stepsN fun _ _ => True := by
  rw [r2nSteps_eq]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < p.L.w + 1 ∧ R2nSsAt p 0 s) [.x0]
    (pins_r2dGood (fun (p : R2nSs) => p.L) fun _ _ h => h.1.1) (by taint_decide) ?_) ?_
  · rintro p s ⟨⟨⟨mi, hg, hw, hw'⟩, hw3⟩, hw30, h13, -, hN, hz, hP, hD, hd, hv, hX, hXM⟩
    refine WP.mono (r2dStepsStartN_ok hg.1 hg.2 (by omega_arith) h13 hN hP hD hv (by rw [hX]; exact hXM)) fun t hI =>
      ⟨by omega_arith, s, mi, ?_, hg.2, hw3, hw30, hz, hd, Nat.lt_of_le_of_lt (Nat.zero_le _) hXM⟩
    rw [hX] at hI; exact hI
  refine (two_loop (Φ := R2nSsAt) (Ψ := fun _ _ => True) (fun p => p.L.w + 1) ?_ ?_).mono (fun _ _ h => h)
    fun _ _ _ => trivial
  · refine RelCT.seq (two_post (Ψ := fun (q : R2nSs × Nat) s => R2dGoodS q.1.L s)
      (two_map (fun q => (⟨q.1.L, q.1.M, q.1.X0 * 2 ^ (64 * q.2) % q.1.M, q.1.z⟩ : R2nS))
        (fun _ _ h => r2nSsAt_sPre h.2) r2nStep_ct) ?_)
      (two_taint _ (pins_r2dGood (·.1.L) fun _ _ h => h) (by taint_decide))
    rintro ⟨p, j⟩ s ⟨hj, σ, mi, hI, hZ, hw, hw', hz, hd, hM0⟩
    exact WP.mono (r2dStepN_ok hI.g hZ hw (by omega_arith) hI.n hI.p hz hI.d hd hI.v
      (by rw [hI.x]; exact Nat.mod_lt _ hM0)) fun t ⟨g, _, _, _⟩ => ⟨mi, ⟨g, hZ⟩, by omega_arith, by omega_arith⟩
  · rintro p j s hj ⟨σ, mi, hI, hZ, hw, hw', hz, hd, hM0⟩
    exact WP.mono (stepsIterN_ok hZ hw (by omega_arith) hz hd hM0 (by omega_arith) hj hI)
      fun t ⟨hI', hz'⟩ => ⟨eval_count hj hz', fun _ => ⟨σ, mi, hI', hZ, hw, hw', hz, hd, hM0⟩, fun _ => trivial⟩

/-! ## `fastN` -/

/-- `fastN`'s precondition (`r2dFastN_ok`'s), with `m`. -/
def R2nFPre (q : Ws × Nat) (s : State) : Prop :=
  R2nG q.1 s ∧ q.1.w < 2 ^ 30 ∧ wv s.mem q.1.B (slot q.1.w aN) q.1.w = q.2 ∧ q.2 % 2 = 1 ∧
    2 ^ (64 * (q.1.w - 1)) ≤ q.2

/-- After `fastN`'s loads. -/
def R2nF0 (q : Ws × Nat) (s : State) : Prop :=
  R2nFPre q s ∧ s.gpr .x11 = off q.1.B (slot q.1.w aR2) ∧ s.gpr .x9 = off q.1.B (slot q.1.w aN) ∧
    s.gpr .x6 = off q.1.B (slot q.1.w aTmp) ∧ s.gpr .x12 = BitVec.ofNat 64 q.1.w ∧ s.gpr .x7 = 0

theorem pins_R2nF0 : Pins R2nF0 [.x0, .x11, .x9, .x6, .x12, .x7] := by
  intro q s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pins_r2dGood (fun (q : Ws × Nat) => q.1) (fun _ _ h => h.1.1.1) q s₁ s₂ h₁ h₂ .x0 (by simp)
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2.1, h₂.2.2.2.1]
  · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  · rw [h₁.2.2.2.2.2, h₂.2.2.2.2.2]

theorem r2nLoads_ok {q : Ws × Nat} {s : State} (h : R2nFPre q s) :
    WP isa (.block [ldh .x11 (sArr aR2), ldh .x9 (sArr aN), ldh .x6 (sArr aTmp), ldh .x12 sW, movi .x7 0]) s
      (R2nF0 q) := by
  obtain ⟨⟨⟨mi, hg, hw, hw'⟩, hw3⟩, hw30, hN, hodd, hlo⟩ := h
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off q.1.B (8 * i)) 8 := fun i hi =>
    hg.1.scr.ld (by have := hdr_lt_slot q.1.w 8 hi; have := hg.2; omega_arith)
  refine WP.mono (WP.keep [.x6, .x7, .x9, .x11, .x12] (Q := fun t => (t.gpr .x11 = off q.1.B (slot q.1.w aR2) ∧
      t.gpr .x9 = off q.1.B (slot q.1.w aN) ∧ t.gpr .x6 = off q.1.B (slot q.1.w aTmp) ∧
      t.gpr .x12 = BitVec.ofNat 64 q.1.w ∧ t.gpr .x7 = 0) ∧ t.mem = s.mem)
    (by brun [hg.1.x0, hdr_enc (show sArr aN < 32 by decide), hdr_enc (show sArr aR2 < 32 by decide),
        hdr_enc (show sArr aTmp < 32 by decide), hdr_enc (show sW < 32 by decide), hl (sArr aN) (by decide),
        hl (sArr aR2) (by decide), hl (sArr aTmp) (by decide), hl sW (by decide), hg.1.hdr.harr aN (by decide),
        hg.1.hdr.harr aR2 (by decide), hg.1.hdr.harr aTmp (by decide), hg.1.hdr.hw])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨r, hm⟩, k⟩ => ⟨?_, r⟩
  exact ⟨⟨⟨mi, ⟨hg.1.keep hm k (by decide), hg.2⟩, hw, hw'⟩, hw3⟩, hw30, by rw [hm]; exact hN, hodd, hlo⟩

/-- `fastN`'s pieces before its steps. -/
def fastNHead : Prog isa := seqs [
  .block [ldh .x11 (sArr aR2), ldh .x9 (sArr aN), ldh .x6 (sArr aTmp), ldh .x12 sW, movi .x7 0],
  normN, recipN, setTop, .block [.addImm .x .x13 .x12 1]]

/-- `fastN`'s pieces before its steps leak the same, and leave the same `z`, in
runs with the same `m`. -/
theorem r2nHead_ct : RelCT isa (Two R2nFPre) fastNHead (Two R2nSsPre) := by
  have hct : RelCT isa (Two R2nFPre) fastNHead fun _ _ => True := by
    show RelCT isa (Two R2nFPre) (.seq (.block [ldh .x11 (sArr aR2), ldh .x9 (sArr aN), ldh .x6 (sArr aTmp),
      ldh .x12 sW, movi .x7 0]) (.seq normN (.seq recipN (.seq setTop (.block [.addImm .x .x13 .x12 1]))))) _
    exact RelCT.seq (two_piece (Ψ := R2nF0) [.x0] (pins_r2dGood (fun (q : Ws × Nat) => q.1) fun _ _ h => h.1.1)
      (by taint_decide) fun _ _ h => r2nLoads_ok h) (two_taint _ pins_R2nF0 (by taint_decide))
  refine (two_post (Ψ := fun (q : Ws × Nat) t => ∃ z, R2nSsPre ⟨q.1, q.2, 2 ^ (64 * (q.1.w - 1)), z⟩ t) hct ?_).mono
    (fun _ _ h => h) fun _ _ h => two_bind (fun q s₁ s₂ h₁ h₂ => ?_) h
  · rintro q s ⟨⟨⟨mi, hg, hw, hw'⟩, hw3⟩, hw30, hN, hodd, hlo⟩
    exact WP.mono (r2dFastNHead_ok hg.1 hg.2 hw3 hw30 hN hodd hlo) fun t ⟨g, h13, N, ⟨z, hz, P, D, hd, V⟩, X, hlt, _, _⟩ =>
      ⟨z, ⟨⟨mi, ⟨g, hg.2⟩, hw, hw'⟩, hw3⟩, hw30, h13, ⟨⟨⟨mi, ⟨g, hg.2⟩, hw, hw'⟩, hw3⟩, N, hz, P, D, hd, V, X, hlt⟩⟩
  · obtain ⟨z₁, h₁⟩ := h₁
    obtain ⟨z₂, h₂⟩ := h₂
    have e : z₁ = z₂ := by
      obtain ⟨-, -, -, -, -, -, -, D₁, d₁, -⟩ := h₁
      obtain ⟨-, -, -, -, -, -, -, D₂, d₂, -⟩ := h₂
      unfold R2nS.d at D₁ d₁ D₂ d₂
      exact WordStep.norm_unique d₁ (D₁ ▸ BitVec.isLt _) d₂ (D₂ ▸ BitVec.isLt _)
    subst e
    exact ⟨_, h₁, h₂⟩

theorem r2nFast_eq : fastN = seqs (([.block [ldh .x11 (sArr aR2), ldh .x9 (sArr aN), ldh .x6 (sArr aTmp),
    ldh .x12 sW, movi .x7 0], normN, recipN, setTop, .block [.addImm .x .x13 .x12 1]] : List (Prog isa)) ++
    ([stepsN] : List (Prog isa))) := rfl

/-- `fastN` leaks the same in runs with the same `m`. -/
theorem r2nFast_ct : RelCT isa (Two R2nFPre) fastN fun _ _ => True := by
  rw [r2nFast_eq]
  exact RelCT.seqs_append (by simp) (by simp) (RelCT.seq r2nHead_ct r2nSteps_ct)

/-! ## `R² mod m` -/

/-- After `choiceW`'s test: `w - 2`. -/
def R2w (p : R2Pub) (s : State) : Prop := R2Pre p s ∧ s.gpr .x13 = BitVec.ofNat 64 (p.L.w - 2)

theorem r2w_ok {p : R2Pub} {s : State} (h : R2Pre p s) :
    WP isa (.block [ldh .x12 sW, .subImm .x .x13 .x12 2]) s (R2w p) := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.L.B (8 * i)) 8 := fun i hi =>
    h.1.1.scr.ld (by have := hdr_lt_slot p.L.w 8 hi; have := h.1.2; omega_arith)
  have hw := h.2.1
  refine WP.mono (WP.keep [.x12, .x13] (Q := fun t => t.gpr .x13 = BitVec.ofNat 64 (p.L.w - 2) ∧ t.mem = s.mem)
    (by
      brun [h.1.1.x0, hdr_enc (show sW < 32 by decide), hl sW (by decide), h.1.1.hdr.hw]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega_arith)
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h13, hm⟩, k⟩ => ⟨h.keep hm k (by decide), h13⟩

/-- `choiceW` leaks the same in runs that agree on `m`: it branches on `w`. -/
theorem r2W_ct (M : Mont) :
    RelCT isa (Two R2Pre) (R2Div.choiceW (seqs (r2StepsOld M.mm)) R2Div.fastN) fun _ _ => True := by
  unfold R2Div.choiceW
  refine RelCT.seq (two_piece (Ψ := R2w) _ (pins_r2 fun _ _ h => h) (by taint_decide) fun _ _ h => r2w_ok h) ?_
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2]) ?_ ?_
  · exact (r2Old_ct M).mono (fun _ _ h => two_mono (fun _ _ h => h.1.1) h) fun _ _ h => h
  · refine two_map (fun p => (p.L.ws, p.N)) (fun p s ⟨⟨h, h13⟩, he⟩ => ?_) r2nFast_ct
    obtain ⟨hg, hw, hw30, hN, -, hodd, hlo⟩ := h
    have hw3 : 3 ≤ p.L.w := by
      rw [eval_zero, h13] at he
      by_contra hlt
      have : p.L.w - 2 = 0 := by omega_arith
      rw [this] at he
      exact absurd he (by decide)
    exact ⟨⟨⟨p.L.minv, hg, hw, by show p.L.w < 2 ^ 31; omega_arith⟩, hw3⟩, hw30, hN, hodd, hlo⟩

/-- `R² mod m` for a public `m` leaks the same in runs that agree on `m`:
`choicePub` branches on its top bit, `choiceW` on `w`, and `fastPub` and
`fastN` on values that `m` fixes. -/
theorem r2Pub_ct (M : Mont) : RelCT isa (Two R2Pre) (seqs (r2StepsPub M.mm)) fun _ _ => True := by
  show RelCT isa (Two R2Pre) (R2Div.choicePub (R2Div.choiceW (seqs (r2StepsOld M.mm)) R2Div.fastN)) _
  unfold R2Div.choicePub
  rw [fastTest_eq]
  refine RelCT.seq (RelCT.block_append (RelCT.seq
    (two_piece (Ψ := R2t) _ (pins_r2 fun _ _ h => h) (by taint_decide) fun _ _ h => r2t_ok h)
    (two_piece (Ψ := R2u) _ pins_r2t (by taint_decide) fun _ _ h => r2u_ok h))) ?_
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2]) ?_ ?_
  · exact (r2W_ct M).mono (fun _ _ h => two_mono (fun _ _ h => h.1.1) h) fun _ _ h => h
  · refine two_map (fun p => (p.L.ws, p.N)) (fun p s ⟨⟨h, h3⟩, he⟩ => ⟨h.fpre ?_, h.2.2.2.1⟩) r2pFast_ct
    rw [eval_zero, h3] at he
    by_contra hlt
    rw [decide_eq_false hlt] at he
    exact absurd he (by decide)

end VG.Proof.Bignum.AArch64
