module

public import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecipNCT
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecipNCT
meta import VerifiedGarbage.Proof.Bignum.Words
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# `R² mod m` for a public `m` on AArch64 leaks only `m`

`r2StepsPub`'s steps branch on the sign of `t = x 2^64 - q̂ m` (`addBackPub`),
which is a function of `m` and `x`, and `x` is a function of `m` and the
step's index: in runs that agree on `m`, every branch agrees.

The relations fix the values the branches depend on: a step's (`R2pS`), `m`
and `x`; `addBackPub`'s (`R2pAB`), `m` and `t`. A step's first pieces, which
the taint analysis checks, leave `t` with `t + q̂ m = 2^64 x + 2^(64 (w + 1)) b`
for a borrow `b`, and `t < 2^(64 (w + 1))`, so the same `t` in both runs
(`r2pStepPre_ct`); `addBackPub` branches on its sign and leaves
`(t + m) mod 2^(64 (w + 1))` or `t` (`r2pAddBack_ct`). The steps fix `m` and the
first `x`, `R - m` (`r2pSteps_ct`), and `r2Pub_ct` is `r2_ct` with them.
`fastPub`'s reciprocal, `recipN`, branches on `m`'s top word
(`recipN_ct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.R2Div
open VG.Impl.Rsa.AArch64
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- `Pins` for a stronger relation. -/
theorem Pins.r2pOf {α : Type} {Φ Φ' : α → State → Prop} {rs : List Reg} (hp : Pins Φ rs)
    (h : ∀ a s, Φ' a s → Φ a s) : Pins Φ' rs :=
  fun a _ _ h₁ h₂ r hr => hp a _ _ (h a _ h₁) (h a _ h₂) r hr

/-- A number below `2^n` with the same remainder and a carry out of it. -/
theorem r2p_lt_carry_mod {x y W c : Nat} (h : x + W * c = y) (hx : x < W) : x = y % W := by
  rw [← h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

/-! ## `addBackPub` -/

/-- What `addBackPub`'s branch depends on: `m` and `t`. -/
structure R2pAB where
  L : Ws
  M : Nat
  T : Nat

/-- The sign of `t`, from its top word. -/
def R2pAB.sgn (p : R2pAB) : Bool := decide (2 ^ 63 ≤ p.T / 2 ^ (64 * p.L.w) % 2 ^ 64)

/-- `t` after `addBackPub`. -/
def R2pAB.next (p : R2pAB) : R2pAB :=
  ⟨p.L, p.M, (p.T + if 2 ^ (64 * (p.L.w + 1)) / 2 ≤ p.T then p.M else 0) % 2 ^ (64 * (p.L.w + 1))⟩

/-- A step's registers, `m` and `t`. -/
def R2pABPre (p : R2pAB) (s : State) : Prop :=
  R2dGoodS p.L s ∧ StepRegs s p.L.B p.L.w ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.M ∧
    wv s.mem p.L.B (slot p.L.w aAcc) (p.L.w + 1) = p.T

theorem pins_r2pABPre : Pins R2pABPre [.x0, .x8, .x9, .x11, .x6, .x12, .x7] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pins_r2dGood (fun (p : R2pAB) => p.L) (fun _ _ h => h.1) p s₁ s₂ h₁ h₂ .x0 (by simp)
  · rw [h₁.2.1.x8, h₂.2.1.x8]
  · rw [h₁.2.1.x9, h₂.2.1.x9]
  · rw [h₁.2.1.x11, h₂.2.1.x11]
  · rw [h₁.2.1.x6, h₂.2.1.x6]
  · rw [h₁.2.1.x12, h₂.2.1.x12]
  · rw [h₁.2.1.x7, h₂.2.1.x7]

/-- `R2pABPre` with `x3` the sign of `t`. -/
def R2pABSgn (p : R2pAB) (s : State) : Prop := R2pABPre p s ∧ s.gpr .x3 = BitVec.ofNat 64 p.sgn.toNat

/-- `t`'s sign is its top word's top bit. -/
theorem r2pABPre_sign {p : R2pAB} {s : State} (h : R2pABPre p s) :
    decide (2 ^ 63 ≤ (word s.mem p.L.B (slot p.L.w aAcc + 8 * p.L.w)).toNat) = p.sgn := by
  rw [R2pAB.sgn, word_of_wv s.mem p.L.B (slot p.L.w aAcc) (p.L.w + 1) (Nat.lt_succ_self _), h.2.2.2]

theorem r2pSign_ok {p : R2pAB} {s : State} (h : R2pABPre p s) : WP isa (.block signTest) s (R2pABSgn p) := by
  obtain ⟨⟨mi, ⟨hg, hZ⟩, hw, hw'⟩, r, hN, hT⟩ := h
  have lA := Nat.le_trans (slot_le (w := p.L.w) (show aAcc < 8 by decide)) hZ
  refine WP.mono (signTest_ok hg.scr r.x8 r.x12 hw' (by omega)) fun t ⟨⟨h3, hm⟩, k⟩ => ?_
  refine ⟨⟨⟨mi, ⟨hg.keep hm k (by decide), hZ⟩, hw, hw'⟩, r.keep k, by rw [hm]; exact hN, by rw [hm]; exact hT⟩, ?_⟩
  rw [h3, r2pABPre_sign ⟨⟨mi, ⟨hg, hZ⟩, hw, hw'⟩, r, hN, hT⟩]

/-- `t`'s sign is whether `t ≥ 2^(64 (w + 1)) / 2`. -/
theorem r2pABPre_sgn_iff {p : R2pAB} {s : State} (h : R2pABPre p s) :
    p.sgn = true ↔ 2 ^ (64 * (p.L.w + 1)) / 2 ≤ p.T := by
  rw [← r2pABPre_sign h, sign_top, h.2.2.2, decide_eq_true_iff]

/-- `addBackPub` leaks only `t`'s sign, which `t` fixes, and leaves `t` as
`R2pAB.next` says. -/
theorem r2pAddBack_ct : RelCT isa (Two R2pABPre) addBackPub (Two fun (p : R2pAB) => R2pABPre p.next) := by
  unfold addBackPub
  refine RelCT.seq (two_piece (Ψ := R2pABSgn) _ pins_r2pABPre (by taint_decide) fun _ _ h => r2pSign_ok h) ?_
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2]) ?_ ?_
  · -- The sign clear: `t` stays.
    refine two_post (two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)) ?_
    rintro p s ⟨⟨h, h3⟩, he⟩
    refine WP.block_nil ?_
    have hs : p.sgn = false := by
      rw [eval_zero, h3] at he
      cases hb : p.sgn
      · rfl
      · rw [hb] at he; exact absurd he (by decide)
    have hlt := wv_lt s.mem p.L.B (slot p.L.w aAcc) (p.L.w + 1)
    rw [h.2.2.2] at hlt
    have hn : ¬ 2 ^ (64 * (p.L.w + 1)) / 2 ≤ p.T := fun hc => by
      rw [← r2pABPre_sgn_iff h, hs] at hc; exact absurd hc (by decide)
    obtain ⟨g, r, hN, hT⟩ := h
    refine ⟨g, r, hN, ?_⟩
    simp only [R2pAB.next, hn, ↓reduceIte, Nat.add_zero]
    rw [hT, Nat.mod_eq_of_lt hlt]
  · -- The sign set: `m` added.
    refine two_post (two_taint _ (pins_r2pABPre.r2pOf fun _ _ h => h.1.1) (by taint_decide)) ?_
    rintro p s ⟨⟨h, -⟩, -⟩
    obtain ⟨⟨mi, ⟨hg, hZ⟩, hw, hw'⟩, r, hN, hT⟩ := h
    have hn := hg.scr.nowrap
    have sl : ∀ j < 8, slot p.L.w j + 8 * (p.L.w + 2) ≤ p.L.Z := fun j hj => Nat.le_trans (slot_le hj) hZ
    have lA := sl aAcc (by decide)
    have lM := sl aN (by decide)
    have sAM := slot_sep (w := p.L.w) (show aAcc ≠ aN by decide)
    refine WP.mono (addBack_spec hg.scr r.x8 r.x9 r.x12 r.x7 (by omega) hw' (by omega) (by omega) (by omega))
      fun t ⟨c, hv, o, k⟩ => ?_
    have ha : Arrays p.L.B p.L.w [aAcc] s.mem t.mem :=
      Arrays.of_outside (List.mem_singleton_self _) o (Nat.le_refl _) (by omega)
    refine ⟨⟨mi, ⟨⟨hg.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hg.x0, ha.hdr hg.hdr⟩, hZ⟩, hw, hw'⟩,
      r.keep k, by show wv t.mem p.L.B (slot p.L.w aN) p.L.w = p.M; rw [o.wv (by omega) (by omega)]; exact hN, ?_⟩
    rw [hT, hN] at hv
    exact r2p_lt_carry_mod hv (wv_lt _ _ _ _)

/-- Runs related after `addBackPub` are related by `R2pABPre`. -/
theorem r2p_two_next {s₁ s₂ : State} (h : Two (fun (p : R2pAB) => R2pABPre p.next) s₁ s₂) : Two R2pABPre s₁ s₂ :=
  two_bind (fun p _ _ h₁ h₂ => ⟨p.next, h₁, h₂⟩) h

/-! ## A step -/

/-- What a step's branches depend on: `m` and `x`. -/
structure R2pS where
  L : Ws
  M : Nat
  X : Nat

/-- `q̂` of `x` and `m`'s top words. -/
def R2pS.q (p : R2pS) : Nat :=
  min ((p.X / 2 ^ (64 * (p.L.w - 1)) % 2 ^ 64 * 2 ^ 64 + p.X / 2 ^ (64 * (p.L.w - 2)) % 2 ^ 64) /
    (p.M / 2 ^ (64 * (p.L.w - 1)) % 2 ^ 64)) (2 ^ 64 - 1)

/-- `stepPub`'s precondition (`r2dStep_ok`'s), with `m` and `x`. -/
def R2pSPre (p : R2pS) (s : State) : Prop :=
  R2dGoodS p.L s ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.M ∧
    2 ^ 63 ≤ (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat ∧
    (word s.mem p.L.B (slot p.L.w aTmp)).toNat =
      (2 ^ 128 - 1) / (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat - 2 ^ 64 ∧
    wv s.mem p.L.B (slot p.L.w aR2) p.L.w = p.X ∧ p.X < p.M

/-- `q̂` is a function of `m` and `x`. -/
theorem r2pSPre_q {p : R2pS} {s : State} (h : R2pSPre p s) :
    r2dQ s.mem p.L.B p.L.w (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat = p.q := by
  obtain ⟨⟨_, _, hw, _⟩, hN, -, -, hX, -⟩ := h
  unfold r2dQ R2pS.q
  rw [word_of_wv s.mem p.L.B (slot p.L.w aR2) p.L.w (show p.L.w - 1 < p.L.w by omega),
    word_of_wv s.mem p.L.B (slot p.L.w aR2) p.L.w (show p.L.w - 2 < p.L.w by omega),
    word_of_wv s.mem p.L.B (slot p.L.w aN) p.L.w (show p.L.w - 1 < p.L.w by omega), hX, hN]

/-- After a step's first pieces: `t = 2^64 x - q̂ m` with a borrow. -/
def R2pSMid (p : R2pS) (s : State) : Prop :=
  R2dGoodS p.L s ∧ StepRegs s p.L.B p.L.w ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.M ∧
    ∃ b : Bool, wv s.mem p.L.B (slot p.L.w aAcc) (p.L.w + 1) + p.q * p.M =
      2 ^ 64 * p.X + 2 ^ (64 * (p.L.w + 1)) * b.toNat

theorem r2pSPre_mid {p : R2pS} {s : State} (h : R2pSPre p s) :
    WP isa (seqs [.block (R2Div.bases ++ quot), zeroAcc, mulAddRow, subPass]) s (R2pSMid p) := by
  have hq := r2pSPre_q h
  obtain ⟨⟨mi, ⟨hg, hZ⟩, hw, hw'⟩, hN, hd, hv, hX, hXM⟩ := h
  refine WP.mono (r2dStepPre_ok hg hZ hw hw' hN rfl hd hv (by rw [hX]; exact hXM))
    fun t ⟨g, r, hN', ⟨b, hb⟩, _, _⟩ => ⟨⟨mi, ⟨g, hZ⟩, hw, hw'⟩, r, hN', b, ?_⟩
  rw [hq, hX] at hb; exact hb

/-- Runs with the same `m` and `x` leave the same `t`. -/
theorem r2pSMid_bind (p : R2pS) (s₁ s₂ : State) (h₁ : R2pSMid p s₁) (h₂ : R2pSMid p s₂) :
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
    omega

theorem pins_r2pSPre : Pins R2pSPre [.x0] := pins_r2dGood (fun (p : R2pS) => p.L) fun _ _ h => h.1

/-- A step's first pieces leak the same, and leave the same `t`, in runs with
the same `m` and `x`. -/
theorem r2pStepPre_ct :
    RelCT isa (Two R2pSPre) (seqs [.block (R2Div.bases ++ quot), zeroAcc, mulAddRow, subPass]) (Two R2pABPre) := by
  have hct : RelCT isa (Two R2pSPre) (seqs [.block (R2Div.bases ++ quot), zeroAcc, mulAddRow, subPass])
      fun _ _ => True := by
    refine two_map (fun (p : R2pS) => p.L) (fun _ _ h => h.1) ?_
    show RelCT isa (Two R2dGoodS) (.seq (.block (R2Div.bases ++ quot)) (.seq zeroAcc (.seq mulAddRow subPass))) _
    refine RelCT.seq (RelCT.block_append (RelCT.seq
      (two_piece (Ψ := R2dStepR) [.x0] (pins_r2dGood id fun _ _ h => h) (by taint_decide)
        fun _ _ h => r2dBases_ok h)
      (two_piece (Ψ := R2dStepR) _ pins_r2dStepR (by taint_decide) fun _ _ h => quot_stepR h)))
      (two_taint _ pins_r2dStepR (by taint_decide))
  exact (two_post hct fun _ _ h => r2pSPre_mid h).mono (fun _ _ h => h) fun _ _ h => two_bind r2pSMid_bind h

theorem r2pStep_eq : stepPub = seqs (([.block (R2Div.bases ++ quot), zeroAcc, mulAddRow, subPass] : List (Prog isa)) ++
    ([addBackPub, addBackPub, copyBack] : List (Prog isa))) := rfl

/-- `stepPub` leaks the same in runs with the same `m` and `x`. -/
theorem r2pStep_ct : RelCT isa (Two R2pSPre) stepPub fun _ _ => True := by
  rw [r2pStep_eq]
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq r2pStepPre_ct ?_)
  show RelCT isa (Two R2pABPre) (.seq addBackPub (.seq addBackPub copyBack)) _
  refine RelCT.seq r2pAddBack_ct (RelCT.seq (r2pAddBack_ct.mono (fun _ _ h => r2p_two_next h) fun _ _ h => r2p_two_next h) ?_)
  exact two_taint _ (pins_r2pABPre.r2pOf fun _ _ h => h) (by taint_decide)

/-! ## The steps -/

/-- What the steps' branches depend on: `m` and the first `x`. -/
structure R2pSs where
  L : Ws
  M : Nat
  X0 : Nat

/-- `stepsPub`'s precondition (`R2dSPre`), with `m` and the first `x`. -/
def R2pSsPre (p : R2pSs) (s : State) : Prop :=
  R2dSPre p.L s ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.M ∧ wv s.mem p.L.B (slot p.L.w aR2) p.L.w = p.X0

/-- After `j` of the `w` steps. -/
def R2pSsAt (p : R2pSs) (j : Nat) (t : State) : Prop :=
  ∃ (σ : State) (mi : BitVec 64) (D : Nat), R2dStepsInv σ p.L.B p.L.Z p.L.w mi p.M D p.X0 p.L.w j t ∧
    slot p.L.w 8 ≤ p.L.Z ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 31 ∧ 2 ^ 63 ≤ D ∧ 0 < p.M

/-- The step after `j` steps, with its `x`. -/
theorem r2pSsAt_sPre {p : R2pSs} {j : Nat} {t : State} (h : R2pSsAt p j t) :
    R2pSPre ⟨p.L, p.M, p.X0 * 2 ^ (64 * j) % p.M⟩ t := by
  obtain ⟨_, mi, D, hI, hZ, hw, hw', hd, hM0⟩ := h
  exact ⟨⟨mi, ⟨hI.g, hZ⟩, hw, hw'⟩, hI.n, by rw [hI.top]; exact hd, by rw [hI.v, hI.top], hI.x,
    Nat.mod_lt _ hM0⟩

/-- `stepsPub` leaks the same in runs with the same `m` and first `x`. -/
theorem r2pSteps_ct : RelCT isa (Two R2pSsPre) stepsPub fun _ _ => True := by
  rw [stepsPub_eq_of]
  unfold stepsOf
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < p.L.w ∧ R2pSsAt p 0 s) [.x0]
    (pins_r2dGood (fun (p : R2pSs) => p.L) fun _ _ h => h.1.1) (by taint_decide) ?_) ?_
  · rintro p s ⟨⟨⟨mi, hg, hw, hw'⟩, h13, hd, hv, hX⟩, hN, hX0⟩
    refine WP.mono (r2dStepsStart_ok hg.1 hg.2 h13 hN rfl hv (by rw [hN] at hX; exact hX)) fun t hI =>
      ⟨by omega, s, mi, _, ?_, hg.2, hw, hw', hd, ?_⟩
    · rw [hX0] at hI; exact hI
    · rw [← hN]; exact Nat.lt_of_le_of_lt (Nat.zero_le _) hX
  refine (two_loop (Φ := R2pSsAt) (Ψ := fun _ _ => True) (fun p => p.L.w) ?_ ?_).mono (fun _ _ h => h)
    fun _ _ _ => trivial
  · refine RelCT.seq (two_post (Ψ := fun (q : R2pSs × Nat) s => R2dGoodS q.1.L s)
      (two_map (fun q => (⟨q.1.L, q.1.M, q.1.X0 * 2 ^ (64 * q.2) % q.1.M⟩ : R2pS))
        (fun _ _ h => r2pSsAt_sPre h.2) r2pStep_ct) ?_)
      (two_taint _ (pins_r2dGood (·.1.L) fun _ _ h => h) (by taint_decide))
    rintro ⟨p, j⟩ s ⟨hj, σ, mi, D, hI, hZ, hw, hw', hd, hM0⟩
    exact WP.mono (stepPub_spec hI.g hZ hw hw' hI.n hI.top hd hI.v (by rw [hI.x]; exact Nat.mod_lt _ hM0))
      fun t ⟨g, _, _, _⟩ => ⟨mi, ⟨g, hZ⟩, hw, hw'⟩
  · rintro p j s hj ⟨σ, mi, D, hI, hZ, hw, hw', hd, hM0⟩
    exact WP.mono (stepsIterWith_ok stepPub_spec hZ hw hw' hd hM0 hw' hj hI)
      fun t ⟨hI', hz⟩ => ⟨eval_count hj hz, fun _ => ⟨σ, mi, D, hI', hZ, hw, hw', hd, hM0⟩, fun _ => trivial⟩

/-! ## `fastPub` -/

/-- `fastPub`'s precondition (`R2dFPre`), with `m`. -/
def R2pFPre (q : Ws × Nat) (s : State) : Prop := R2dFPre q.1 s ∧ wv s.mem q.1.B (slot q.1.w aN) q.1.w = q.2

theorem r2pFast_eq : fastPub = seqs (([.block [ldh .x11 (sArr aR2), ldh .x9 (sArr aN), ldh .x6 (sArr aTmp),
    ldh .x12 sW, movi .x7 0], neg, recipN, .block [ldh .x13 sW]] : List (Prog isa)) ++ ([stepsPub] : List (Prog isa))) :=
  rfl

/-- `fastPub` leaks the same in runs with the same `m`. -/
theorem r2pFast_ct : RelCT isa (Two R2pFPre) fastPub fun _ _ => True := by
  rw [r2pFast_eq]
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (Q := fun _ _ => True)
    (R := Two fun (q : Ws × Nat) => R2pSsPre ⟨q.1, q.2, 2 ^ (64 * q.1.w) - q.2⟩) ?_
    (two_map (fun (q : Ws × Nat) => (⟨q.1, q.2, 2 ^ (64 * q.1.w) - q.2⟩ : R2pSs)) (fun _ _ h => h) r2pSteps_ct))
  have hct : RelCT isa (Two R2pFPre) (seqs [.block [ldh .x11 (sArr aR2), ldh .x9 (sArr aN), ldh .x6 (sArr aTmp),
      ldh .x12 sW, movi .x7 0], neg, recipN, .block [ldh .x13 sW]]) fun _ _ => True := by
    refine RelCT.seq (two_piece (Ψ := fun (q : Ws × Nat) s => R2dF0 q.1 s ∧ wv s.mem q.1.B (slot q.1.w aN) q.1.w = q.2)
      [.x0] (pins_r2dGood Prod.fst fun _ _ h => h.1.1) (by taint_decide) fun _ _ h =>
        (fastLoads_ok h.1).mono fun _ h' => ⟨h'.1, by rw [h'.2]; exact h.2⟩) ?_
    refine RelCT.seq (two_piece (Ψ := R2pF1) _ (fun q s₁ s₂ h₁ h₂ => pins_R2dF0 q.1 s₁ s₂ h₁.1 h₂.1)
      (by taint_decide) fun _ _ h => (fastNeg_ok h.1).mono fun _ h' => ⟨h'.1, by rw [h'.2]; exact h.2⟩) ?_
    refine RelCT.seq recipN_ct ?_
    exact two_taint [.x0] (pins_r2dGood Prod.fst fun _ _ h => h.1.1) (by taint_decide)
  refine two_post hct ?_
  rintro ⟨L, M⟩ s ⟨⟨⟨mi, hg, hw, hw'⟩, hodd, hd⟩, hN⟩
  refine WP.mono (r2dFastHead_ok recipN_spec hg.1 hg.2 hw hw' hN (by rw [← hN]; exact hodd) hd)
    fun t ⟨g, h13, hN', hT, hv, hX, hlt, _, _⟩ => ⟨⟨⟨mi, ⟨g, hg.2⟩, hw, hw'⟩, h13, by rw [hT]; exact hd,
      by rw [hT]; exact hv, by rw [hX, hN']; exact hlt⟩, hN', hX⟩

/-! ## `R² mod m` -/

/-- `R² mod m` for a public `m` leaks the same in runs that agree on `m`:
`choicePub` branches on its top bit, and `fastPub` on values that `m` fixes. -/
theorem r2Pub_ct (M : Mont) : RelCT isa (Two R2Pre) (seqs (r2StepsPub M.mm)) fun _ _ => True := by
  show RelCT isa (Two R2Pre) (R2Div.choicePub (seqs (r2StepsOld M.mm))) _
  unfold R2Div.choicePub
  rw [fastTest_eq]
  refine RelCT.seq (RelCT.block_append (RelCT.seq
    (two_piece (Ψ := R2t) _ (pins_r2 fun _ _ h => h) (by taint_decide) fun _ _ h => r2t_ok h)
    (two_piece (Ψ := R2u) _ pins_r2t (by taint_decide) fun _ _ h => r2u_ok h))) ?_
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2, h₂.2]) ?_ ?_
  · exact (r2Old_ct M).mono (fun _ _ h => two_mono (fun _ _ h => h.1.1) h) fun _ _ h => h
  · refine two_map (fun p => (p.L.ws, p.N)) (fun p s ⟨⟨h, h3⟩, he⟩ => ⟨h.fpre ?_, h.2.2.2.1⟩) r2pFast_ct
    rw [eval_zero, h3] at he
    by_contra hlt
    rw [decide_eq_false hlt] at he
    exact absurd he (by decide)

end VG.Proof.Bignum.AArch64
