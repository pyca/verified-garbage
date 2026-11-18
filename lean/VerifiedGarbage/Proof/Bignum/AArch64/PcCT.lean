module

public import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
public import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
public import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.WordStepNorm
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.AArch64.Run
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
meta import VerifiedGarbage.Proof.Bignum.WordStepNorm
meta import VerifiedGarbage.Proof.Bignum.Words
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.AArch64.Run

/-! ### `Bignum.AArch64.R2dNormCT`, which this module and modules that import it used -/

section

/-! ### `Bignum.AArch64.R2dPubCT`, which only this module used -/

section

/-!
# `R² mod m` for a public `m` on AArch64 leaks only `m`

`r2StepsPub`'s steps branch on the sign of `t = x 2^64 - q̂ m` (`addBackPub`),
which is a function of `m` and `x`, and `x` is a function of `m` and the
step's index: in runs that agree on `m`, every branch agrees.

The relations fix the values the branches depend on: a step's (`R2pS`), `m`
and `x`; `addBackPub`'s (`R2pAB`), `m` and `t`. A step's first pieces, which
the taint analysis checks, leave `t` in place of `x` with
`t + q̂ m = 2^64 x + 2^(64 (w + 1)) b` for a borrow `b`, and
`t < 2^(64 (w + 1))`, so the same `t` in both runs
(`r2pStepPre_ct`); `addBackPub` branches on its sign and leaves
`(t + m) mod 2^(64 (w + 1))` or `t` (`r2pAddBack_ct`). The steps fix `m` and the
first `x`, `R - m` (`r2pSteps_ct`), and `r2Pub_ct` is `r2_ct` with them.
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
    wv s.mem p.L.B (slot p.L.w aR2) (p.L.w + 1) = p.T

theorem pins_r2pABPre : Pins R2pABPre [.x0, .x9, .x11, .x6, .x12, .x7] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pins_r2dGood (fun (p : R2pAB) => p.L) (fun _ _ h => h.1) p s₁ s₂ h₁ h₂ .x0 (by simp)
  · rw [h₁.2.1.x9, h₂.2.1.x9]
  · rw [h₁.2.1.x11, h₂.2.1.x11]
  · rw [h₁.2.1.x6, h₂.2.1.x6]
  · rw [h₁.2.1.x12, h₂.2.1.x12]
  · rw [h₁.2.1.x7, h₂.2.1.x7]

/-- `R2pABPre` with `x3` the sign of `t`. -/
def R2pABSgn (p : R2pAB) (s : State) : Prop := R2pABPre p s ∧ s.gpr .x3 = BitVec.ofNat 64 p.sgn.toNat

/-- `t`'s sign is its top word's top bit. -/
theorem r2pABPre_sign {p : R2pAB} {s : State} (h : R2pABPre p s) :
    decide (2 ^ 63 ≤ (word s.mem p.L.B (slot p.L.w aR2 + 8 * p.L.w)).toNat) = p.sgn := by
  rw [R2pAB.sgn, word_of_wv s.mem p.L.B (slot p.L.w aR2) (p.L.w + 1) (Nat.lt_succ_self _), h.2.2.2]

theorem r2pSign_ok {p : R2pAB} {s : State} (h : R2pABPre p s) : WP isa (.block signTest) s (R2pABSgn p) := by
  obtain ⟨⟨mi, ⟨hg, hZ⟩, hw, hw'⟩, r, hN, hT⟩ := h
  have lA := Nat.le_trans (slot_le (w := p.L.w) (show aR2 < 8 by decide)) hZ
  refine WP.mono (signTest_ok hg.scr r.x11 r.x12 hw' (by omega_arith)) fun t ⟨⟨h3, hm⟩, k⟩ => ?_
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
    have hlt := wv_lt s.mem p.L.B (slot p.L.w aR2) (p.L.w + 1)
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
    have lA := sl aR2 (by decide)
    have lM := sl aN (by decide)
    have sAM := slot_sep (w := p.L.w) (show aR2 ≠ aN by decide)
    refine WP.mono (addBack_spec hg.scr r.x11 r.x9 r.x12 r.x7 (by omega_arith) hw' (by omega_arith) (by omega_arith) (by omega_arith))
      fun t ⟨c, hv, o, k⟩ => ?_
    have ha : Arrays p.L.B p.L.w [aR2] s.mem t.mem :=
      Arrays.of_outside (List.mem_singleton_self _) o (Nat.le_refl _) (by omega_arith)
    refine ⟨⟨mi, ⟨⟨hg.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hg.x0, ha.hdr hg.hdr⟩, hZ⟩, hw, hw'⟩,
      r.keep k, by show wv t.mem p.L.B (slot p.L.w aN) p.L.w = p.M; rw [o.wv (by omega_arith) (by omega_arith)]; exact hN, ?_⟩
    rw [hT, hN] at hv
    exact r2p_lt_carry_mod hv (wv_lt _ _ _ _)

/-! ## A step -/

/-- What a step's branches depend on: `m` and `x`. -/
structure R2pS where
  L : Ws
  M : Nat
  X : Nat

/-- `q̂` of `x` and `m`. -/
def R2pS.q (p : R2pS) : Nat := r2dQ p.X p.M p.L.w

/-- `stepPub`'s precondition (`r2dStep_ok`'s), with `m` and `x`. -/
def R2pSPre (p : R2pS) (s : State) : Prop :=
  R2dGoodS p.L s ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.M ∧
    2 ^ 63 ≤ (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat ∧
    (word s.mem p.L.B (slot p.L.w aTmp)).toNat =
      (2 ^ 128 - 1) / (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat - 2 ^ 64 ∧
    wv s.mem p.L.B (slot p.L.w aR2) p.L.w = p.X ∧ p.X < p.M

/-- After a step's first pieces: `t = 2^64 x - q̂ m` with a borrow. -/
def R2pSMid (p : R2pS) (s : State) : Prop :=
  R2dGoodS p.L s ∧ StepRegs s p.L.B p.L.w ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.M ∧
    ∃ b : Bool, wv s.mem p.L.B (slot p.L.w aR2) (p.L.w + 1) + p.q * p.M =
      2 ^ 64 * p.X + 2 ^ (64 * (p.L.w + 1)) * b.toNat

theorem r2pSPre_mid {p : R2pS} {s : State} (h : R2pSPre p s) :
    WP isa (seqs [.block (R2Div.bases ++ quot), .block quot3, mulSub]) s (R2pSMid p) := by
  obtain ⟨⟨mi, ⟨hg, hZ⟩, hw, hw'⟩, hN, hd, hv, hX, hXM⟩ := h
  refine WP.mono (r2dStepPre_ok hg hZ hw hw' hN rfl hd hv (by rw [hX]; exact hXM))
    fun t ⟨g, r, hN', ⟨b, hb⟩, _, _⟩ => ⟨⟨mi, ⟨g, hZ⟩, hw, hw'⟩, r, hN', b, ?_⟩
  rw [hX] at hb; exact hb

/-- Runs with the same `m` and `x` leave the same `t`. -/
theorem r2pSMid_bind (p : R2pS) (s₁ s₂ : State) (h₁ : R2pSMid p s₁) (h₂ : R2pSMid p s₂) :
    ∃ q, R2pABPre q s₁ ∧ R2pABPre q s₂ := by
  obtain ⟨g₁, r₁, n₁, b₁, e₁⟩ := h₁
  obtain ⟨g₂, r₂, n₂, b₂, e₂⟩ := h₂
  refine ⟨⟨p.L, p.M, wv s₁.mem p.L.B (slot p.L.w aR2) (p.L.w + 1)⟩, ⟨g₁, r₁, n₁, rfl⟩, ⟨g₂, r₂, n₂, ?_⟩⟩
  show wv s₂.mem p.L.B (slot p.L.w aR2) (p.L.w + 1) = wv s₁.mem p.L.B (slot p.L.w aR2) (p.L.w + 1)
  have l₁ := wv_lt s₁.mem p.L.B (slot p.L.w aR2) (p.L.w + 1)
  have l₂ := wv_lt s₂.mem p.L.B (slot p.L.w aR2) (p.L.w + 1)
  generalize 2 ^ (64 * (p.L.w + 1)) = W at *
  generalize p.q * p.M = Q at *
  generalize 2 ^ 64 * p.X = X at *
  cases b₁ <;> cases b₂ <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one] at e₁ e₂ <;>
    omega_arith

/-- A step's first pieces leak the same, and leave the same `t`, in runs with
the same `m` and `x`. -/
theorem r2pStepPre_ct :
    RelCT isa (Two R2pSPre) (seqs [.block (R2Div.bases ++ quot), .block quot3, mulSub]) (Two R2pABPre) := by
  have hct : RelCT isa (Two R2pSPre) (seqs [.block (R2Div.bases ++ quot), .block quot3, mulSub])
      fun _ _ => True := by
    refine two_map (fun (p : R2pS) => p.L) (fun _ _ h => h.1) ?_
    show RelCT isa (Two R2dGoodS) (.seq (.block (R2Div.bases ++ quot)) (.seq (.block quot3) mulSub)) _
    refine RelCT.seq (RelCT.block_append (RelCT.seq
      (two_piece (Ψ := R2dStepR) [.x0] (pins_r2dGood id fun _ _ h => h) (by taint_decide)
        fun _ _ h => r2dBases_ok h)
      (two_piece (Ψ := R2dStepR) _ pins_r2dStepR (by taint_decide) fun _ _ h => quot_stepR h)))
      (two_taint _ pins_r2dStepR (by taint_decide))
  exact (two_post hct fun _ _ h => r2pSPre_mid h).mono (fun _ _ h => h) fun _ _ h => two_bind r2pSMid_bind h

theorem r2pStep_eq : stepPub = seqs (([.block (R2Div.bases ++ quot), .block quot3, mulSub] : List (Prog isa)) ++
    ([addBackPub] : List (Prog isa))) := rfl

/-- `stepPub` leaks the same in runs with the same `m` and `x`. -/
theorem r2pStep_ct : RelCT isa (Two R2pSPre) stepPub fun _ _ => True := by
  rw [r2pStep_eq]
  exact RelCT.seqs_append (by simp) (by simp) (RelCT.seq r2pStepPre_ct (r2pAddBack_ct.mono (fun _ _ h => h)
    fun _ _ _ => trivial))

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
      ⟨by omega_arith, s, mi, _, ?_, hg.2, hw, hw', hd, ?_⟩
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
    ldh .x12 sW, movi .x7 0], neg, recip, .block [ldh .x13 sW]] : List (Prog isa)) ++ ([stepsPub] : List (Prog isa))) :=
  rfl

/-- `fastPub` leaks the same in runs with the same `m`. -/
theorem r2pFast_ct : RelCT isa (Two R2pFPre) fastPub fun _ _ => True := by
  rw [r2pFast_eq]
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (Q := fun _ _ => True)
    (R := Two fun (q : Ws × Nat) => R2pSsPre ⟨q.1, q.2, 2 ^ (64 * q.1.w) - q.2⟩) ?_
    (two_map (fun (q : Ws × Nat) => (⟨q.1, q.2, 2 ^ (64 * q.1.w) - q.2⟩ : R2pSs)) (fun _ _ h => h) r2pSteps_ct))
  have hct : RelCT isa (Two R2dFPre) (seqs [.block [ldh .x11 (sArr aR2), ldh .x9 (sArr aN), ldh .x6 (sArr aTmp),
      ldh .x12 sW, movi .x7 0], neg, recip, .block [ldh .x13 sW]]) fun _ _ => True := by
    refine RelCT.seq (two_piece (Ψ := R2dF0) [.x0] (pins_r2dGood id fun _ _ h => h.1)
      (by taint_decide) fun _ _ h => fastLoads_ok h) ?_
    refine RelCT.seq (two_piece (Ψ := R2dF1) _ pins_R2dF0 (by taint_decide) fun _ _ h => fastNeg_ok h) ?_
    refine RelCT.seq (two_piece (Ψ := R2dF2) _ pins_R2dF1 (by taint_decide) fun _ _ h => fastRecip_ok h) ?_
    exact two_taint [.x0] (pins_r2dGood id fun _ _ h => h.1.1) (by taint_decide)
  refine two_post (two_map Prod.fst (fun _ _ h => h.1) hct) ?_
  rintro ⟨L, M⟩ s ⟨⟨⟨mi, hg, hw, hw'⟩, hodd, hd⟩, hN⟩
  refine WP.mono (r2dFastHead_ok hg.1 hg.2 hw hw' hN (by rw [← hN]; exact hodd) hd)
    fun t ⟨g, h13, hN', hT, hv, hX, hlt, _, _⟩ => ⟨⟨⟨mi, ⟨g, hg.2⟩, hw, hw'⟩, h13, by rw [hT]; exact hd,
      by rw [hT]; exact hv, by rw [hX, hN']; exact hlt⟩, hN', hX⟩

end VG.Proof.Bignum.AArch64

end

end

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

theorem pins_r2nR : Pins R2nR [.x9, .x11, .x6, .x12, .x7] :=
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
def R2nS.q (p : R2nS) : Nat := r2dQN p.X p.M p.L.w p.z

/-- `stepN`'s precondition (`r2dStepN_ok`'s), with `m`, `x` and `z`. -/
def R2nSPre (p : R2nS) (s : State) : Prop :=
  R2nG p.L s ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.M ∧ p.z ≤ 63 ∧
    (word s.mem p.L.B (slot p.L.w aTmp + 8)).toNat = 2 ^ p.z ∧
    (word s.mem p.L.B (slot p.L.w aTmp + 16)).toNat = p.d ∧ 2 ^ 63 ≤ p.d ∧
    (word s.mem p.L.B (slot p.L.w aTmp)).toNat = (2 ^ 128 - 1) / p.d - 2 ^ 64 ∧
    (word s.mem p.L.B (slot p.L.w aTmp + 24)).toNat = p.M * 2 ^ p.z / 2 ^ (64 * (p.L.w - 2)) % 2 ^ 64 ∧
    wv s.mem p.L.B (slot p.L.w aR2) p.L.w = p.X ∧ p.X < p.M

/-- After a step's first pieces: `t = 2^64 x - q̂ m` with a borrow. -/
def R2nSMid (p : R2nS) (s : State) : Prop :=
  R2dGoodS p.L s ∧ StepRegs s p.L.B p.L.w ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.M ∧
    ∃ b : Bool, wv s.mem p.L.B (slot p.L.w aR2) (p.L.w + 1) + p.q * p.M =
      2 ^ 64 * p.X + 2 ^ (64 * (p.L.w + 1)) * b.toNat

theorem r2nSPre_mid {p : R2nS} {s : State} (h : R2nSPre p s) :
    WP isa (seqs [.block (R2Div.bases ++ quotN), .block quot3N, mulSub]) s (R2nSMid p) := by
  obtain ⟨⟨⟨mi, ⟨hg, hZ⟩, hw, hw'⟩, hw3⟩, hN, hz, hP, hD, hd, hv, hDl, hX, hXM⟩ := h
  refine WP.mono (r2dStepPreN_ok hg hZ hw3 hw' hN hP hz hD hd hv hDl (by rw [hX]; exact hXM))
    fun t ⟨g, r, hN', ⟨b, hb⟩, _, _⟩ => ⟨⟨mi, ⟨g, hZ⟩, hw, hw'⟩, r, hN', b, ?_⟩
  rw [hX] at hb; exact hb

/-- Runs with the same `m`, `x` and `z` leave the same `t`. -/
theorem r2nSMid_bind (p : R2nS) (s₁ s₂ : State) (h₁ : R2nSMid p s₁) (h₂ : R2nSMid p s₂) :
    ∃ q, R2pABPre q s₁ ∧ R2pABPre q s₂ := by
  obtain ⟨g₁, r₁, n₁, b₁, e₁⟩ := h₁
  obtain ⟨g₂, r₂, n₂, b₂, e₂⟩ := h₂
  refine ⟨⟨p.L, p.M, wv s₁.mem p.L.B (slot p.L.w aR2) (p.L.w + 1)⟩, ⟨g₁, r₁, n₁, rfl⟩, ⟨g₂, r₂, n₂, ?_⟩⟩
  show wv s₂.mem p.L.B (slot p.L.w aR2) (p.L.w + 1) = wv s₁.mem p.L.B (slot p.L.w aR2) (p.L.w + 1)
  have l₁ := wv_lt s₁.mem p.L.B (slot p.L.w aR2) (p.L.w + 1)
  have l₂ := wv_lt s₂.mem p.L.B (slot p.L.w aR2) (p.L.w + 1)
  generalize 2 ^ (64 * (p.L.w + 1)) = W at *
  generalize p.q * p.M = Q at *
  generalize 2 ^ 64 * p.X = X at *
  cases b₁ <;> cases b₂ <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one] at e₁ e₂ <;>
    omega_arith

/-- A step's first pieces leak the same, and leave the same `t`, in runs with
the same `m`, `x` and `z`. -/
theorem r2nStepPre_ct :
    RelCT isa (Two R2nSPre) (seqs [.block (R2Div.bases ++ quotN), .block quot3N, mulSub]) (Two R2pABPre) := by
  have hct : RelCT isa (Two R2nSPre) (seqs [.block (R2Div.bases ++ quotN), .block quot3N, mulSub])
      fun _ _ => True := by
    refine two_map (fun (p : R2nS) => p.L) (fun _ _ h => h.1) ?_
    show RelCT isa (Two R2nG) (.seq (.block (R2Div.bases ++ quotN)) (.seq (.block quot3N) mulSub)) _
    refine RelCT.seq (RelCT.block_append (RelCT.seq
      (two_piece (Ψ := R2nR) [.x0] (pins_r2dGood id fun _ _ h => h.1) (by taint_decide)
        fun _ _ h => r2nBases_ok h)
      (two_piece (Ψ := R2dStepR) _ pins_r2nR (by taint_decide) fun _ _ h => quotN_stepR h)))
      (two_taint _ pins_r2dStepR (by taint_decide))
  exact (two_post hct fun _ _ h => r2nSPre_mid h).mono (fun _ _ h => h) fun _ _ h => two_bind r2nSMid_bind h

theorem r2nStep_eq : stepN = seqs (([.block (R2Div.bases ++ quotN), .block quot3N, mulSub] : List (Prog isa)) ++
    ([addBackPub] : List (Prog isa))) := rfl

/-- `stepN` leaks the same in runs with the same `m`, `x` and `z`. -/
theorem r2nStep_ct : RelCT isa (Two R2nSPre) stepN fun _ _ => True := by
  rw [r2nStep_eq]
  exact RelCT.seqs_append (by simp) (by simp) (RelCT.seq r2nStepPre_ct (r2pAddBack_ct.mono (fun _ _ h => h)
    fun _ _ _ => trivial))

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
  exact ⟨⟨⟨mi, ⟨hI.g, hZ⟩, by show 2 ≤ p.L.w; omega_arith, by show p.L.w < 2 ^ 31; omega_arith⟩, hw⟩, hI.n, hz, hI.p, hI.d, hd, hI.v,
    hI.dl, hI.x, Nat.mod_lt _ hM0⟩

theorem r2nSteps_eq : stepsN =
    .seq (.block [sth .x13 sCnt]) (.loop (.seq stepN (.block (dblCount sCnt))) (.nonzero .x .x13)) := rfl

/-- `stepsN` leaks the same in runs with the same `m`, first `x` and `z`. -/
theorem r2nSteps_ct : RelCT isa (Two R2nSsPre) stepsN fun _ _ => True := by
  rw [r2nSteps_eq]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < p.L.w + 1 ∧ R2nSsAt p 0 s) [.x0]
    (pins_r2dGood (fun (p : R2nSs) => p.L) fun _ _ h => h.1.1) (by taint_decide) ?_) ?_
  · rintro p s ⟨⟨⟨mi, hg, hw, hw'⟩, hw3⟩, hw30, h13, -, hN, hz, hP, hD, hd, hv, hDl, hX, hXM⟩
    refine WP.mono (r2dStepsStartN_ok hg.1 hg.2 (by omega_arith) h13 hN hP hD hv hDl (by rw [hX]; exact hXM)) fun t hI =>
      ⟨by omega_arith, s, mi, ?_, hg.2, hw3, hw30, hz, hd, Nat.lt_of_le_of_lt (Nat.zero_le _) hXM⟩
    rw [hX] at hI; exact hI
  refine (two_loop (Φ := R2nSsAt) (Ψ := fun _ _ => True) (fun p => p.L.w + 1) ?_ ?_).mono (fun _ _ h => h)
    fun _ _ _ => trivial
  · refine RelCT.seq (two_post (Ψ := fun (q : R2nSs × Nat) s => R2dGoodS q.1.L s)
      (two_map (fun q => (⟨q.1.L, q.1.M, q.1.X0 * 2 ^ (64 * q.2) % q.1.M, q.1.z⟩ : R2nS))
        (fun _ _ h => r2nSsAt_sPre h.2) r2nStep_ct) ?_)
      (two_taint _ (pins_r2dGood (·.1.L) fun _ _ h => h) (by taint_decide))
    rintro ⟨p, j⟩ s ⟨hj, σ, mi, hI, hZ, hw, hw', hz, hd, hM0⟩
    exact WP.mono (r2dStepN_ok hI.g hZ hw (by omega_arith) hI.n hI.p hz hI.d hd hI.v hI.dl
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
    exact WP.mono (r2dFastNHead_ok hg.1 hg.2 hw3 hw30 hN hodd hlo)
      fun t ⟨g, h13, N, ⟨z, hz, P, D, hd, V, Dl⟩, X, hlt, _, _⟩ =>
      ⟨z, ⟨⟨mi, ⟨g, hg.2⟩, hw, hw'⟩, hw3⟩, hw30, h13, ⟨⟨⟨mi, ⟨g, hg.2⟩, hw, hw'⟩, hw3⟩, N, hz, P, D, hd, V, Dl, X, hlt⟩⟩
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

end

end

/-!
# `vg_rsa_public_precompute` on AArch64: constant time but for `n`

Every piece's addresses and branches depend only on the pointers, the
lengths and `n`: the load of `m` and `-m⁻¹` (`pcLoad_ct`), `R² mod m`
(`pcR2_ct`), the copies to `pre` (`pcOut_ct`), and the whole function
(`pcCode_constantTime`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

theorem slot0_ge (w : Nat) : 8 * 31 + 8 ≤ slot w 0 ∧ slot w 0 + 8 * (w + 2) ≤ slot w 8 :=
  ⟨hdr_lt_slot w 0 (by decide), slot_le (by decide)⟩

/-! ## `main` -/

/-- The public data of `main`: the working space, `k`, `pre`, and `m` (its
bytes `nb` at `np`). -/
structure PcPub where
  B : Addr
  Z : Nat
  k : Nat
  op : Addr
  np : Addr
  nb : List Byte

abbrev PcPub.w (p : PcPub) : Nat := (p.k + 7) / 8
abbrev PcPub.N (p : PcPub) : Nat := Spec.Rsa.os2ip p.nb

/-- `pcMain_ok`'s hypotheses. -/
def PcM (p : PcPub) (s : State) : Prop :=
  Scr s p.B p.Z ∧ s.gpr .x0 = p.B ∧ slot p.w 8 ≤ p.Z ∧ 64 ≤ p.k ∧ p.k ≤ 1024 ∧
    word s.mem p.B (8 * sOut) = p.op ∧ word s.mem p.B (8 * sK) = BitVec.ofNat 64 p.k ∧
    word s.mem p.B (8 * sN) = p.np ∧ Src s p.B p.Z p.np p.nb ∧ p.nb.length = p.k ∧
    Spec.Rsa.modulusValid p.N p.k = true ∧ (∀ i < 2 * p.w, InRegions s.wr (off p.op (8 * i)) 8) ∧
    (∀ i < 16 * p.w, p.Z ≤ ofs p.B (p.op + BitVec.ofNat 64 i)) ∧ InRegions (s.rd ++ s.wr) p.np p.k

/-- `PcM` after code that changes only memory in the working space outside
the header's arguments, and not `x0`. -/
theorem PcM.congr {p : PcPub} {s t : State} (h : PcM p s) {rs : List (Nat × Nat)}
    (hf : Frm p.B rs s.mem t.mem) (hz : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z)
    (hx : ∀ r ∈ rs, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16))
    {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : PcM p t := by
  obtain ⟨hs, h0, hZ, hk1, hk2, hO, hK, hN, hn, hnl, hv, hpw, hps, hsp⟩ := h
  have hi := InScr.of_frm hf hz
  have hfx := Fixed.of_frm hf hx
  exact ⟨hs.congr k.wr, (k.gpr .x0 hr).trans h0, hZ, hk1, hk2, (hfx sOut (by decide)).trans hO,
    (hfx sK (by decide)).trans hK, (hfx sN (by decide)).trans hN, hn.congrK hi k, hnl, hv,
    fun i hi => by rw [k.wr]; exact hpw i hi, hps, by rw [k.rd, k.wr]; exact hsp⟩

/-- What the load of `m` and `-m⁻¹` needs: `PcM` but for `pre`. -/
def PcL (p : PcPub) (s : State) : Prop :=
  Scr s p.B p.Z ∧ s.gpr .x0 = p.B ∧ slot p.w 8 ≤ p.Z ∧ 64 ≤ p.k ∧ p.k ≤ 1024 ∧
    word s.mem p.B (8 * sK) = BitVec.ofNat 64 p.k ∧ word s.mem p.B (8 * sN) = p.np ∧ Src s p.B p.Z p.np p.nb ∧
    p.nb.length = p.k ∧ Spec.Rsa.modulusValid p.N p.k = true

theorem PcM.load {p : PcPub} {s : State} (h : PcM p s) : PcL p s :=
  let ⟨hs, h0, hZ, hk1, hk2, _, hK, hN, hn, hnl, hv, _⟩ := h
  ⟨hs, h0, hZ, hk1, hk2, hK, hN, hn, hnl, hv⟩

/-- `PcL`, with `m` in one region: what the load of `m` a word at a time
needs. -/
def PcLW (p : PcPub) (s : State) : Prop := PcL p s ∧ InRegions (s.rd ++ s.wr) p.np p.k

theorem PcM.loadW {p : PcPub} {s : State} (h : PcM p s) : PcLW p s :=
  ⟨h.load, h.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- `PcL` after code that changes only memory in the working space outside
the header's arguments, and not `x0`. -/
theorem PcL.congr {p : PcPub} {s t : State} (h : PcL p s) {rs : List (Nat × Nat)}
    (hf : Frm p.B rs s.mem t.mem) (hz : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z)
    (hx : ∀ r ∈ rs, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16))
    {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : PcL p t := by
  obtain ⟨hs, h0, hZ, hk1, hk2, hK, hN, hn, hnl, hv⟩ := h
  have hi := InScr.of_frm hf hz
  have hfx := Fixed.of_frm hf hx
  exact ⟨hs.congr k.wr, (k.gpr .x0 hr).trans h0, hZ, hk1, hk2, (hfx sK (by decide)).trans hK,
    (hfx sN (by decide)).trans hN, hn.congrK hi k, hnl, hv⟩

theorem PcLW.congr {p : PcPub} {s t : State} (h : PcLW p s) {rs : List (Nat × Nat)}
    (hf : Frm p.B rs s.mem t.mem) (hz : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z)
    (hx : ∀ r ∈ rs, 8 * 22 ≤ r.1 ∨ (8 * 6 ≤ r.1 ∧ r.1 + r.2 ≤ 8 * 16))
    {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : PcLW p t :=
  ⟨h.1.congr hf hz hx k hr, by rw [k.rd, k.wr]; exact h.2⟩

theorem pins_PcL : Pins PcL [.x0] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]

/-- After the first block. -/
def Pc1 (p : PcPub) (s : State) : Prop :=
  PcL p s ∧ s.gpr .x1 = p.np ∧ s.gpr .x2 = BitVec.ofNat 64 p.k ∧ s.gpr .x8 = off p.B (slot p.w aN)

/-- After `-m⁻¹`: `R² mod m`'s hypotheses, and `PcM`. -/
def Pc3 (p : PcPub) (s : State) : Prop :=
  ∃ mi : BitVec 64, PcM p s ∧ R2Pre ⟨⟨p.B, p.Z, p.w, mi⟩, p.N⟩ s

theorem pins_Pc1 : Pins Pc1 [.x0, .x1, .x2, .x8] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.1.2.1, h₂.1.2.1]
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2, h₂.2.2.2]

/-- The load of `m` and `-m⁻¹` leak the same in runs that agree on `m`. -/
theorem pcLoad_ct : RelCT isa (Two PcL) (seqs pcLoad) fun _ _ => True := by
  unfold pcLoad
  -- `w`, the bases, and `m`'s registers.
  refine RelCT.seq (two_piece (Ψ := Pc1) _ pins_PcL (by taint_decide) ?_) ?_
  · intro p s h
    have h' := h
    obtain ⟨hs, h0, hZ, hk1, hk2, hK, hN, -⟩ := h'
    obtain ⟨g0, g8⟩ := slot0_ge p.w
    refine WP.mono (pcHead_ok hs h0 hZ (by omega_arith) hK hN) fun t ⟨h1, h2, h8, _, _, hf, k⟩ =>
      ⟨h.congr hf (fun r hr => ?_) (fun r hr => ?_) k (by decide), h1, h2, h8⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sW, sArr] <;> omega_arith
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sW, sArr] <;> omega_arith
  -- `m`.
  refine RelCT.seq (two_piece (Ψ := fun (p : PcPub) s => s.gpr .x0 = p.B ∧ s.gpr .x8 = off p.B (slot p.w aN)) _
    pins_Pc1 (by taint_decide) ?_) ?_
  · intro p s ⟨h, h1, h2, h8⟩
    obtain ⟨hs, h0, hZ, hk1, hk2, -, -, hn, hnl, -⟩ := h
    exact WP.mono (loadArr_ok hs (by decide) hZ hn hnl (by omega_arith) (by omega_arith) h1 h2 h8) fun t ⟨_, _, k⟩ =>
      ⟨(k.gpr .x0 (by decide)).trans h0, (k.gpr .x8 (by decide)).trans h8⟩
  -- `-m⁻¹`.
  exact two_taint [.x0, .x8] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1, h₂.1]
    · rw [h₁.2, h₂.2]) (by taint_decide)

/-- After the first block of `pcLoadW`. -/
def Pc1W (p : PcPub) (s : State) : Prop :=
  PcLW p s ∧ s.gpr .x1 = p.np ∧ s.gpr .x2 = BitVec.ofNat 64 p.k ∧ s.gpr .x8 = off p.B (slot p.w aN)

theorem pins_Pc1W : Pins Pc1W [.x0, .x1, .x2, .x8] :=
  fun p s₁ s₂ h₁ h₂ => pins_Pc1 p s₁ s₂ ⟨h₁.1.1, h₁.2⟩ ⟨h₂.1.1, h₂.2⟩

/-- The load of `m` a word at a time and `-m⁻¹` leak the same in runs that
agree on `m`. -/
theorem pcLoadW_ct : RelCT isa (Two PcLW) (seqs pcLoadW) fun _ _ => True := by
  unfold pcLoadW pcLoadWith
  -- `w`, the bases, and `m`'s registers.
  refine RelCT.seq (two_piece (Ψ := Pc1W) [.x0] (fun p s₁ s₂ h₁ h₂ => pins_PcL p s₁ s₂ h₁.1 h₂.1)
    (by taint_decide) ?_) ?_
  · intro p s h
    have h' := h.1
    obtain ⟨hs, h0, hZ, hk1, hk2, hK, hN, -⟩ := h'
    obtain ⟨g0, g8⟩ := slot0_ge p.w
    refine WP.mono (pcHead_ok hs h0 hZ (by omega_arith) hK hN) fun t ⟨h1, h2, h8, _, _, hf, k⟩ =>
      ⟨h.congr hf (fun r hr => ?_) (fun r hr => ?_) k (by decide), h1, h2, h8⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sW, sArr] <;> omega_arith
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [sW, sArr] <;> omega_arith
  -- `m`.
  refine RelCT.seq (two_piece (Ψ := fun (p : PcPub) s => s.gpr .x0 = p.B ∧ s.gpr .x8 = off p.B (slot p.w aN)) _
    pins_Pc1W (by taint_decide) ?_) ?_
  · intro p s ⟨⟨h, hsp⟩, h1, h2, h8⟩
    obtain ⟨hs, h0, hZ, hk1, hk2, -, -, hn, hnl, -⟩ := h
    exact WP.mono (loadArrW_ok hs (by decide) hZ hn hsp hnl (by omega_arith) (by omega_arith) h1 h2 h8) fun t ⟨_, _, k⟩ =>
      ⟨(k.gpr .x0 (by decide)).trans h0, (k.gpr .x8 (by decide)).trans h8⟩
  -- `-m⁻¹`.
  exact two_taint [.x0, .x8] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1, h₂.1]
    · rw [h₁.2, h₂.2]) (by taint_decide)

/-- `R² mod m`'s hypotheses after the load of `m` a word at a time and
`-m⁻¹`. -/
theorem pcLoadW_r2 {s : State} {B : Addr} {Z k : Nat} {np : Addr} {nb : List Byte} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 64 ≤ k) (hk2 : k ≤ 1024)
    (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k) (hN : word s.mem B (8 * sN) = np)
    (hnb : Src s B Z np nb) (hsp : InRegions (s.rd ++ s.wr) np k) (hnl : nb.length = k)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) :
    WP isa (seqs pcLoadW) s fun t => ∃ minv, R2Pre ⟨⟨B, Z, (k + 7) / 8, minv⟩, Spec.Rsa.os2ip nb⟩ t ∧
      Frm B (pcLoadRanges ((k + 7) / 8)) s.mem t.mem ∧ Keep mmRegs s t := by
  obtain ⟨hodd, -, hlo⟩ := valid_facts hv hk1
  exact WP.mono (pcLoadW_ok hs h0 hZ (by omega_arith) (by omega_arith) hK hN hnb hsp hnl hodd)
    fun t ⟨minv, hg, hn, hinv, f, k⟩ => ⟨minv, ⟨⟨hg, hZ⟩, by dsimp only; omega_arith, by dsimp only; omega_arith, hn, hinv,
      hodd, hlo⟩, f, k⟩

/-! ## `R² mod m` -/

/-- `main`'s public data with `-m⁻¹`. -/
abbrev PcPub.L (q : PcPub × BitVec 64) : Lay := ⟨q.1.B, q.1.Z, q.1.w, q.2⟩

/-- `-m⁻¹` is the same in runs that agree on `m`. -/
theorem pc3_minv {p : PcPub} {s₁ s₂ : State} {mi₁ mi₂ : BitVec 64}
    (h₁ : R2Pre ⟨⟨p.B, p.Z, p.w, mi₁⟩, p.N⟩ s₁) (h₂ : R2Pre ⟨⟨p.B, p.Z, p.w, mi₂⟩, p.N⟩ s₂) : mi₁ = mi₂ := by
  have e : ∀ {s : State} {mi : BitVec 64}, R2Pre ⟨⟨p.B, p.Z, p.w, mi⟩, p.N⟩ s →
      ((p.N % 2 ^ 64) * mi.toNat + 1) % 2 ^ 64 = 0 := fun h => by
    have hw := h.2.1
    have hv := h.2.2.2.1
    have hi := h.2.2.2.2.1
    dsimp only at hw hv hi
    rwa [← wv_mod64 _ _ _ (show 1 ≤ p.w by omega_arith), hv] at hi
  exact minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact h₁.2.2.2.2.2.1) (e h₁) (e h₂)

/-- What the copies to `pre` need. -/
def PcO (q : PcPub × BitVec 64) (s : State) : Prop :=
  GoodL (PcPub.L q) s ∧ 2 ≤ q.1.w ∧ q.1.w < 2 ^ 30 ∧ word s.mem q.1.B (8 * sOut) = q.1.op ∧
    (∀ i < 2 * q.1.w, InRegions s.wr (off q.1.op (8 * i)) 8) ∧
    (∀ i < 16 * q.1.w, q.1.Z ≤ ofs q.1.B (q.1.op + BitVec.ofNat 64 i))

/-- `R² mod m` leaks the same in runs that agree on `m`. -/
theorem pcR2_ct (M : Mont) : RelCT isa (Two Pc3) (seqs (r2StepsPub M.mm)) (Two PcO) := by
  have h := two_post (Φ := fun (q : PcPub × BitVec 64) s => PcM q.1 s ∧ R2Pre ⟨PcPub.L q, q.1.N⟩ s)
    (Ψ := PcO) (two_map (fun q => (⟨PcPub.L q, q.1.N⟩ : R2Pub)) (fun _ _ h => h.2) (r2Pub_ct M)) ?_
  · exact h.mono (fun _ _ hp => two_bind (fun p s₁ s₂ ⟨mi₁, m₁, r₁⟩ ⟨mi₂, m₂, r₂⟩ => by
      obtain rfl := pc3_minv r₁ r₂
      exact ⟨(p, mi₁), ⟨m₁, r₁⟩, m₂, r₂⟩) hp) fun _ _ h => h
  rintro ⟨p, mi⟩ s ⟨hm, hr⟩
  obtain ⟨hg, hw, hw', hn, hinv, hodd, hlo⟩ := hr
  dsimp only at hg hw hw' hn hinv hodd hlo
  refine WP.mono (r2Pub_ok M hg.1 hg.2 hw hw' hn hinv hodd hlo) fun t ⟨hg', _, _, f, k⟩ =>
    ⟨⟨hg', hg.2⟩, hw, hw', ?_, fun i hi => by rw [k.wr]; exact hm.2.2.2.2.2.2.2.2.2.2.2.1 i hi,
      hm.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
  rw [(Fixed.of_frm f (r2Ranges_fixed _)) sOut (by decide)]
  exact hm.2.2.2.2.2.1

/-! ## The copies to `pre` -/

/-- `Good` after code that changes only memory outside the working space. -/
theorem Good.of_inScr {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hi : ∀ x, ofs B x < Z → t.mem x = s.mem x) (hwr : t.wr = s.wr)
    (h0 : t.gpr .x0 = B) : Good t B Z w minv := by
  have hn := hg.scr.nowrap
  have h8 := hdr_lt_slot w 0 (show 31 < 32 by decide)
  have h0' := slot_le (w := w) (show 0 < 8 by decide)
  have hw : ∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi' =>
    Mem.readW_congr fun b hb => hi _ (by rw [ofs_off B (d := 8 * i) (i := b) (by omega_arith)]; omega_arith)
  exact ⟨hg.scr.congr hwr, h0, ⟨by rw [hw sW (by decide)]; exact hg.hdr.hw,
    by rw [hw sMinv (by decide)]; exact hg.hdr.hminv,
    fun j hj => by rw [hw (sArr j) (by unfold sArr; omega_arith)]; exact hg.hdr.harr j hj⟩⟩

/-- Before the first copy. -/
def PcO1 (q : PcPub × BitVec 64) (s : State) : Prop :=
  PcO q s ∧ s.gpr .x12 = BitVec.ofNat 64 q.1.w ∧ s.gpr .x16 = off q.1.B (slot q.1.w aN) ∧
    s.gpr .x17 = off q.1.op 0

/-- After the first copy. -/
def PcO2 (q : PcPub × BitVec 64) (s : State) : Prop :=
  PcO q s ∧ s.gpr .x12 = BitVec.ofNat 64 q.1.w ∧ s.gpr .x17 = off q.1.op (8 * q.1.w)

/-- Before the second copy. -/
def PcO3 (q : PcPub × BitVec 64) (s : State) : Prop :=
  PcO q s ∧ s.gpr .x12 = BitVec.ofNat 64 q.1.w ∧ s.gpr .x16 = off q.1.B (slot q.1.w aR2) ∧
    s.gpr .x17 = off q.1.op (8 * q.1.w)

theorem pins_PcO : Pins PcO [.x0] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.x0, h₂.1.1.x0]

/-- A copy of `w` words from the working space to `pre` at `pre + 8 d`,
`d ≤ w`: the working space is as it was. -/
theorem pcCopy_ok {q : PcPub × BitVec 64} {s : State} (h : PcO q s) {e d : Nat} (hd : d ≤ q.1.w)
    (he : e + 8 * q.1.w ≤ q.1.Z) (h16 : s.gpr .x16 = off q.1.B e) (h17 : s.gpr .x17 = off q.1.op (8 * d))
    (h12 : s.gpr .x12 = BitVec.ofNat 64 q.1.w) :
    WP isa copyWords s fun t => PcO q t ∧ t.gpr .x17 = off q.1.op (8 * d + 8 * q.1.w) ∧
      Keep [.x3, .x14, .x16, .x17] s t := by
  obtain ⟨hg, hw, hw', hO, hpw, hps⟩ := h
  have hs : Scr s q.1.B q.1.Z := hg.1.scr
  have hn := hs.nowrap
  have hZ : slot q.1.w 8 ≤ q.1.Z := hg.2
  have hsep : ∀ x, ofs q.1.B x < q.1.Z → 16 * q.1.w ≤ ofs q.1.op x := fun x hx => le_ofs_of_sep hps hx
  refine WP.mono (copyWords_ok h16 h17 h12 (by omega_arith) (by omega_arith) (by omega_arith)
    (fun j hj => hs.ld (by omega_arith))
    (fun j hj => by rw [show 8 * d + 8 * j = 8 * (d + j) by omega_arith]; exact hpw (d + j) (by omega_arith))
    (fun j hj b hb => Or.inr (Nat.le_trans (by omega_arith)
      (hsep _ (by rw [ofs_off q.1.B (d := e + 8 * j) (i := b) (by omega_arith)]; omega_arith)))))
    fun t ⟨_, _, ho, _, h17', k⟩ => ?_
  have hi : ∀ x, ofs q.1.B x < q.1.Z → t.mem x = s.mem x := fun x hx =>
    ho x (Or.inr (by have := hsep x hx; omega_arith))
  refine ⟨⟨⟨Good.of_inScr (hg.1 : Good s q.1.B q.1.Z q.1.w q.2) hZ hi k.wr
    ((k.gpr .x0 (by decide)).trans hg.1.x0), hZ⟩, hw, hw', ?_,
    fun i hi' => by rw [k.wr]; exact hpw i hi', hps⟩, h17', k⟩
  rw [← hO]
  exact Mem.readW_congr fun b hb => hi _ (by
    have := hdr_lt_slot q.1.w 0 (show 31 < 32 by decide)
    have := slot_le (w := q.1.w) (show 0 < 8 by decide)
    rw [ofs_off q.1.B (d := 8 * sOut) (i := b) (by unfold sOut sFn; omega_arith)]; unfold sOut sFn; omega_arith)

theorem PcO.mem {q : PcPub × BitVec 64} {s t : State} (h : PcO q s) (hm : t.mem = s.mem)
    {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs) : PcO q t := by
  obtain ⟨hg, hw, hw', hO, hpw, hps⟩ := h
  exact ⟨⟨Good.of_inScr (hg.1 : Good s q.1.B q.1.Z q.1.w q.2) hg.2 (fun x _ => by rw [hm]) k.wr
    ((k.gpr .x0 hr).trans hg.1.x0), hg.2⟩, hw, hw', by rw [hm]; exact hO,
    fun i hi => by rw [k.wr]; exact hpw i hi, hps⟩

/-- The copies to `pre` leak the same in runs with the same working space and
`pre`. -/
theorem pcOut_ct : RelCT isa (Two PcO) (seqs Precompute.pcOut) fun _ _ => True := by
  unfold Precompute.pcOut
  -- The first copy's registers.
  refine RelCT.seq (two_piece (Ψ := PcO1) _ pins_PcO (by taint_decide) ?_) ?_
  · intro q s h
    have hs : Scr s q.1.B q.1.Z := h.1.1.scr
    have hZ : slot q.1.w 8 ≤ q.1.Z := h.1.2
    obtain ⟨g0, g8⟩ := slot0_ge q.1.w
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off q.1.B (8 * i)) 8 := fun i hi => hs.ld (by omega_arith)
    refine WP.mono (WP.keep [.x12, .x16, .x17] (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 q.1.w ∧
        t.gpr .x16 = off q.1.B (slot q.1.w aN) ∧ t.gpr .x17 = off q.1.op 0 ∧ t.mem = s.mem) (by
      brun [h.1.1.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show sArr aN < 32 by decide),
        hdr_enc (show sOut < 32 by decide), hl sW (by decide), hl (sArr aN) (by decide), hl sOut (by decide),
        h.1.1.hdr.hw, h.1.1.hdr.harr aN (by decide), h.2.2.2.1]) (by decide) (by decide) (by decide +kernel))
      fun t ⟨⟨h12, h16, h17, hm⟩, k⟩ => ⟨h.mem hm k (by decide), h12, h16, h17⟩
  -- The first copy.
  refine RelCT.seq (two_piece (Ψ := PcO2) [.x16, .x17, .x12] (fun q s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
    · rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_) ?_
  · rintro q s ⟨h, h12, h16, h17⟩
    have := slot_le (w := q.1.w) (show aN < 8 by decide)
    have hZ : slot q.1.w 8 ≤ q.1.Z := h.1.2
    exact WP.mono (pcCopy_ok h (d := 0) (by omega_arith) (by omega_arith) h16 (by rw [h17]) h12)
      fun t ⟨h', h17', k⟩ => ⟨h', (k.gpr .x12 (by decide)).trans h12, by rw [h17']; congr 1; omega_arith⟩
  -- The second copy's registers.
  refine RelCT.seq (two_piece (Ψ := PcO3) _ (fun q s₁ s₂ h₁ h₂ => pins_PcO q s₁ s₂ h₁.1 h₂.1)
    (by taint_decide) ?_) ?_
  · rintro q s ⟨h, h12, h17⟩
    have hs : Scr s q.1.B q.1.Z := h.1.1.scr
    have hZ : slot q.1.w 8 ≤ q.1.Z := h.1.2
    obtain ⟨g0, g8⟩ := slot0_ge q.1.w
    refine WP.mono (WP.keep [.x16] (Q := fun t => t.gpr .x16 = off q.1.B (slot q.1.w aR2) ∧ t.mem = s.mem) (by
      brun [h.1.1.x0, hdr_enc (show sArr aR2 < 32 by decide), hs.ld (d := 8 * sArr aR2) (by unfold sArr aR2; omega_arith),
        h.1.1.hdr.harr aR2 (by decide)]) (by decide) (by decide) (by decide +kernel))
      fun t ⟨⟨h16, hm⟩, k⟩ => ⟨h.mem hm k (by decide), (k.gpr .x12 (by decide)).trans h12, h16,
        (k.gpr .x17 (by decide)).trans h17⟩
  -- The second copy and the return.
  exact two_taint [.x16, .x17, .x12, .x0] (fun q s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2, h₂.2.2.2]
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.1.1.1.x0, h₂.1.1.1.x0]) (by taint_decide)

/-- `main` leaks the same in runs that agree on the public data and `n`. -/
theorem pcMain_ct (M : Mont) : RelCT isa (Two PcM) (Precompute.main M.mm) fun _ _ => True := by
  rw [pcMain_eq M]
  refine RelCT.seqs_append (by simp [pcLoadW, pcLoadWith]) (by simp [r2StepsPub]) (RelCT.seq (R := Two Pc3)
    (two_post (pcLoadW_ct.mono (fun _ _ h => two_mono (fun _ _ h => PcM.loadW h) h) fun _ _ _ => trivial)
      fun p s h => ?_) ?_)
  · have h' := h
    obtain ⟨hs, h0, hZ, hk1, hk2, -, hK, hN, hn, hnl, hv, -, -, hsp⟩ := h'
    refine WP.mono (pcLoadW_r2 hs h0 hZ hk1 hk2 hK hN hn hsp hnl hv) fun t ⟨mi, hr, f, k⟩ =>
      ⟨mi, h.congr f (fun r hr => Nat.le_trans (pcLoadRanges_le _ r hr) hZ) (pcLoadRanges_fixed _) k (by decide), hr⟩
  exact RelCT.seqs_append (by simp [r2StepsPub]) (by simp [Precompute.pcOut]) (RelCT.seq (pcR2_ct M) pcOut_ct)

/-! ## The whole function -/

/-- A state the contract allows, with the public data `p`. -/
def PcC (p : PcPub) (s : State) : Prop :=
  pcContract.pre s ∧ s.gpr .x4 = p.B ∧ (s.gpr .x5).toNat * 8 = p.Z ∧ (s.gpr .x3).toNat = p.k ∧
    s.gpr .x0 = p.op ∧ s.gpr .x2 = p.np ∧ Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat = p.nb

/-- After the entry and the modulus' check. -/
def PcC3 (p : PcPub) (t : State) : Prop :=
  Scr t p.B p.Z ∧ t.gpr .x0 = p.B ∧ slot p.w 8 ≤ p.Z ∧ 64 ≤ p.k ∧ p.k ≤ 1024 ∧
    word t.mem p.B (8 * sOut) = p.op ∧ word t.mem p.B (8 * sK) = BitVec.ofNat 64 p.k ∧
    word t.mem p.B (8 * sN) = p.np ∧ Src t p.B p.Z p.np p.nb ∧ p.nb.length = p.k ∧
    (∀ i < 2 * p.w, InRegions t.wr (off p.op (8 * i)) 8) ∧
    (∀ i < 16 * p.w, p.Z ≤ ofs p.B (p.op + BitVec.ofNat 64 i)) ∧
    t.gpr .x9 = BitVec.ofNat 64 (Spec.Rsa.modulusValid p.N p.k).toNat ∧ InRegions (t.rd ++ t.wr) p.np p.k

/-- `vg_rsa_public_precompute` leaks the same in runs that agree on the public
data and `n`. -/
theorem pcCode_ct (M : Mont) : RelCT isa (Two PcC) (Precompute.code M.mm) fun _ _ => True := by
  unfold Precompute.code
  refine RelCT.seq (two_piece (Ψ := PcC3) [.x4, .x2, .x3] (fun p s₁ s₂ h₁ h₂ r hr => by
    obtain ⟨-, a₁, -, c₁, -, d₁, -⟩ := h₁
    obtain ⟨-, a₂, -, c₂, -, d₂, -⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [a₁, a₂]
    · rw [d₁, d₂]
    · rw [← ofNat_toNat64 (s₁.gpr .x3), ← ofNat_toNat64 (s₂.gpr .x3), c₁, c₂]) (by taint_decide) ?_) ?_
  · rintro ⟨B, Z, k, op, np, nb⟩ s ⟨hs, hB, hZ, hk, hop, hnp, hnb⟩
    have c := pcCtx_of hs
    have hZ' := c.hZ
    have hk1 := c.hk1
    have hk2 := c.hk2
    have hn := c.hs.nowrap
    rw [WP.block_append_iff]
    refine WP.mono (pcEntry_ok rfl fun i hi => c.hs.st (by omega_arith)) fun t₁ ⟨h0, hO, hN, hK, ho₁, k₁⟩ => ?_
    have i₁ : InScr (s.gpr .x4) ((s.gpr .x5).toNat * 8) s.mem t₁.mem := InScr.of_outside ho₁ (by omega_arith)
    have hnb₁ := c.hnb.congrK i₁ k₁
    refine WP.mono (WP.keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] (invalid_ok (k₁.gpr .x2 (by decide))
      (by rw [k₁.gpr .x3 (by decide), ofNat_toNat64]) hk1 hk2
      (bytesAt_length _ _ _) (fun i hi => hnb₁.rd i (by rw [bytesAt_length]; exact hi))
      (fun i hi => hnb₁.val i _)) (by decide) (by decide) (by decide +kernel))
      fun t₂ ⟨⟨hz₂, hm₂, _⟩, k₂⟩ => ?_
    have kk := k₁.trans k₂
    subst hB hZ hk hop hnp hnb
    exact ⟨c.hs.congr kk.wr, (k₂.gpr .x0 (by decide)).trans h0,
      show slot (((s.gpr .x3).toNat + 7) / 8) 8 ≤ (s.gpr .x5).toNat * 8 by unfold slot hdrBytes; omega_arith, hk1, hk2,
      by rw [hm₂]; exact hO, by rw [hm₂, hK, ofNat_toNat64], by rw [hm₂]; exact hN,
      c.hnb.congrK (by rw [hm₂]; exact i₁) kk, bytesAt_length _ _ _,
      fun i hi => by rw [kk.wr]; exact c.hpw i hi, c.hps, hz₂, by rw [kk.rd, kk.wr]; exact c.hnspan⟩
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by
    rw [eval_zero, eval_zero, h₁.2.2.2.2.2.2.2.2.2.2.2.2.1, h₂.2.2.2.2.2.2.2.2.2.2.2.2.1]) ?_ ?_
  · -- `fail`.
    unfold Precompute.fail
    refine RelCT.seq (two_piece (Ψ := fun p t => t.gpr .x1 = off p.op 0 ∧
        t.gpr .x2 = BitVec.ofNat 64 (2 * p.w)) [.x0] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.2.1, h₂.1.2.1]) (by taint_decide) ?_)
      (two_taint [.x1, .x2] (fun p s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) (by taint_decide))
    rintro p t ⟨⟨hs, h0, hZ, hk1, hk2, hO, hK, -⟩, -⟩
    obtain ⟨g0, g8⟩ := slot0_ge p.w
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off p.B (8 * i)) 8 := fun i hi => hs.ld (by omega_arith)
    refine WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t' => t'.gpr .x1 = off p.op 0 ∧
        t'.gpr .x2 = BitVec.ofNat 64 (2 * p.w)) (by
      brun [h0, hdr_enc (show sOut < 32 by decide), hdr_enc (show sK < 32 by decide), hl sOut (by decide),
        hl sK (by decide), hO, hK, two_w p.k (by omega_arith)]) (by decide) (by decide) (by decide +kernel))
      fun t' ⟨h, _⟩ => h
  · -- `main`.
    refine two_map id (fun p t ⟨⟨hs, h0, hZ, hk1, hk2, hO, hK, hN, hnb, hnl, hpw, hps, hz, hsp⟩, he⟩ =>
      ⟨hs, h0, hZ, hk1, hk2, hO, hK, hN, hnb, hnl, ?_, hpw, hps, hsp⟩) (pcMain_ct M)
    rw [eval_zero, hz] at he
    cases hv : Spec.Rsa.modulusValid p.N p.k
    · rw [hv] at he; simp at he
    · exact hv

/-- The public data of a state. -/
def pcPubOf (s : State) : PcPub :=
  ⟨s.gpr .x4, (s.gpr .x5).toNat * 8, (s.gpr .x3).toNat, s.gpr .x0, s.gpr .x2,
    Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat⟩

/-- `vg_rsa_public_precompute` is constant time but for `n`. -/
theorem pcCode_constantTime (M : Mont) :
    ConstantTime isa pcContract.pre pcContract.pub (Precompute.code M.mm) := by
  refine RelCT.constantTime ((pcCode_ct M).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨pcPubOf s₁, ?_, ?_, hp.1⟩)
    fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨-, hl, h0, -, h2, h3, h4, h5⟩ := hp
    have hn := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl
    exact ⟨h₂, h4.symm, congrArg (fun x : BitVec 64 => x.toNat * 8) h5.symm, congrArg BitVec.toNat h3.symm,
      h0.symm, h2.symm, hn.symm⟩

end VG.Proof.Bignum.AArch64
