module
-- separate module: the proof of Appendix C.2's body is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Rsa.Arm.Stage.Prod
import VerifiedGarbage.Proof.Rsa.ProductExact
import VerifiedGarbage.Proof.Rsa.Arm.Stage.MM
import VerifiedGarbage.Proof.Rsa.Arm.Stage.KS
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ctx
import VerifiedGarbage.Proof.Rsa.Arm.MulMod
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops2
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Ops
public import VerifiedGarbage.Proof.Rsa.Arm.RdOps
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
public import VerifiedGarbage.Proof.Rsa.Arm.RdTaint
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Tools
import VerifiedGarbage.Proof.Rsa.TwosMath
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # `vg_rsa_recover_primes_det` on ARMv7: `d e - 1` and the halvings

From the product `d e` (`RecoverDet.prodW`): `x = d e - 1` and whether `d e ≥ 2`
(`deMinus_vp`); then `u = n - 1` and the `32 w` halvings (`twos_vp`), whose
step is any `f` with the halvings' formula (Appendix C.2's model,
`Proof/Rsa/RecoverDet.lean`, calls it `twoStep`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

/-- `M = d e`. -/
abbrev Mv (P : RP) (σ : State) : Nat := dv P σ * P.e

/-- The arrays with `W` words after the product. -/
def AWp (P : RP) (σ : State) : Nat → Nat := upd (AW1 P σ) wM (Mv P σ)

end VG.Proof.Rsa.Arm.Recover

namespace VG.Proof.Rsa.Arm.RecoverDet
open VG VG.Arm VG.Proof.Mont VG.Proof.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Recover
open VG.Impl.Rsa.Arm.Keys hiding aT1 aT2 aT3 aT4
open VG.Proof.X25519.Arm
open VG.Impl.Rsa.Arm.RecoverDet
open VG.Impl.Rsa.Arm.Recover (nArr)
open VG.Proof.Rsa (sub32 b2n)

/-- A stage: `E`, the key working space, and its context with `v` words. -/
abbrev Dk (P : RP) (E : State → Prop) (A : State → Nat → Nat) (L : List Nat) (AW : State → Nat → Nat)
    (LW : List Nat) (V : State → Nat → Nat) (LS : List Nat) (v N : Nat) (σ s : State) : Prop :=
  E σ ∧ KS P σ (A σ) L (AW σ) LW (V σ) LS s ∧ Ws s P.B P.Z v N

/-- `d e`, `d e - 1` modulo `2^(32 W)`, and whether `d e ≥ 2`. -/
abbrev deV (P : RP) (σ : State) : Nat := Mv P σ
abbrev xV (P : RP) (σ : State) : Nat := sub32 P.W (deV P σ) 1
abbrev okDEv (P : RP) (σ : State) : Bool := !(decide (deV P σ < 1) || decide (xV P σ < 1))

/-- After `deMinus`. -/
def AN (P : RP) : Nat → Nat := upd (fun _ => 0) aN P.n
def AW1 (P : RP) (σ : State) : Nat → Nat := upd (upd (upd (fun _ => 0) wZ 0) wOne 1) wX (xV P σ)
def V1 (P : RP) (σ : State) : Nat → Nat := upd (fun _ => 0) sOkDE (b2n (okDEv P σ))

section
variable {P : RP}

theorem ws_regs' {s₁ s₂ : State} {v N : Nat} (h₁ : Ws s₁ P.B P.Z v N) (h₂ : Ws s₂ P.B P.Z v N) :
    ∀ r ∈ ctxRegs, s₁.gpr r = s₂.gpr r := by
  simp only [ctxRegs, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · rw [h₁.r7, h₂.r7]
  · rw [h₁.r8, h₂.r8]
  · rw [h₁.r9, h₂.r9]

/-- A piece the taint analysis checks with `r7`–`r9` public, between stages
with the working space's context. -/
theorem VP.dctx {F G : State → State → Prop} {c : Prog isa} {v N : Nat} (cert : DCert c)
    (hws : ∀ σ s, F σ s → Ws s P.B P.Z v N) (wp : ∀ σ s, F σ s → WP isa c s (G σ)) : VP F c G :=
  VP.taint _ cert (fun _ _ _ _ h₁ h₂ => ws_regs' (hws _ _ h₁) (hws _ _ h₂)) wp

theorem b2n_lt_one (p : Prop) [Decidable p] : b2n (decide p) ≤ 1 := by
  unfold b2n; split <;> omega

theorem b2n_nor (p q : Prop) [Decidable p] [Decidable q] :
    (if b2n (decide p) = 0 ∧ b2n (decide q) = 0 then 1 else 0) = b2n (!(decide p || decide q)) := by
  unfold b2n; by_cases a : p <;> by_cases b : q <;> simp [a, b]

theorem deMinus_ok {σ s : State}
    (h : KS P σ (Aload P σ) [VG.Impl.Rsa.Arm.Recover.aN] (AWp P σ)
      [VG.Impl.Rsa.Arm.Recover.wM, VG.Impl.Rsa.Arm.Recover.wZ] (fun _ => 0) [] s)
    (hw : Ws s P.B P.Z P.W 22) :
    WP isa deMinus s fun t => KS P σ (AN P) [aN] (AW1 P σ) [wX, wOne, wZ] (V1 P σ) [sOkDE] t ∧
      Ws t P.B P.Z P.W 22 := by
  simp only [deMinus, seqs]
  refine WP.seq (WP.mono (h.sub_W hw (o := wZ) (a := VG.Impl.Rsa.Arm.Recover.wM)
    (b := VG.Impl.Rsa.Arm.Recover.wM) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun s1 ⟨h1, hw1, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h1.copy_W hw1 (o := wOne) (a := wZ) (by decide) (by decide) (by decide) (by decide))
    fun s2 ⟨h2, hw2, _⟩ => ?_)
  refine WP.seq (h2.setOne_W hw2 (j := wOne) (by decide) (by decide) fun s3 h3 hw3 _ => WP.block_nil ?_)
  refine WP.seq (WP.mono (h3.sub_W hw3 (o := wX) (a := VG.Impl.Rsa.Arm.Recover.wM) (b := wOne) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) fun s4 ⟨h4, hw4, _, c4⟩ => ?_)
  refine WP.seq (h4.brw hw4 (d := sB0) (by decide) fun s5 h5 hw5 _ => WP.block_nil ?_)
  refine WP.seq (WP.mono (h5.sub_W hw5 (o := wT1) (a := wX) (b := wOne) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) fun s6 ⟨h6, hw6, _, c6⟩ => ?_)
  refine h6.brw hw6 (d := sB1) (by decide) fun s7 h7 hw7 _ => ?_
  refine h7.norS hw7 (d := sOkDE) (a := sB0) (b := sB1) (by decide) (by decide)
    (by rw [upd_ne _ _ (by decide), upd_self, c4]; exact b2n_lt_one _)
    (by rw [upd_self, c6]; exact b2n_lt_one _) (by decide) fun t ht hwt => WP.block_nil ⟨?_, hwt⟩
  refine ht.mono (fun j hj => ?_) (fun j hj => ?_) (fun d hd => ?_)
  · simp only [List.mem_singleton] at hj; subst hj
    exact ⟨by decide, by simp only [AN, Aload]; rd_ev⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;> simp only [AW1, AWp, xV, deV] <;> rd_ev <;> simp [sub32]
  · simp only [List.mem_singleton] at hd; subst hd
    refine ⟨by decide, ?_⟩
    rw [upd_self, V1, upd_self, upd_self, upd_ne _ _ (show sB0 ≠ sB1 by decide), upd_self, c4, c6, b2n_nor]
    simp only [okDEv, xV, deV, AWp]
    rd_ev

theorem deMinus_vp {E : State → Prop} :
    VP (fun σ s => E σ ∧ KS P σ (Aload P σ) [VG.Impl.Rsa.Arm.Recover.aN] (AWp P σ)
      [VG.Impl.Rsa.Arm.Recover.wM, VG.Impl.Rsa.Arm.Recover.wZ] (fun _ => 0) [] s ∧
      Ws s P.B P.Z P.W 22) deMinus
      (Dk P E (fun _ => AN P) [aN] (AW1 P) [wX, wOne, wZ] (V1 P) [sOkDE] P.W 22) :=
  VP.dctx deMinus_taint (fun _ _ h => h.2.2) fun _ _ ⟨e, h, hw⟩ =>
    WP.mono (deMinus_ok h hw) fun _ ⟨ht, hwt⟩ => ⟨e, ht, hwt⟩

/-! ## The halvings -/

/-- `(u, x / 2^k, 2^k x)` after `k` halvings from `(n - 1, x mod 2^(32 w), x)`. -/
abbrev ts (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) (k : Nat) : Nat × Nat × Nat :=
  f^[k] (sub32 P.w P.n 1, xV P σ % 2 ^ (32 * P.w), xV P σ)

def AT (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) (k : Nat) : Nat → Nat :=
  upd (upd (upd (upd (upd (fun _ => 0) aOneN 1) aZN 0) aN P.n) aX2 (ts P f σ k).2.1) aU (ts P f σ k).1
def AWT (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) (k : Nat) : Nat → Nat :=
  upd (upd (upd (fun _ => 0) wZ 0) wOne 1) wX3 (ts P f σ k).2.2
def VT (P : RP) (σ : State) (k : Nat) : Nat → Nat :=
  upd (upd (fun _ => 0) sOkDE (b2n (okDEv P σ))) sK (32 * P.w - k)

abbrev LT : List Nat := [aU, aX2, aN, aZN, aOneN]
abbrev LWT : List Nat := [wX3, wOne, wZ]
abbrev LST : List Nat := [sK, sOkDE]

/-- After `k` halvings. -/
def TI (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) (σ : State) (k : Nat) (s : State) : Prop :=
  KS P σ (AT P f σ k) LT (AWT P f σ k) LWT (VT P σ k) LST s ∧ Ws s P.B P.Z P.w nArr

/-- The step of the halvings. -/
abbrev TwoF (P : RP) (f : Nat × Nat × Nat → Nat × Nat × Nat) : Prop :=
  ∀ u x y, f (u, x, y) = if u % 2 = 0 then
    (if x % 2 = 0 then (u / 2, x / 2, 2 * y % 2 ^ (32 * P.W)) else (u / 2, x, y)) else (u, x, y)

/-- A loop of `K ≥ 1` iterations whose body takes the stage `I k` to `I (k + 1)`, with Z when
`K - (k + 1) = 0`. -/
theorem VP.count {E : State → Prop} {I : Nat → State → State → Prop} {body : Prog isa} {K : Nat}
    (pos : 0 < K) (hb : ∀ k, k < K → VP (fun σ s => E σ ∧ I k σ s) body
      (fun σ s => (E σ ∧ I (k + 1) σ s) ∧ s.z = decide (K - (k + 1) = 0))) :
    VP (fun σ s => E σ ∧ I 0 σ s) (.loop body .ne) (fun σ s => E σ ∧ I K σ s) := by
  let J := fun n σ s => E σ ∧ n ≤ K ∧ I (K - n) σ s
  have hl := VP.loop (I := J) (body := body) (c := .ne) (Q := fun σ s => E σ ∧ I K σ s) (fun n => ?_)
  · refine (hl (K - 1)).mono (fun σ s ⟨e, h⟩ => ⟨e, by omega, by rw [show K - (K - 1 + 1) = 0 by omega]; exact h⟩)
      fun _ _ h => h
  · refine (VP.of_imp (p := n + 1 ≤ K) (fun σ s h => h.2.1) fun hn => ?_)
    refine (hb (K - (n + 1)) (by omega)).mono (fun σ s ⟨e, _, h⟩ => ⟨e, h⟩) fun σ s ⟨⟨e, h⟩, z⟩ => ⟨?_, ?_, ?_⟩
    · show some (!s.z) = some (decide (0 < n))
      rw [z, show K - (K - (n + 1) + 1) = n by omega]
      by_cases h0 : n = 0 <;> simp [h0, Nat.pos_iff_ne_zero]
    · intro h0; subst h0; refine ⟨e, ?_⟩; rw [show K - (0 + 1) + 1 = K by omega] at h; exact h
    · intro hp; refine ⟨e, by omega, ?_⟩; rw [show K - (n + 1) + 1 = K - n by omega] at h; exact h

end

end VG.Proof.Rsa.Arm.RecoverDet
