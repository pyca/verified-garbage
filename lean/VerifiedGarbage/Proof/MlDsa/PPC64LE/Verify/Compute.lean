module

public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.SampA
import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Steps

/-!
# ML-DSA verification on PPC64LE: after the samplers

As on 32-bit ARM (`Proof/MlDsa/Arm/Verify/Compute.lean`): once the samplers
are done, with `Â` and `c` in memory as `A'` and `cc` and `r24` as `R`, the
rest of the function computes `w′₁` from them, whatever they are (`KC5`);
which writes keep it (`K5Chk`, `k5chks`); and the NTTs of `z` and `c`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Verify

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv Callee ip_ok ip_tr
  polyIs_keepW polyAt_keepW reduced_keepW bytes_keepW keepD)
open VG.Impl.MlDsa.PPC64LE.Verify
open VG.Spec.MlDsa (Params toRq ntt simpleBitPack)
open VG.Proof.MlDsa (HintIs PolyIs polyAt Reduced)
open VG.Proof.MlDsa.Verify (vZ zHat w1Row)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-- What the samplers give, with `R` their result: `A'` and `cc` those of the
standard for some bounds if `R` is 1, and a sampler failing within the least
bounds if 0. -/
def Gd (p : Params) (σ : State) (A' : Nat → Nat → Spec.MlDsa.Poly) (cc : Spec.MlDsa.Poly) (R : BitVec 64) : Prop :=
  ∃ q : Bool, R = flag q ∧
    (q = true → (∀ r < p.k, ∀ s' < p.ℓ, ∃ b : Nat,
      Spec.MlDsa.rejNTTPoly b (Proof.MlDsa.Verify.aSeed (pkOf p σ) r s') = some (A' r s')) ∧
      ∃ b : Nat, (Spec.MlDsa.sampleInBall p.τ b (Proof.MlDsa.Verify.vCt p (sgOf p σ))).map toRq = some cc) ∧
    (q = false → (∃ r < p.k, ∃ s' < p.ℓ, Spec.MlDsa.rejNTTPoly Spec.MlDsa.minBounds.rejNTT
      (Proof.MlDsa.Verify.aSeed (pkOf p σ) r s') = none) ∨
      Spec.MlDsa.sampleInBall p.τ Spec.MlDsa.minBounds.ball (Proof.MlDsa.Verify.vCt p (sgOf p σ)) = none)

/-- After the samplers: `w′₁` from `A'` and `cc`, so far. -/
structure KC5 (p : Params) (STK : Nat) (σ : State) (A' : Nat → Nat → Spec.MlDsa.Poly) (cc : Spec.MlDsa.Poly)
    (h : List (Vector Bool Spec.MlDsa.n)) (R : BitVec 64) (nz : Nat) (nc : Bool) (nr : Nat) (s : State) : Prop where
  vc : VC p STK σ s
  hh : hintOf p σ = some h
  hint : HintIs s.mem ((vlay p STK σ).A 0 (oP 0)) p.k h
  a : ∀ r < p.k, ∀ s' < p.ℓ, PolyIs s.mem (aA p STK σ r s') (A' r s')
  z : ∀ i < p.ℓ, PolyIs s.mem ((vlay p STK σ).A 0 (oP (8 + i)))
    (if i < nz then zHat p (sgOf p σ) i else toRq (vZ p (sgOf p σ) i))
  c : PolyIs s.mem ((vlay p STK σ).A 0 (oP 15)) (if nc then ntt cc else cc)
  rows : ∀ r < nr, bytesAt s.mem ((vlay p STK σ).A 0 (oB + w1Len p * r)) (w1Len p) =
    simpleBitPack (w1Row p (pkOf p σ) (sgOf p σ) A' (ntt cc) h r) (w1Max p)
  r24 : s.gpr .r24 = R
  gd : Gd p σ A' cc R

/-- A part that writes `W` keeps what `KC5` says of the polynomials it does not write. -/
structure K5Chk (p : Params) (STK : Nat) (nr : Nat) (W : List (Nat × Nat × Nat)) : Prop where
  vc : vcChk p STK W = true
  hint : sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP 0, 1024 * p.k) W = true
  a : ∀ r < p.k, ∀ s' < p.ℓ, sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP (20 + 8 * r + s'), 1024) W = true
  z : ∀ i < p.ℓ, sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP (8 + i), 1024) W = true
  c : sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP 15, 1024) W = true
  rows : ∀ r < nr, sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oB + w1Len p * r, w1Len p) W = true

/-- Proves a `K5Chk`, in each case of `w1Len`. -/
tactic_template "k5chk " hF:term:max : tactic => `(tactic| (
      rcases ($hF).w1l with hw1 | ⟨hw1, _⟩ <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> vsep $hF [vcChk, hw1]))

theorem sepAll_append {sz : List Nat} {a : Nat × Nat × Nat} {W₁ W₂ : List (Nat × Nat × Nat)}
    (h₁ : sepAll sz a W₁ = true) (h₂ : sepAll sz a W₂ = true) : sepAll sz a (W₁ ++ W₂) = true := by
  simp only [sepAll, List.all_append, Bool.and_eq_true] at *
  exact ⟨h₁, h₂⟩

theorem vcChk_append {p : Params} {STK : Nat} {W₁ W₂ : List (Nat × Nat × Nat)} (h₁ : vcChk p STK W₁ = true)
    (h₂ : vcChk p STK W₂ = true) : vcChk p STK (W₁ ++ W₂) = true := by
  simp only [vcChk, List.all_append, Bool.and_eq_true] at *
  exact ⟨⟨⟨⟨sepAll_append h₁.1.1.1.1 h₂.1.1.1.1, h₁.1.1.1.2, h₂.1.1.1.2⟩, sepAll_append h₁.1.1.2 h₂.1.1.2⟩,
    sepAll_append h₁.1.2 h₂.1.2⟩, sepAll_append h₁.2 h₂.2⟩

/-- The checks of two parts of writes, for both. -/
theorem K5Chk.append {p : Params} {STK nr : Nat} {W₁ W₂ : List (Nat × Nat × Nat)} (h₁ : K5Chk p STK nr W₁)
    (h₂ : K5Chk p STK nr W₂) : K5Chk p STK nr (W₁ ++ W₂) :=
  ⟨vcChk_append h₁.vc h₂.vc, sepAll_append h₁.hint h₂.hint,
    fun r hr s hs => sepAll_append (h₁.a r hr s hs) (h₂.a r hr s hs), fun i hi => sepAll_append (h₁.z i hi) (h₂.z i hi),
    sepAll_append h₁.c h₂.c, fun r hr => sepAll_append (h₁.rows r hr) (h₂.rows r hr)⟩

/-! `K5Chk` of the writes of a part, from those of each region, each proved once for
any region (`k5chk` on a literal list of writes costs seconds). -/

theorem K5Chk.nil {p : Params} (_ : VFacts p) {STK nr : Nat} (_ : nr ≤ p.k) : K5Chk p STK nr [] :=
  ⟨rfl, rfl, fun _ _ _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ => rfl⟩

theorem K5Chk.stk {p : Params} (hF : VFacts p) {STK nr : Nat} (hnr : nr ≤ p.k) : K5Chk p STK nr [(1, 0, STK)] := by
  k5chk hF

/-- A write to `scratch` apart from what `KC5` holds. -/
theorem K5Chk.c0 {p : Params} (hF : VFacts p) {STK nr : Nat} (hnr : nr ≤ p.k) {o n : Nat}
    (h1 : o + n ≤ 840 ∨ 912 ≤ o) (h2 : o + n ≤ oB ∨ oB + w1Len p * nr ≤ o) (h3 : o + n ≤ oP 0 ∨ oP 8 ≤ o)
    (h4 : o + n ≤ oP 8 ∨ oP 16 ≤ o) (h5 : o + n ≤ oP 20) : K5Chk p STK nr [(0, o, n)] := by
  simp only [oB, oP] at h2 h3 h4 h5
  rcases hF.w1l with hw1 | ⟨hw1, _⟩ <;> rw [hw1] at h2 <;>
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> vsep hF [vcChk, hw1]

theorem K5Chk.cons_c0 {p : Params} (hF : VFacts p) {STK nr : Nat} (hnr : nr ≤ p.k) {o n : Nat}
    {W : List (Nat × Nat × Nat)}
    (h1 : o + n ≤ 840 ∨ 912 ≤ o) (h2 : o + n ≤ oB ∨ oB + w1Len p * nr ≤ o ∨ oB + 1024 ≤ o)
    (h3 : o + n ≤ oP 0 ∨ oP 8 ≤ o) (h4 : o + n ≤ oP 8 ∨ oP 16 ≤ o) (h5 : o + n ≤ oP 20) (h : K5Chk p STK nr W) :
    K5Chk p STK nr ((0, o, n) :: W) := by
  have : w1Len p * nr ≤ 1024 := by
    have := Nat.mul_le_mul_left (w1Len p) hnr; rw [Nat.mul_comm (w1Len p) p.k] at this; have := hF.w1; omega
  exact (K5Chk.c0 hF hnr h1 (by omega) h3 h4 h5).append (W₁ := [_]) h

theorem K5Chk.cons_stk {p : Params} (hF : VFacts p) {STK nr : Nat} (hnr : nr ≤ p.k) {W : List (Nat × Nat × Nat)}
    (h : K5Chk p STK nr W) : K5Chk p STK nr ((1, 0, STK) :: W) :=
  (K5Chk.stk hF hnr).append (W₁ := [_]) h

/-- Proves a `K5Chk` of writes to `scratch` and the stack, with `hnr : nr ≤ p.k`. -/
tactic_template "k5chks " hF:term:max hnr:term:max : tactic => `(tactic| (
                   repeat' (first
                     | with_reducible exact VG.Proof.MlDsa.PPC64LE.Verify.K5Chk.nil $hF $hnr
                     | apply VG.Proof.MlDsa.PPC64LE.Verify.K5Chk.cons_stk $hF $hnr
                     | apply VG.Proof.MlDsa.PPC64LE.Verify.K5Chk.cons_c0 $hF $hnr)
                   all_goals (
                     have := ($hF).w1.1; have := ($hF).k; have := ($hF).l
                     try simp only [VG.Impl.MlDsa.PPC64LE.Verify.oP, VG.Impl.MlDsa.PPC64LE.Verify.oB, VG.Impl.MlDsa.PPC64LE.Verify.oSS,
                       VG.Impl.MlDsa.PPC64LE.Verify.oCT]
                     omega_arith)))

theorem KC5.keep {p : Params} (hF : VFacts p) {STK : Nat} {σ : State} {A' : Nat → Nat → Spec.MlDsa.Poly}
    {cc : Spec.MlDsa.Poly} {h : List (Vector Bool Spec.MlDsa.n)} {R : BitVec 64} {nz : Nat} {nc : Bool} {nr : Nat}
    {s s' : State} (hk5 : KC5 p STK σ A' cc h R nz nc nr s) {W : List (Nat × Nat × Nat)}
    (hk : Kept ((vlay p STK σ).RL W) s s') (hc : K5Chk p STK nr W) : KC5 p STK σ A' cc h R nz nc nr s' := by
  have hL := hk5.vc.site.ok
  have hle : w1Len p ≤ 2 ^ 64 := by rcases hF.w1l with e | ⟨e, _⟩ <;> omega
  exact ⟨hk5.vc.keep hk hc.vc, hk5.hh, hintIs_keepW hL hk.frame hc.hint (by decide) (by have := hF.k; omega) hk5.hint,
    fun r hr s' hs' => polyIs_keepW hL hk.frame (hc.a r hr s' hs') (by decide) rfl (hk5.a r hr s' hs'),
    fun i hi => polyIs_keepW hL hk.frame (hc.z i hi) (by decide) rfl (hk5.z i hi),
    polyIs_keepW hL hk.frame hc.c (by decide) rfl hk5.c,
    fun r hr => by rw [bytes_keepW hL hk.frame (hc.rows r hr) (by decide) hle]; exact hk5.rows r hr,
    (hk.cs .r24 (by decide)).trans hk5.r24, hk5.gd⟩

/-- The states of `compute` with `nz`, `nc` and `nr`, for some `A'`, `cc`, `h` and `R`. -/
abbrev KX (p : Params) (STK : Nat) (nz : Nat) (nc : Bool) (nr : Nat) (σ s : State) : Prop :=
  ∃ A' cc h R, KC5 p STK σ A' cc h R nz nc nr s

/-! ## The NTTs of `z` and `c` -/

section
variable {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

theorem nttZ_ok {j : Nat} (hj : j < p.ℓ) {σ : State} {A' cc h R} {s : State}
    (hk5 : KC5 p STK σ A' cc h R j false 0 s) : WP isa (nttAt P (pZ j)) s (KC5 p STK σ A' cc h R (j + 1) false 0) := by
  have hk := hF.k; have hl := hF.l
  have hs := hk5.vc.site
  have hL := hs.ok
  have hz := hk5.z j hj
  rw [ifn (Nat.lt_irrefl j)] at hz
  unfold nttAt
  refine ip_ok (t := ntt) hP.ntt hs hS (f := pZ j) (w := sc oSS) ⟨⟨vptr_ok rfl (by unfold oP; omega), by vsep hF⟩,
    ⟨vptr_ok rfl (by decide), by vsep hF⟩, show ix Reg.r31 ∈ vWb by decide, show ix Reg.r31 ∈ vWb by decide,
    by vsep hF⟩ hz.1 fun s' k' hb => ?_
  refine ⟨hk5.vc.keep k' (by vsep hF [vcChk]), hk5.hh,
    hintIs_keepW hL k'.frame (by vsep hF) (by decide) (by omega) hk5.hint,
    fun r hr s' hs' => polyIs_keepW hL k'.frame (by vsep hF) (by decide) rfl (hk5.a r hr s' hs'),
    fun i hi => ?_, polyIs_keepW hL k'.frame (by vsep hF) (by decide) rfl hk5.c,
    fun _ h => absurd h (Nat.not_lt_zero _), (k'.cs .r24 (by decide)).trans hk5.r24, hk5.gd⟩
  by_cases e : i = j
  · subst e
    rw [ifp (Nat.lt_succ_self _)]
    show PolyIs s'.mem (lpa (vlay p STK σ) (pZ i)) _
    have e2 : polyAt s.mem (lpa (vlay p STK σ) (pZ i)) = _ := hz.2
    rw [e2] at hb
    exact hb
  · have := polyIs_keepW hL k'.frame (i := 0) (o := oP (8 + i)) (by vsep hF) (by decide) rfl (hk5.z i hi)
    by_cases hlt : i < j
    · rwa [ifp hlt, ← ifp (show i < j + 1 by omega) (zHat p (sgOf p σ) i) (toRq (vZ p (sgOf p σ) i))] at this
    · rwa [ifn hlt, ← ifn (show ¬ i < j + 1 by omega) (zHat p (sgOf p σ) i) (toRq (vZ p (sgOf p σ) i))] at this

theorem nttZ_piece {j : Nat} (hj : j < p.ℓ) :
    VPiece p STK (KX p STK j false 0) (KX p STK (j + 1) false 0) (nttAt P (pZ j)) := by
  have hl := hF.l
  refine ⟨fun _ _ _ ⟨A', cc, h, R, hk5⟩ => WP.mono (nttZ_ok hP hF hS hj hk5) fun _ h' => ⟨A', cc, h, R, h'⟩, ?_⟩
  unfold nttAt
  refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
    Reduced x.mem (lpa (vlay p STK σ) (pZ j)) ∧ Reduced y.mem (lpa (vlay p STK σ) (pZ j)))
    (RelCT.exists_ fun σ => ip_tr (t := ntt) hP.ntt hS (f := pZ j) (w := sc oSS)
      (⟨⟨vptr_ok rfl (by unfold oP; omega), by vsep hF⟩, ⟨vptr_ok rfl (by decide), by vsep hF⟩,
        show ix Reg.r31 ∈ vWb by decide, show ix Reg.r31 ∈ vWb by decide, by vsep hF⟩ : KeyGen.IpOk (vlay p STK σ) vWb _ _)
      fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩)
    fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => ?_
  have r₂ : Reduced _ (lpa (vlay p STK _) (pZ j)) := (h₂.z j hj).1
  rw [← vlay_pub pub] at r₂
  exact ⟨σ₁, vc_twoL pub h₁.vc h₂.vc, (h₁.z j hj).1, r₂⟩

theorem nttC_ok {σ : State} {A' cc h R} {s : State} (hk5 : KC5 p STK σ A' cc h R p.ℓ false 0 s) :
    WP isa (nttAt P pC) s (KC5 p STK σ A' cc h R p.ℓ true 0) := by
  have hk := hF.k; have hl := hF.l
  have hs := hk5.vc.site
  have hL := hs.ok
  unfold nttAt
  refine ip_ok (t := ntt) hP.ntt hs hS (f := pC) (w := sc oSS) ⟨⟨vptr_ok rfl (by decide), by vsep hF⟩,
    ⟨vptr_ok rfl (by decide), by vsep hF⟩, show ix Reg.r31 ∈ vWb by decide, show ix Reg.r31 ∈ vWb by decide,
    by vsep hF⟩ hk5.c.1 fun s' k' hb => ?_
  refine ⟨hk5.vc.keep k' (by vsep hF [vcChk]), hk5.hh,
    hintIs_keepW hL k'.frame (by vsep hF) (by decide) (by omega) hk5.hint,
    fun r hr s' hs' => polyIs_keepW hL k'.frame (by vsep hF) (by decide) rfl (hk5.a r hr s' hs'),
    fun i hi => polyIs_keepW hL k'.frame (by vsep hF) (by decide) rfl (hk5.z i hi), ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), (k'.cs .r24 (by decide)).trans hk5.r24, hk5.gd⟩
  show PolyIs s'.mem (lpa (vlay p STK σ) pC) _
  have e2 : polyAt s.mem (lpa (vlay p STK σ) pC) = cc := hk5.c.2
  rw [e2] at hb
  exact hb

theorem nttC_piece : VPiece p STK (KX p STK p.ℓ false 0) (KX p STK p.ℓ true 0) (nttAt P pC) := by
  refine ⟨fun _ _ _ ⟨A', cc, h, R, hk5⟩ => WP.mono (nttC_ok hP hF hS hk5) fun _ h' => ⟨A', cc, h, R, h'⟩, ?_⟩
  unfold nttAt
  refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
    Reduced x.mem (lpa (vlay p STK σ) pC) ∧ Reduced y.mem (lpa (vlay p STK σ) pC))
    (RelCT.exists_ fun σ => ip_tr (t := ntt) hP.ntt hS (f := pC) (w := sc oSS)
      (⟨⟨vptr_ok rfl (by decide), by vsep hF⟩, ⟨vptr_ok rfl (by decide), by vsep hF⟩,
        show ix Reg.r31 ∈ vWb by decide, show ix Reg.r31 ∈ vWb by decide, by vsep hF⟩ : KeyGen.IpOk (vlay p STK σ) vWb _ _)
      fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩)
    fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => ?_
  have r₂ : Reduced _ (lpa (vlay p STK _) pC) := h₂.c.1
  rw [← vlay_pub pub] at r₂
  exact ⟨σ₁, vc_twoL pub h₁.vc h₂.vc, h₁.c.1, r₂⟩

end

end VG.Proof.MlDsa.PPC64LE.Verify
