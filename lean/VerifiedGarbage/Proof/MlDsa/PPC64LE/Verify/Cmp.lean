module

import VerifiedGarbage.Proof.MlKem.PPC64LE.CmpSel
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Seeds
import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
import VerifiedGarbage.Proof.MlKem.KPke
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Site
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.SampA
import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Steps
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Seeds
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest
meta import VerifiedGarbage.Proof.MlKem.KPke
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Site
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.SampA
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Steps

/-! ### `MlDsa.PPC64LE.Verify.Hash`, which this module and modules that import it used -/

section

/-! ### `MlDsa.PPC64LE.Verify.Compute`, which this module and modules that import it used -/

section

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
    have := Nat.mul_le_mul_left (w1Len p) hnr; rw [Nat.mul_comm (w1Len p) p.k] at this; have := hF.w1; omega_arith
  exact (K5Chk.c0 hF hnr h1 (by omega_using [h2, this]) h3 h4 h5).append (W₁ := [_]) h

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
  have hle : w1Len p ≤ 2 ^ 64 := by rcases hF.w1l with e | ⟨e, _⟩ <;> omega_using [e]
  exact ⟨hk5.vc.keep hk hc.vc, hk5.hh, hintIs_keepW hL hk.frame hc.hint (by decide) (by have := hF.k; omega_using [this]) hk5.hint,
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
  refine ip_ok (t := ntt) hP.ntt hs hS (f := pZ j) (w := sc oSS) ⟨⟨vptr_ok rfl (by unfold oP; omega_using [hj, hl]), by vsep hF⟩,
    ⟨vptr_ok rfl (by decide), by vsep hF⟩, show ix Reg.r31 ∈ vWb by decide, show ix Reg.r31 ∈ vWb by decide,
    by vsep hF⟩ hz.1 fun s' k' hb => ?_
  refine ⟨hk5.vc.keep k' (by vsep hF [vcChk]), hk5.hh,
    hintIs_keepW hL k'.frame (by vsep hF) (by decide) (by omega_using [hk]) hk5.hint,
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
    · rwa [ifp hlt, ← ifp (show i < j + 1 by omega_using [hlt]) (zHat p (sgOf p σ) i) (toRq (vZ p (sgOf p σ) i))] at this
    · rwa [ifn hlt, ← ifn (show ¬ i < j + 1 by omega_using [e, hlt]) (zHat p (sgOf p σ) i) (toRq (vZ p (sgOf p σ) i))] at this

theorem nttZ_piece {j : Nat} (hj : j < p.ℓ) :
    VPiece p STK (KX p STK j false 0) (KX p STK (j + 1) false 0) (nttAt P (pZ j)) := by
  have hl := hF.l
  refine ⟨fun _ _ _ ⟨A', cc, h, R, hk5⟩ => WP.mono (nttZ_ok hP hF hS hj hk5) fun _ h' => ⟨A', cc, h, R, h'⟩, ?_⟩
  unfold nttAt
  refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
    Reduced x.mem (lpa (vlay p STK σ) (pZ j)) ∧ Reduced y.mem (lpa (vlay p STK σ) (pZ j)))
    (RelCT.exists_ fun σ => ip_tr (t := ntt) hP.ntt hS (f := pZ j) (w := sc oSS)
      (⟨⟨vptr_ok rfl (by unfold oP; omega_using [hj, hl]), by vsep hF⟩, ⟨vptr_ok rfl (by decide), by vsep hF⟩,
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
    hintIs_keepW hL k'.frame (by vsep hF) (by decide) (by omega_using [hk]) hk5.hint,
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

end

end

/-!
# ML-DSA verification on PPC64LE: `c̃′`

As on 32-bit ARM (`Proof/MlDsa/Arm/Verify/Hash.lean`):
`c̃′ = H(μ ‖ w1Encode(w′₁), λ/4)` to `2048` (`vhash_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Verify

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv hashLay hashLay_ptr
  hashS hashS_tr pieceS ix_ne1 shake31)
open VG.Impl.MlDsa.PPC64LE.Verify
open VG.Impl.MlKem.PPC64LE (hash)
open VG.Spec.MlDsa (Params toRq ntt simpleBitPack)
open VG.Proof.MlDsa (HintIs PolyIs polyAt Reduced)
open VG.Proof.MlDsa.Verify (vZ zHat w1Row)
open VG.Spec.Sha3 (bytesAt)

/-- The buffers of the sponge: `mu` and `scratch`. -/
abbrev Kmu : Nat → Bool := fun i => i == 3

theorem kmu : ∀ i < 5, ∀ j < 5, i ≠ j → 2 ≤ i → 2 ≤ j → Kmu i = true → Kmu j = true → i ∈ vWb ∨ j ∈ vWb :=
  fun i _ j _ hij _ _ hi hj => by
    simp only [Kmu, beq_iff_eq] at hi hj; omega

/-- `w1Encode(w′₁)` of rows `A'`, `cc` and `h`. -/
abbrev w1Enc (p : Params) (σ : State) (A' : Nat → Nat → Spec.MlDsa.Poly) (cc : Spec.MlDsa.Poly)
    (h : List (Vector Bool Spec.MlDsa.n)) : List Byte :=
  (List.range p.k).flatMap fun r => simpleBitPack (w1Row p (pkOf p σ) (sgOf p σ) A' (ntt cc) h r) (w1Max p)

theorem flatMap_congr_mem' {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      flatMap_congr_mem' fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- After the hash. -/
abbrev KF (p : Params) (STK : Nat) (σ s : State) : Prop :=
  ∃ A' cc h R, KC5 p STK σ A' cc h R p.ℓ true p.k s ∧
    bytesAt s.mem ((vlay p STK σ).A 0 oCT) p.ctildeLen = Spec.MlDsa.H (muOf σ ++ w1Enc p σ A' cc h) p.ctildeLen

theorem vhPieces {p : Params} (hF : VFacts p) {STK : Nat} {σ s : State} (hs : Site (vlay p STK σ) vWb STK s) :
    (∀ pc ∈ ([⟨.r29, 0, 64⟩, ⟨.r31, oB, p.k * w1Len p⟩] : List Impl.MlKem.PPC64LE.Piece),
      PieceOk (hashLay (vlay p STK σ) s Kmu) ix s false pc) ∧
    PieceOk (hashLay (vlay p STK σ) s Kmu) ix s true (⟨.r31, oCT, p.ctildeLen⟩ : Impl.MlKem.PPC64LE.Piece) := by
  have hk := hF.k
  obtain ⟨w1a, w1b⟩ := hF.w1
  refine ⟨fun pc hpc => ?_, pieceS hs rfl (show oCT < 32768 by decide)
    (show p.ctildeLen < 32768 by rcases hF.ct with e | e | e <;> omega_using [e])
    (show 0 < p.ctildeLen by rcases hF.ct with e | e | e <;> omega_using [e])
    (by rcases hF.ct with e | e | e <;> vsep hF [hashLay, Lay.size, e]) (.inl rfl)
    fun _ => show ix Reg.r31 ∈ vWb by decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
  rcases hpc with rfl | rfl
  · exact pieceS hs rfl (show (0 : Nat) < 32768 by decide) (show 64 < 32768 by decide) (by decide)
      (by vsep hF [hashLay, Lay.size]) (.inr rfl) fun h => absurd h (by decide)
  · exact pieceS hs rfl (show oB < 32768 by decide) (show p.k * w1Len p < 32768 by omega_using [w1a]) w1b
      (by rcases hF.w1l with e | ⟨e, _⟩ <;> vsep hF [hashLay, Lay.size, e]) (.inl rfl) fun h => absurd h (by decide)

theorem B_bytes {p : Params} {STK : Nat} {σ : State} {A' cc h R nz nc} {s : State}
    (hk5 : KC5 p STK σ A' cc h R nz nc p.k s) :
    bytesAt s.mem ((vlay p STK σ).A 0 oB) (p.k * w1Len p) = w1Enc p σ A' cc h := by
  rw [Nat.mul_comm, Lay.A, Proof.MlDsa.KeyGen.bytesAt_pieces s.mem _ oB (w1Len p) p.k]
  exact flatMap_congr_mem' fun r hr => hk5.rows r (List.mem_range.mp hr)

theorem vhash_ok {p : Params} (hF : VFacts p) {STK : Nat} {σ : State} {A' cc h R} {s : State}
    (hk5 : KC5 p STK σ A' cc h R p.ℓ true p.k s) :
    WP isa (hash 136 0x1f [⟨.r29, 0, 64⟩, ⟨.r31, oB, p.k * w1Len p⟩] [⟨.r31, oCT, p.ctildeLen⟩]) s
      (KF p STK σ) := by
  have hk := hF.k
  have hs := hk5.vc.site
  obtain ⟨hin, hq⟩ := vhPieces hF hs
  refine WP.mono (hashS hs kmu (rate := 136) (sfx := 0x1f) (by decide) (by decide) (by simp) hin hq)
    fun s' ⟨k', o'⟩ => ⟨A', cc, h, R, hk5.keep hF k' ?_, ?_⟩
  · have : p.ctildeLen ≤ 64 := by rcases hF.ct with e | e | e <;> omega_using [e]
    k5chks hF (Nat.le_refl _)
  · have o₃ : bytesAt s'.mem ((vlay p STK σ).A 0 oCT) p.ctildeLen = _ := o'
    rw [o₃]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Lay.pb,
      hashLay_ptr _ _ _ (ix_ne1 _)]
    have e1 : bytesAt s.mem ((vlay p STK σ).ptr (ix Reg.r29) + BitVec.ofNat 64 0) 64 = muOf σ :=
      hk5.vc.mu
    have e2 : bytesAt s.mem ((vlay p STK σ).ptr (ix Reg.r31) + BitVec.ofNat 64 oB) (p.k * w1Len p) =
        w1Enc p σ A' cc h := B_bytes hk5
    rw [e1, e2, shake31]
    exact (Proof.MlKem.shake256_eq _ _).symm

theorem vhash_piece {p : Params} (hF : VFacts p) {STK : Nat} :
    VPiece p STK (KX p STK p.ℓ true p.k) (KF p STK)
      (hash 136 0x1f [⟨.r29, 0, 64⟩, ⟨.r31, oB, p.k * w1Len p⟩] [⟨.r31, oCT, p.ctildeLen⟩]) :=
  ⟨fun _ _ _ ⟨_, _, _, _, h⟩ => vhash_ok hF h,
    rel_of (RelCT.exists_ fun σ => hashS_tr kmu (rate := 136) (sfx := 0x1f) (by decide) (by decide)
      (by simp) (fun s hs => (vhPieces hF (σ := σ) hs).1) (fun s hs => (vhPieces hF hs).2) fun _ _ h => h)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => ⟨σ₁, vc_twoL pub h₁.vc h₂.vc⟩⟩

end VG.Proof.MlDsa.PPC64LE.Verify

end

end

/-!
# ML-DSA verification on PPC64LE: `c̃′ = c̃`

As on 32-bit ARM (`Proof/MlDsa/Arm/Verify/Cmp.lean`): `r24 ← 0` unless
`c̃′ = c̃`, without a branch (`cmp_piece`), by ML-KEM's loop comparing two
buffers (`Proof/MlKem/PPC64LE/CmpSel.lean`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Verify

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv argOk arg_ok
  argOk_ne baseReg_of base_pres)
open VG.Impl.MlDsa.PPC64LE.Verify
open VG.Impl.MlDsa.PPC64LE.KeyGen (Ptr Arg)
open VG.Impl.MlKem.PPC64LE (cmpBody)
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

/-! ## A state that differs but in registers other than the layout's -/

theorem siteCongr {L : Lay} {Wb : List Nat} {STK : Nat} {s s' : State} (h : Site L Wb STK s)
    (hr : ∀ r ∈ [Reg.r28, .r29, .r30, .r31], s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Site L Wb STK s' :=
  ⟨h.ok, h.len, h.w0, h.w1, h.sz0, h.sz1, by rw [hsp]; exact h.p1, h.s48, by rw [hsp]; exact h.spk,
    by rw [hr _ (by decide)]; exact h.r31, by rw [hr _ (by decide)]; exact h.r30,
    by rw [hr _ (by decide)]; exact h.r29, by rw [hr _ (by decide)]; exact h.r28,
    by rw [hwr]; exact h.cw, by rw [hrd, hwr]; exact h.cr⟩

theorem VC.congr {p : Params} {STK : Nat} {σ s s' : State} (h : VC p STK σ s)
    (hr : ∀ r ∈ preserved, r ≠ .r24 → r ≠ .r26 → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VC p STK σ s' :=
  ⟨siteCongr h.site (fun r hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl <;> exact hr _ (by decide) (by decide) (by decide)) hsp hrd hwr,
    hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp,
    fun r hp hs => by
      have : r ≠ .r24 ∧ r ≠ .r26 := ⟨fun e => by subst e; simp [savedTop] at hs,
        fun e => by subst e; simp [savedTop] at hs⟩
      rw [hr r hp this.1 this.2]; exact h.pres r hp hs,
    by rw [hm]; exact h.sav, by rw [hm]; exact h.pk, by rw [hm]; exact h.mu, by rw [hm]; exact h.sg,
    fun hc hne => by rw [hm]; exact h.cache hc hne⟩

/-! ## The comparison -/

theorem cmpPre_ok {a b : Ptr} (ha : argOk (.ptr a) = true) (hb : argOk (.ptr b) = true) {n : Nat} (hn : n < 2 ^ 31)
    (s : State) :
    WP isa (.block (Arg.instrs .r3 (.ptr a) ++ Arg.instrs .r4 (.ptr b) ++ Arg.instrs .r26 (.imm n) ++
      ([.li .r12 0] : List Instr))) s fun s' =>
      s'.gpr .r3 = s.gpr a.1 + BitVec.ofNat 64 a.2 ∧ s'.gpr .r4 = s.gpr b.1 + BitVec.ofNat 64 b.2 ∧
      s'.gpr .r26 = BitVec.ofNat 64 n ∧ s'.gpr .r12 = 0 ∧ (∀ r ∈ preserved, r ≠ .r26 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have pa := base_pres (baseReg_of ha)
  have pb := base_pres (baseReg_of hb)
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (arg_ok .r3 ha (argOk_ne (by decide) ha) s) fun s1 e1 => ?_
  refine WP.mono (arg_ok .r4 hb (argOk_ne (by decide) hb) s1) fun s2 e2 => ?_
  refine WP.mono (arg_ok .r26 (a := .imm n) (by simp only [argOk, decide_eq_true_eq]; exact hn)
    (fun _ e => by cases e) s2) fun s3 e3 => ?_
  subst e1 e2 e3
  prun []
  have nb3 : b.1 ≠ .r3 := fun e => by rw [e] at pb; simp [preserved] at pb
  refine ⟨rfl, by simp only [KeyGen.argVal, RegUpd.gpr_write_of_ne _ _ nb3], rfl, rfl, fun r hr hs => ?_, trivial⟩
  simp (disch := decide) only [RegUpd.gpr_write_of_ne _ _ hs, Sample.gpr_write_pres hr]

theorem shr63_eq : ∀ n < 256, (BitVec.ofNat 64 n - 1) >>> 63 = if n = 0 then (1 : BitVec 64) else 0 := by
  decide +kernel

theorem shr63_of {v : BitVec 64} (h : v.toNat < 256) : (v - 1) >>> 63 = if v = 0 then (1 : BitVec 64) else 0 := by
  have hv := shr63_eq v.toNat h
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hv
  rw [hv]
  by_cases e : v = 0
  · subst e; rfl
  · have e' : ¬ v.toNat = 0 := fun h' => e (BitVec.eq_of_toNat_eq (by rw [h']; rfl))
    simp only [e, e', ↓reduceIte]

theorem cmpPost_ok (s : State) :
    WP isa (.block [.subi .r12 .r12 1, .lsr .d .r12 .r12 63, .logic .and .r24 .r24 .r12]) s
      fun s' => s'.gpr .r24 = s.gpr .r24 &&& ((s.gpr .r12 - 1) >>> 63) ∧
        (∀ r ∈ preserved, r ≠ .r24 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.sp = s.sp := by
  prun []
  refine ⟨rfl, fun r hr hs => ?_, trivial⟩
  simp (disch := decide) only [RegUpd.gpr_write_of_ne _ _ hs, Sample.gpr_write_pres hr]

/-- `r24 ← r24 ∧ (the `n` bytes at `a` and `b` are equal)`. -/
theorem cmpAnd_okS {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : Site L Wb STK s) {a b : Ptr} {n : Nat}
    (pa : PtrIn L a n) (pb : PtrIn L b n) (hn : 0 < n) (hn' : n < 2 ^ 31) :
    WP isa (cmpAnd a b n) s fun s' =>
      s'.gpr .r24 = s.gpr .r24 &&& flag (decide (bytesAt s.mem (lpa L a) n = bytesAt s.mem (lpa L b) n)) ∧
      (∀ r ∈ preserved, r ≠ .r24 → r ≠ .r26 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  have cr : Covers [⟨lpa L a, n⟩, ⟨lpa L b, n⟩] (s.rd ++ s.wr) :=
    Covers.cons (hs.crE pa) (Covers.cons (hs.crE pb) Covers.nil)
  unfold cmpAnd
  refine WP.seq (WP.mono (cmpPre_ok pa.1 pb.1 hn' s) fun s₁ ⟨g3, g4, g26, g12, cs, m, rd, wr, sp⟩ => ?_)
  rw [hs.base (baseReg_of pa.1)] at g3
  rw [hs.base (baseReg_of pb.1)] at g4
  refine WP.seq (wp_loop_nz (CmpInv (lpa L a) (lpa L b) n s₁) (N := n) hn
      (fun k hk s h => cmp_step (by omega_using [hn']) (by rw [rd, wr]; exact cr) hk h) (fun s₂ h => ?_)
    ⟨by rw [g3]; simp [lpa, Lay.A], by rw [g4]; simp [lpa, Lay.A], by rw [g26, Nat.sub_zero], fun _ _ _ => rfl,
      rfl, rfl, rfl, rfl, by rw [g12]; decide,
      by rw [g12]; exact ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ => rfl⟩⟩)
  refine WP.mono (cmpPost_ok s₂) fun s' ⟨r24, rs, m', rd', wr', sp'⟩ => ⟨?_, fun r hr h24 h26 => ?_,
    m'.trans (h.mem.trans m), rd'.trans (h.rd.trans rd), wr'.trans (h.wr.trans wr), sp'.trans (h.sp.trans sp)⟩
  · have e24 : s₂.gpr .r24 = s.gpr .r24 := (h.cs .r24 (by decide) (by decide)).trans (cs .r24 (by decide) (by decide))
    rw [r24, shr63_of h.lt, e24]
    congr 1
    have key : s₂.gpr .r12 = 0 ↔ bytesAt s.mem (lpa L a) n = bytesAt s.mem (lpa L b) n := by
      rw [h.eq, m]
      constructor
      · intro he
        exact Proof.MlKem.bytesAt_eq (Proof.MlKem.bytesAt_length _ _ _) fun t ht => by
          rw [he t ht, Proof.MlKem.bytesAt_getElem]
      · intro he t ht
        have := congrArg (fun L : List Byte => L[t]!) he
        simp only [Proof.MlKem.bytesAt_getElem! _ _ ht] at this
        exact this
    by_cases e : s₂.gpr .r12 = 0
    · simp only [e, decide_eq_true (key.mp e), ↓reduceIte, flag]
    · simp only [e, decide_eq_false (fun h' => e (key.mpr h')), ↓reduceIte, flag, Bool.false_eq_true]
  · rw [rs r hr h24]
    exact (h.cs r hr h26).trans (cs r hr h26)

/-! ## After the comparison -/

/-- At the end of `compute`: `r24` is the samplers' result `R` and whether
`c̃′ = c̃`. -/
abbrev KE (p : Params) (STK : Nat) (σ s : State) : Prop :=
  ∃ A' cc h R, VC p STK σ s ∧ hintOf p σ = some h ∧ h.length = p.k ∧ Gd p σ A' cc R ∧
    s.gpr .r24 = R &&& flag (decide (Spec.MlDsa.H (muOf σ ++ w1Enc p σ A' cc h) p.ctildeLen =
      Proof.MlDsa.Verify.vCt p (sgOf p σ)))

theorem cmp_ok {p : Params} (hF : VFacts p) {STK : Nat} {σ s : State} (h : KF p STK σ s) :
    WP isa (cmpAnd (sc oCT) (.r28, 0) p.ctildeLen) s (KE p STK σ) := by
  obtain ⟨A', cc, hh, R, hk5, hb⟩ := h
  have hk := hF.k
  have hct := hF.ct
  have pa : PtrIn (vlay p STK σ) (sc oCT) p.ctildeLen := by
    refine ⟨vptr_ok rfl (by decide), ?_⟩; rcases hct with e | e | e <;> vsep hF [e]
  have pb : PtrIn (vlay p STK σ) (.r28, 0) p.ctildeLen := by
    refine ⟨vptr_ok rfl (by decide), ?_⟩; have := hF.sig; have := hF.hint; vsep hF
  refine WP.mono (cmpAnd_okS hk5.vc.site pa pb (by omega_using [hct]) (by omega_using [hct]))
    fun s' ⟨r24, rs, m, rd, wr, sp⟩ => ⟨A', cc, hh, R, hk5.vc.congr rs m sp rd wr, hk5.hh, hk5.hint.1, hk5.gd, ?_⟩
  have e4 : bytesAt s.mem (lpa (vlay p STK σ) (.r28, 0)) p.ctildeLen = Proof.MlDsa.Verify.vCt p (sgOf p σ) := by
    have := sig_slice hk5.vc (o := 0) (l := p.ctildeLen) (by have := hF.sig; have := hF.hint; omega_arith)
    rw [List.drop_zero] at this
    exact this
  have e0 : bytesAt s.mem (lpa (vlay p STK σ) (sc oCT)) p.ctildeLen = _ := hb
  rw [r24, e0, e4, hk5.r24]

theorem cmp_taint {n : Nat} (hn : n = 32 ∨ n = 48 ∨ n = 64) : ∃ hc, (VG.PPC64LE.taint.check
    (Taint.ofRegs [.r28, .r29, .r30, .r31]) (cmpAnd (sc oCT) (.r28, 0) n) hc).isSome = true := by
  rcases hn with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

theorem cmp_piece {p : Params} (hF : VFacts p) {STK : Nat} :
    VPiece p STK (KF p STK) (KE p STK) (cmpAnd (sc oCT) (.r28, 0) p.ctildeLen) :=
  ⟨fun _ _ _ h => cmp_ok hF h, rel_of (vtaint4 (cmp_taint hF.ct).choose_spec)
    fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, _⟩ ⟨_, _, _, _, h₂, _⟩ => ⟨σ₁, vc_twoL pub h₁.vc h₂.vc⟩⟩

end VG.Proof.MlDsa.PPC64LE.Verify
