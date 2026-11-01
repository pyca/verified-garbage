module

import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Middle
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
public import VerifiedGarbage.Proof.Weierstrass.MulContract

/-!
# ECDSA on PPC64LE: `s`

As on 32-bit ARM (`Proof/Ecdsa/Arm/Scalar.lean`): `scOps_ok`, the seven
field operations of `scalar` modulo `n`: `r`, `d` and `e` into Montgomery's
form, `s = k^(n-2) (e + r d)`, and `s` out of it.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Spec.Weierstrass

variable {c : Cfg}

theorem scalar_eq (c : Cfg) : c.scalar =
    .seq (mulCall c.SN (c.sl RM) (c.sl RR) (c.sl R2N)) (.seq (mulCall c.SN (c.sl DM) (c.sl D) (c.sl R2N))
    (.seq (mulCall c.SN (c.sl EM) (c.sl E) (c.sl R2N)) (.seq (mulCall c.SN (c.sl TT) (c.sl RM) (c.sl DM))
    (.seq (addCall c.SN (c.sl TT) (c.sl TT) (c.sl EM)) (.seq (mulCall c.SN (c.sl SM) (c.sl ACC) (c.sl TT))
    (.seq (mulCall c.SN (c.sl SS) (c.sl SM) (c.sl ONE)) (.block (c.checkNonzero (c.sl SS) ++ c.finish)))))))) :=
  rfl

/-- What `scalar`'s field operations leave. -/
structure ScPost (c : Cfg) (s₀ : State) (base : Addr) (s s' : State) : Prop extends Keep c s₀ base s' where
  same : ∀ {i}, i < 45 → i ∉ [RM, DM, EM, TT, SM, SS] → sv c base s' i = sv c base s i
  flag : flagW c base s' = flagW c base s
  ss_lt : sv c base s' SS < c.C.n
  ss : Fin.ofNat c.C.n (sv c base s' SS) = toM c.C.n (2 ^ (64 * c.n)) (sv c base s ACC) *
    (Fin.ofNat c.C.n (sv c base s E) + Fin.ofNat c.C.n (sv c base s RR) * Fin.ofNat c.C.n (sv c base s D))

/-- The seven field operations of `scalar`. -/
theorem scOps_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State} (K₀ : Keep c s₀ base s)
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', ScPost c s₀ base s s' → WP isa rest s' Q) :
    WP isa (.seq (mulCall c.SN (c.sl RM) (c.sl RR) (c.sl R2N)) (.seq (mulCall c.SN (c.sl DM) (c.sl D) (c.sl R2N))
      (.seq (mulCall c.SN (c.sl EM) (c.sl E) (c.sl R2N)) (.seq (mulCall c.SN (c.sl TT) (c.sl RM) (c.sl DM))
      (.seq (addCall c.SN (c.sl TT) (c.sl TT) (c.sl EM)) (.seq (mulCall c.SN (c.sl SM) (c.sl ACC) (c.sl TT))
      (.seq (mulCall c.SN (c.sl SS) (c.sl SM) (c.sl ONE)) rest))))))) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have hn3 := hc.n_ge
  have hone : sv c base s ONE = 1 := K₀.fixed.one
  have hr2 : sv c base s R2N = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n := K₀.fixed.r2n
  have hr2lt : 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n < c.C.n := Nat.mod_lt _ (by omega)
  -- `RM = RR · R²`.
  refine WP.seq (WP.mono (slMul_ok hc.fn hc.fnk hc.fnm h7 K₀.ws (o := RM) (a := RR) (b := R2N) (by decide)
    (by decide) (by decide) (by rw [hr2]; exact hr2lt)) fun s₁ ⟨k₁, U₁, _, e₁⟩ => ?_)
  obtain ⟨K₁, f₁, -, v₁⟩ := K₀.call h0 h7 (o := RM) (by decide) (by decide) (by decide) k₁ U₁
  have rm₁ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₁ RM) = Fin.ofNat c.C.n (sv c base s RR) :=
    toM_r2 hnR (by rw [e₁, hr2])
  -- `DM = D · R²`.
  refine WP.seq (WP.mono (slMul_ok hc.fn hc.fnk hc.fnm h7 K₁.ws (o := DM) (a := D) (b := R2N) (by decide)
    (by decide) (by decide) (by rw [v₁ (by decide) (by decide), hr2]; exact hr2lt)) fun s₂ ⟨k₂, U₂, lt₂, e₂⟩ => ?_)
  obtain ⟨K₂, f₂, -, v₂⟩ := K₁.call h0 h7 (o := DM) (by decide) (by decide) (by decide) k₂ U₂
  have b₂ : ∀ {i}, i < 45 → i ∉ [RM, DM] → sv c base s₂ i = sv c base s i := fun hi hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hl
    rw [v₂ hi hl.2, v₁ hi hl.1]
  have dm₂ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₂ DM) = Fin.ofNat c.C.n (sv c base s D) :=
    toM_r2 hnR (by rw [e₂, v₁ (i := D) (by decide) (by decide), v₁ (i := R2N) (by decide) (by decide), hr2])
  -- `EM = E · R²`.
  refine WP.seq (WP.mono (slMul_ok hc.fn hc.fnk hc.fnm h7 K₂.ws (o := EM) (a := E) (b := R2N) (by decide)
    (by decide) (by decide) (by rw [b₂ (by decide) (by decide), hr2]; exact hr2lt)) fun s₃ ⟨k₃, U₃, lt₃, e₃⟩ => ?_)
  obtain ⟨K₃, f₃, -, v₃⟩ := K₂.call h0 h7 (o := EM) (by decide) (by decide) (by decide) k₃ U₃
  have b₃ : ∀ {i}, i < 45 → i ∉ [RM, DM, EM] → sv c base s₃ i = sv c base s i := fun hi hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hl
    rw [v₃ hi hl.2.2, b₂ hi (by simp [hl.1, hl.2.1])]
  have em₃ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₃ EM) = Fin.ofNat c.C.n (sv c base s E) :=
    toM_r2 hnR (by rw [e₃, b₂ (i := E) (by decide) (by decide), b₂ (i := R2N) (by decide) (by decide), hr2])
  -- `TT = RM · DM`.
  refine WP.seq (WP.mono (slMul_ok hc.fn hc.fnk hc.fnm h7 K₃.ws (o := TT) (a := RM) (b := DM) (by decide)
    (by decide) (by decide) (by rw [v₃ (by decide) (by decide)]; exact lt₂)) fun s₄ ⟨k₄, U₄, lt₄, e₄⟩ => ?_)
  obtain ⟨K₄, f₄, -, v₄⟩ := K₃.call h0 h7 (o := TT) (by decide) (by decide) (by decide) k₄ U₄
  have tt₄ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₄ TT) =
      Fin.ofNat c.C.n (sv c base s RR) * Fin.ofNat c.C.n (sv c base s D) := by
    rw [toM_mul hnR e₄, v₃ (i := RM) (by decide) (by decide), v₂ (i := RM) (by decide) (by decide), rm₁,
      v₃ (i := DM) (by decide) (by decide), dm₂]
  -- `TT = TT + EM`.
  have em₄ : sv c base s₄ EM = sv c base s₃ EM := v₄ (by decide) (by decide)
  refine WP.seq (WP.mono (slAdd_ok hc.fn hc.fnk hc.fnm h7 K₄.ws (o := TT) (a := TT) (b := EM) (by decide)
    (by decide) (by decide) (by rw [em₄]; omega)) fun s₅ ⟨k₅, U₅, e₅⟩ => ?_)
  obtain ⟨K₅, f₅, -, v₅⟩ := K₄.call h0 h7 (o := TT) (by decide) (by decide) (by decide) k₅ U₅
  have tt₅ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₅ TT) =
      Fin.ofNat c.C.n (sv c base s RR) * Fin.ofNat c.C.n (sv c base s D) + Fin.ofNat c.C.n (sv c base s E) := by
    rw [e₅, toM_add, tt₄, em₄, em₃]
  have tt₅lt : sv c base s₅ TT < c.C.n := by rw [e₅]; exact Nat.mod_lt _ (by omega)
  -- `SM = ACC · TT`.
  refine WP.seq (WP.mono (slMul_ok hc.fn hc.fnk hc.fnm h7 K₅.ws (o := SM) (a := ACC) (b := TT) (by decide)
    (by decide) (by decide) tt₅lt) fun s₆ ⟨k₆, U₆, _, e₆⟩ => ?_)
  obtain ⟨K₆, f₆, -, v₆⟩ := K₅.call h0 h7 (o := SM) (by decide) (by decide) (by decide) k₆ U₆
  have b₅ : ∀ {i}, i < 45 → i ∉ [RM, DM, EM, TT] → sv c base s₅ i = sv c base s i := fun hi hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hl
    rw [v₅ hi hl.2.2.2, v₄ hi hl.2.2.2, b₃ hi (by simp [hl.1, hl.2.1, hl.2.2.1])]
  have sm₆ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₆ SM) =
      toM c.C.n (2 ^ (64 * c.n)) (sv c base s ACC) *
        (Fin.ofNat c.C.n (sv c base s RR) * Fin.ofNat c.C.n (sv c base s D) + Fin.ofNat c.C.n (sv c base s E)) := by
    rw [toM_mul hnR e₆, b₅ (i := ACC) (by decide) (by decide), tt₅]
  -- `SS = SM · 1`.
  have one₆ : sv c base s₆ ONE = 1 := by rw [v₆ (by decide) (by decide), b₅ (by decide) (by decide), hone]
  refine WP.seq (WP.mono (slMul_ok hc.fn hc.fnk hc.fnm h7 K₆.ws (o := SS) (a := SM) (b := ONE) (by decide)
    (by decide) (by decide) (by rw [one₆]; omega)) fun s₇ ⟨k₇, U₇, lt₇, e₇⟩ => h s₇ ?_)
  obtain ⟨K₇, f₇, -, v₇⟩ := K₆.call h0 h7 (o := SS) (by decide) (by decide) (by decide) k₇ U₇
  refine ⟨K₇, fun hi hl => ?_, by rw [f₇, f₆, f₅, f₄, f₃, f₂, f₁], lt₇, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hl
    rw [v₇ hi hl.2.2.2.2.2, v₆ hi hl.2.2.2.2.1, b₅ hi (by simp [hl.1, hl.2.1, hl.2.2.1, hl.2.2.2.1])]
  · rw [toM_one_mul hnR (by rw [e₇, one₆]), sm₆, Lean.Grind.AddCommMonoid.add_comm]

end VG.Proof.Ecdsa.PPC64LE
