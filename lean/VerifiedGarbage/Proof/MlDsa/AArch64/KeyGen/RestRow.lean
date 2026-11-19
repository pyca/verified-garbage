module

public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.CallRound
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestBase
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Pack
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Arith

/-! ### `MlDsa.AArch64.KeyGen.RestPack`, which this module and modules that import it used -/

section

/-!
# ML-DSA key generation on AArch64: `s₁ ‖ s₂` to `sk`, and `ŝ₁`

What `BitPack` of each entry of `s₁ ‖ s₂` to `sk` needs: its coefficients
are small (`small_mem`, `small_big`, `bpOk_eta`), and the layout check of
the call (`packS_chk`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt bitPack)
open VG.Proof.MlDsa (polyAt coeffAt Reduced PolyIs)
open VG.Proof.MlDsa.KeyGen (Small ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-! ## The coefficients of a small polynomial -/

theorem coeff_val {m : Mem} {q : Addr} {f : Poly} (h : PolyIs m q f) {i : Nat} (hi : i < 256) :
    (coeffAt m q i).toNat = (f[i]'hi).val := by
  have e := congrArg (fun g : Poly => (g[i]'hi).val) h.2
  simp only [polyAt, Vector.getElem_ofFn, Fin.val_ofNat] at e
  rw [← e, Nat.mod_eq_of_lt (h.1 i hi)]

theorem small_mem {η : Nat} {x : IPoly} (h : Small η x) {i : Nat} (hi : i < 256) :
    -(η : Int) ≤ x[i] ∧ x[i] ≤ η := h _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem hi))

theorem range_of {m : Mem} {q : Addr} {η : Nat} (hη : η ≤ 4) {x : IPoly} (h : PolyIs m q (toRq x))
    (hs : Small η x) : BpRange m q η η := by
  intro i hi
  have hx := small_mem hs hi
  rw [coeff_val h hi]
  simp only [toRq, Vector.getElem_map]
  rw [Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)]
  exact hx

theorem small_big {η : Nat} (hη : η ≤ 4) {x : IPoly} (hs : Small η x) :
    ∀ c ∈ x.toList, -4190208 ≤ c ∧ c ≤ 4190208 := fun c hc => by
  have := hs c hc; omega_arith

theorem eta_le {p : Params} (hF : PFacts p) : p.η ≤ 4 := by rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩ <;> omega_using [h]

theorem bpOk_eta {p : Params} (hF : PFacts p) : BpOk p.η p.η (lenS p) := by
  rcases hF.eta with ⟨h, e⟩ | ⟨h, e⟩ <;> exact ⟨by rw [h]; decide, by rw [e, h]; decide, by rw [e, h]; decide⟩

/-- The entry `r` of `s₁ ‖ s₂`, before `NTT`. -/
theorem KR.sPoly {p : Params} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {np nr : Nat}
    {s : State} (h : KR p σ A S R np 0 nr s) {r : Nat} (hr : r < p.ℓ + p.k) :
    PolyIs s.mem (pa s (sP p r)) (toRq (S r)) := by
  by_cases hl : r < p.ℓ
  · have := h.s1 r hl; rwa [ifn (Nat.not_lt_zero r)] at this
  · have := h.s2 (r - p.ℓ) (by omega_using [hr, hl]); rwa [show p.ℓ + (r - p.ℓ) = r by omega_using [hl]] at this

/-! ## `BitPack` of `s₁ ‖ s₂` -/

theorem packS_chk {p : Params} (hF : PFacts p) {r : Nat} (hr : r < p.ℓ + p.k) :
    rwChk kgR (kgW p) (sP p r) 1024 (.x27, 128 + lenS p * r) (lenS p) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have hlr : lenS p * r + lenS p ≤ lenS p * (p.ℓ + p.k) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega_using [hr])
  unfold rwChk
  lay [hF.pk, hF.sk]

/-- The states after the copies, and the first `np` entries packed, `nj` in the NTT domain and `nr` rows. -/
abbrev KRx (p : Params) (np nj nr : Nat) (σ s : State) : Prop := ∃ A S R, KR p σ A S R np nj nr s

end VG.Proof.MlDsa.AArch64.KeyGen

end

end

/-!
# ML-DSA key generation on AArch64: the rows of `t`

Row `i` of `t`: the layout checks of the calls that add `s₂[i]`, round the
row and pack `t₁[i]` to `pk` and `t₀[i]` to `sk` (`add_chk`, `p2r_chk`,
`sbp_chk`, `bp_chk`), and that `t₁[i]` and `t₀[i]` are in the ranges their
packings need (`sbpOk_t1`, `bpOk_t0`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt nttInv add multiplyNTT bitPack simpleBitPack power2Round ofInt)
open VG.Proof.MlDsa (polyAt natPolyAt coeffAt Reduced PolyIs NatPolyIs)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K ifp ifn)
open VG.Spec.Sha3 (bytesAt)

theorem idx_lt {p : Params} {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) : p.ℓ * i + j < p.k * p.ℓ := by
  have := Nat.mul_le_mul_left p.ℓ (show i + 1 ≤ p.k by omega_using [hi])
  rw [Nat.mul_succ, Nat.mul_comm p.ℓ p.k] at this
  omega_using [hj, this]

/-- The `t` so far. -/
abbrev tIs (p : Params) (g : (Nat → Poly) → (Nat → IPoly) → Poly) (A : Nat → Poly) (S : Nat → IPoly) (s : State) :
    Prop := PolyIs s.mem (pa s (tP p)) (g A S)

theorem range_t0 {m : Mem} {q : Addr} {t : Poly} (h : PolyIs m q (t.map fun c => ofInt (power2Round c).2)) :
    BpRange m q 4095 4096 := fun j hj => by
  rw [coeff_val h hj]
  simp only [Vector.getElem_map]
  have := Proof.MlDsa.KeyGen.power2Round_snd (t[j]'hj)
  rw [Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)]
  omega

theorem modPm_t0 (t : Poly) :
    ((t.map fun c => ofInt (power2Round c).2).map fun c => Spec.MlDsa.modPm c.val Spec.MlDsa.q) =
      t.map fun c => (power2Round c).2 := by
  rw [Vector.map_map]
  refine Vector.map_congr_left fun c _ => ?_
  have := Proof.MlDsa.KeyGen.power2Round_snd c
  exact Proof.MlDsa.KeyGen.modPm_ofInt (by omega_using [this]) (by omega_using [this])

theorem t1_bound {m : Mem} {q : Addr} {p : Params} {A : Nat → Poly} {S : Nat → IPoly} {i : Nat}
    (h1 : NatPolyIs m q (t1K p A S i)) : ∀ j < 256, (coeffAt m q j).toNat ≤ 1023 := fun j hj => by
  rw [show (coeffAt m q j).toNat = (t1K p A S i)[j]'hj from by
    rw [← h1]; simp only [natPolyAt, Vector.getElem_ofFn]]
  simp only [Proof.MlDsa.KeyGen.t1K, Vector.getElem_map]
  have := Proof.MlDsa.KeyGen.power2Round_fst ((Proof.MlDsa.KeyGen.tK p A S i)[j]'hj)
  omega

/-! ## The checks of the calls -/

section
variable {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k)
include hF hi

theorem add_chk : accChk kgR (kgW p) (tP p) (sP p (p.ℓ + i)) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  unfold accChk; layd

theorem p2r_chk : p2rChk kgR (kgW p) (tP p) (t1P p) (t0P p) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  unfold p2rChk; lay

theorem sbp_chk : rwChk kgR (kgW p) (t1P p) 1024 (.x26, 32 + 320 * i) 320 = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  unfold rwChk; layd

theorem bp_chk : rwChk kgR (kgW p) (t0P p) 1024 (.x27, oT0 p + 416 * i) 416 = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have hlen : lenS p = 96 ∨ lenS p = 128 := hF.eta.imp And.right And.right
  unfold rwChk; layd

end

/-! ## The checks of the writes of a row, once each -/

theorem chk_poly {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k) {j : Nat} (hj : j < 3) :
    KRChk p (p.ℓ + p.k) p.ℓ i [(sc (oP (p.k * p.ℓ + p.ℓ + p.k + j)), 1024)] := by
  have := hF.k; have := hF.l; have := hF.kl
  exact KRChk.x28 hF (by omega_using []) (by omega_using [hi]) (.inr (by simp only [SV, oP]; omega_using []))
    (.inr (by simp only [oP]; omega_using [])) (by rw [hF.scr]; simp only [oP]; omega_using [hj])

theorem chk_t {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k) : KRChk p (p.ℓ + p.k) p.ℓ i [(tP p, 1024)] := by
  have := chk_poly hF hi (j := 0) (by decide); rwa [Nat.add_zero] at this

theorem chk_p2r {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k) :
    KRChk p (p.ℓ + p.k) p.ℓ i [(t1P p, 1024), (t0P p, 1024)] :=
  (chk_poly hF hi (j := 1) (by decide)).append (ws₁ := [_]) (chk_poly hF hi (j := 2) (by decide))

theorem chk_sbp {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k) :
    KRChk p (p.ℓ + p.k) p.ℓ i [((.x26, 32 + 320 * i), 320)] :=
  KRChk.x26 hF (Nat.le_refl _) (Nat.le_of_lt hi) (Nat.le_refl _) (by rw [hF.pk]; omega_using [hi])

theorem chk_bp {p : Params} (hF : PFacts p) {i : Nat} (hi : i < p.k) :
    KRChk p (p.ℓ + p.k) p.ℓ i [((.x27, oT0 p + 416 * i), 416)] := by
  have := hF.k; have := hF.l
  exact KRChk.x27 hF (Nat.le_refl _) (Nat.le_of_lt hi) (by simp only [oT0]; omega_using []) (.inr (by simp only [oT0]; omega_using []))
    (.inr (Nat.le_refl _)) (by rw [hF.sk]; omega_using [hi])

theorem sbpOk_t1 : SbpOk 1023 320 := ⟨by decide, by decide, by decide⟩

theorem bpOk_t0 : BpOk 4095 4096 416 := ⟨by decide, by decide, by decide⟩

end VG.Proof.MlDsa.AArch64.KeyGen
