module

public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestBase
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Pack
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Arith
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.Framework.Contract

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
