module

import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA4
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseO
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseL
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA signing on AArch64: pieces of the correctness proof

When `Sign_internal` returns nothing within `minBounds`: its `ExpandA` or its
loop does not finish (`signMu_min_A`, `signMu_min_L`); and when an iteration
passes, the signature within `maxBounds` (`signMu_max`). With the layout
checks of the signing functions (`fChk`, `allChk`) and their entry
(`entry_st`, `pro_in`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `Sign_internal` -/

section
variable {p : Params} {σ : State}

theorem seedE_ij {i j : Nat} (hj : j < p.ℓ) : seedE p σ (p.ℓ * i + j) = aSeed (rhoOf p σ) i j := by
  have hl : 0 < p.ℓ := by omega
  have e1 : (p.ℓ * i + j) / p.ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (p.ℓ * i + j) % p.ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [seedE, e1, e2]

theorem ij_lt {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) : p.ℓ * i + j < p.k * p.ℓ := by
  have := Nat.mul_le_mul_left p.ℓ (show i + 1 ≤ p.k from hi)
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm p.ℓ p.k] at this; omega

theorem expandA_max (hok : ∀ e < p.k * p.ℓ, (rejNTTPoly maxBounds.rejNTT (seedE p σ e)).isSome) :
    expandA p maxBounds (rhoOf p σ) = some (amat p (Am p σ)) :=
  expandA_some fun i hi j hj => by rw [← seedE_ij hj]; exact hok _ (ij_lt hi hj)

theorem signMu_min_A (h : ∃ e < p.k * p.ℓ, rejNTTPoly minBounds.rejNTT (seedE p σ e) = none) :
    signMu p minBounds (skOf p σ) (muOf σ) (rndOf σ) = none := by
  obtain ⟨e, he, hn⟩ := h
  have hl : 0 < p.ℓ := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at he; omega
  exact signMu_none_A (expandA_none ⟨e / p.ℓ, (Nat.div_lt_iff_lt_mul hl).mpr he, e % p.ℓ, Nat.mod_lt _ hl, hn⟩)

theorem signMu_min_L (hA : expandA p maxBounds (rhoOf p σ) = some (amat p (Am p σ)))
    (hL : loopF p σ minBounds minBounds.sign 0 = none) :
    signMu p minBounds (skOf p σ) (muOf σ) (rndOf σ) = none := by
  cases e : expandA p minBounds (rhoOf p σ) with
  | none => exact signMu_none_A e
  | some A' =>
    have := expandA_mono (show minBounds.rejNTT ≤ maxBounds.rejNTT by decide) e
    rw [hA] at this
    obtain rfl := (Option.some.inj this).symm
    exact signMu_none_L e hL

theorem signMu_max (hp : ParamsOk p) (hA : expandA p maxBounds (rhoOf p σ) = some (amat p (Am p σ))) {t : Nat}
    (ht : t < 814) (hr : RejT p σ t) (hs : (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome)
    (hpass : PassV p σ (p.ℓ * t)) :
    signMu p maxBounds (skOf p σ) (muOf σ) (rndOf σ) = some (sigV p σ (p.ℓ * t)) :=
  signMu_some hA (signLoop_pass _ _ _ _ _ _ _ hr (show t < maxBounds.sign by
    show t < 1000; omega) (iter_pass hp hs hpass))

end

/-! ## After the loop -/

/-- Before the return: `x24`, and the signature in `sig` if it is 1. -/
structure FS (p : Params) (D : Nat) (σ s : State) : Prop where
  st : St p D σ s
  r01 : s.gpr .x24 = 0 ∨ s.gpr .x24 = 1
  ok : s.gpr .x24 = 1 →
    signMu p maxBounds (skOf p σ) (muOf σ) (rndOf σ) = some (bytesAt s.mem (pa s (.x23, 0)) p.sigLen)
  bad : s.gpr .x24 = 0 → signMu p minBounds (skOf p σ) (muOf σ) (rndOf σ) = none

/-- What the function needs of the layout, besides its pieces. -/
def fChk (p : Params) : Bool :=
  (List.range 7).all (fun k => inB (sgB p) (sc (oSV + 8 * k)) 8) &&
    decide (scrLen p < 2 ^ 32 ∧ p.skLen < 2 ^ 32 ∧ p.sigLen < 2 ^ 32 ∧ oSV + 56 ≤ scrLen p)

theorem fChk_ok {p : Params} (h : Ok3 p) : fChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

/-- Every check of the layout. -/
def allChk (p : Params) : Bool :=
  aChk p && dChk p && cChk p && bChk p && ksChk p && lChk p && oChk p && fChk p

theorem allChk_ok {p : Params} (h : Ok3 p) : allChk p = true := by
  simp only [allChk, aChk_ok h, dChk_ok h, cChk_ok h, bChk_ok h, ksChk_ok h, lChk_ok h, oChk_ok h, fChk_ok h,
    Bool.and_self]

theorem x24_one {s : State} (h : s.gpr .x24 = 0 ∨ s.gpr .x24 = 1) (hne : (s.gpr .x24).setWidth 32 ≠ 0) :
    s.gpr .x24 = 1 := by
  rcases h with e | e
  · rw [e] at hne; exact absurd rfl hne
  · exact e

theorem x24_zero {s : State} (h : s.gpr .x24 = 0 ∨ s.gpr .x24 = 1) (he : (s.gpr .x24).setWidth 32 = 0) :
    s.gpr .x24 = 0 := by
  rcases h with e | e
  · exact e
  · rw [e] at he; exact absurd he (by decide)

/-! ## The function -/

theorem entry_bytes {σ s : State} {r : Reg} {len : Nat} {R : Region} (hf : Frame [R] σ.mem s.mem)
    (hd : Region.Disjoint ⟨σ.gpr r, len⟩ R) (hl : len ≤ 2 ^ 64) {b : Reg} (hb : s.gpr b = σ.gpr r) :
    bytesAt s.mem (pa s (b, 0)) len = bytesAt σ.mem (σ.gpr r) len := by
  rw [pa, hb, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
  exact VG.Proof.MlKem.bytesAt_frame hf (fun R' hR => by rw [List.mem_singleton] at hR; subst hR; exact hd) hl

theorem entry_st {D : Nat} {p : Params} (h3 : Ok3 p) {σ s : State}
    (hpre : (signK p D).pre σ) (ht : Top σ s)
    (hf : Frame [⟨σ.gpr .x4 + BitVec.ofNat 64 oSV, 56⟩] σ.mem s.mem) : St p D σ s := by
  have hc := fChk_ok h3
  simp only [fChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨-, h1, h2, h3', h4⟩ := hc
  have hsub : Region.Sub ⟨σ.gpr .x4 + BitVec.ofNat 64 oSV, 56⟩ ⟨σ.gpr .x4, scrLen p⟩ := Offset.sub_base _ h4
  have hpre' := hpre
  obtain ⟨_, _, _, d2, _, d4, _, d6, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hpre'
  exact ⟨ht, sgLay hpre ⟨h1, h2, h3'⟩ ht,
    entry_bytes hf (d2.sub_right hsub) (by omega) (ht.regs (.x25, .x0) (by decide)),
    entry_bytes hf (d4.sub_right hsub) (by omega) (ht.regs (.x26, .x1) (by decide)),
    entry_bytes hf (d6.sub_right hsub) (by omega) (ht.regs (.x27, .x2) (by decide))⟩

/-- The prologue saves the registers in `scratch`. -/
theorem pro_in {D : Nat} {p : Params} (h3 : Ok3 p) {σ : State} (hpre : (signK p D).pre σ) :
    ∀ k < 7, InRegions σ.wr (σ.gpr .x4 + BitVec.ofNat 64 (oSV + 8 * k)) 8 := by
  have hc := fChk_ok h3
  simp only [fChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨-, -, -, -, hsz⟩ := hc
  intro k hk
  exact ⟨⟨σ.gpr .x4, scrLen p⟩, by rw [hpre.2.1]; simp,
    Offset.contains_base _ (by omega) (by simp only [oSV]; omega)⟩

end VG.Proof.MlDsa.AArch64.Sign
