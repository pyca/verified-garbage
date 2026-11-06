module
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseK

import VerifiedGarbage.Proof.MlDsa.Round.Decompose
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA signing on AArch64: the signature

Once an iteration passed: `c̃`, then `BitPack(z[r], γ₁ - 1, γ₁)` for each `r`
(in range, as `z` passed its norm check: `inRange_of_norm`), then
`HintBitPack(h)` (with at most `ω` 1s) to `sig`, which then holds
`sigEncode(c̃, z mod± q, h)` (`sigV`); with the layout check of the output
(`oChk`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `z` in range -/

theorem coeff_val {m : Mem} {a : Addr} {f : Poly} (h : PolyIs m a f) {i : Nat} (hi : i < 256) :
    (coeffAt m a i).toNat = f[i].val := by
  have e := congrArg (·[i]) h.2
  simp only [polyAt, Vector.getElem_ofFn] at e
  rw [← e, Fin.val_ofNat, Nat.mod_eq_of_lt (h.1 i hi)]

theorem inRange_of_norm {m : Mem} {a : Addr} {f : Poly} (h : PolyIs m a f) {B γ : Nat}
    (hn : normRq [f] < B) (hB : B ≤ γ) : InRange m a (γ - 1) γ := by
  intro i hi
  have := (VG.Proof.MlDsa.Round.normRq_lt f B).mp hn i hi
  rw [getElem!_pos f i hi] at this
  rw [coeff_val h hi]
  simp only [normZq] at this
  omega

/-! ## The hint -/

theorem hintAt_of {m : Mem} {a : Addr} {k : Nat} {f : Nat → Vector Bool n}
    (h : ∀ i < k, HintIs m (a + BitVec.ofNat 64 (1024 * i)) 1 [f i]) :
    hintAt m a k = (List.range k).map f := by
  unfold hintAt
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  apply Vector.ext
  intro j hj
  have hn : n = 256 := rfl
  have e := (h i hi).2 0 (by decide) j hj
  simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero] at e
  have ea : coeffAt m a (256 * i + j) = coeffAt m (a + BitVec.ofNat 64 (1024 * i)) j := by
    simp only [coeffAt]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 1024 * i + 4 * j = 4 * (256 * i + j) by omega]
  rw [Vector.getElem_ofFn, ea, e, getElem!_pos (f i) j hj]
  cases (f i)[j] <;> decide

theorem hintOnes_map (k : Nat) (f : Nat → Vector Bool n) :
    hintOnes ((List.range k).map f) = onesSum f k := by
  simp only [hintOnes, onesSum, List.map_map]
  rfl

/-! ## The signature -/

theorem pS_hint (s : State) (i : Nat) :
    pa s (pS (5 + i)) = pa s (Impl.MlDsa.AArch64.Sign.hP 0) + BitVec.ofNat 64 (1024 * i) := by
  show s.gpr .x28 + BitVec.ofNat 64 (oP (5 + i)) = s.gpr .x28 + BitVec.ofNat 64 (oP (5 + 0)) + BitVec.ofNat 64 (1024 * i)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show oP (5 + 0) + 1024 * i = oP (5 + i) by simp only [oP]; omega]

theorem r14_bases (o : Nat) : ((.x23, o) : Ptr).1 ∈ keptRegs := by
  show Reg.x23 ∈ keptRegs; decide

/-- The encodings of the first `r` polynomials of `z`. -/
abbrev zEnc (p : Params) (σ : State) (κ r : Nat) : List Byte :=
  (List.range r).flatMap fun j => bitPack ((Zv p σ κ j).map fun c => modPm c.val q) (p.γ₁ - 1) p.γ₁

def ofam (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  ikChk p ws && famChk (sgR p) (sgW p) ws (yBase p) p.ℓ && famChk (sgR p) (sgW p) ws 5 p.k

/-- What the signature needs of the layout. -/
def oChk (p : Params) : Bool :=
  copyChk (sgR p) (sgW p) (.x23, 0) (sc oCT) (cLen p) && ofam p [((.x23, 0), cLen p)] &&
    (List.range p.ℓ).all (fun r => rwChk (sgR p) (sgW p) (yP p r) 1024 (.x23, sigZ p r) (zLen p) &&
      ofam p [((.x23, sigZ p r), zLen p)] && keepB (sgR p) (sgW p) [((.x23, sigZ p r), zLen p)] (.x23, 0) (cLen p + zLen p * r)) &&
    rwChk (sgR p) (sgW p) (hP 0) (256 * p.k * 4) (.x23, sigH p) (p.ω + p.k) &&
    decide ((p.ω, p.k) ∈ hintParams) && decide ((p.γ₁ - 1, p.γ₁) ∈ bitPackParams) &&
    decide (zLen p = 32 * bitlen (p.γ₁ - 1 + p.γ₁)) && decide (p.sigLen = cLen p + zLen p * p.ℓ + (p.ω + p.k)) &&
    ikChk p [((.x23, sigH p), p.ω + p.k)] &&
    keepB (sgR p) (sgW p) [((.x23, sigH p), p.ω + p.k)] (.x23, 0) (cLen p + zLen p * p.ℓ)

theorem oChk_ok {p : Params} (h : Ok3 p) : oChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

/-- `sigEncode` of what the passing iteration returns. -/
abbrev sigV (p : Params) (σ : State) (κ : Nat) : List Byte :=
  sigOf p (CTv p σ κ, (List.range p.ℓ).map (Zv p σ κ), (List.range p.k).map (Hv p σ κ))

end VG.Proof.MlDsa.AArch64.Sign
