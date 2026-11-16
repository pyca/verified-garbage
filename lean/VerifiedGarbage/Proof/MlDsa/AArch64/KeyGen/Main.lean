module

import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp4
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestRow
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecrets
public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Prims
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Hash
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestPack
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.MlKem.Mem
import Std.Tactic.BVDecide.Normalize.Prop
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFold
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp4
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestRow
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecrets
meta import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Prims
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Hash
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestPack
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import Std.Tactic.BVDecide.Normalize.Prop
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFold
meta import VerifiedGarbage.Proof.MlDsa.DecideAt
meta import VerifiedGarbage.TCB.Axioms

/-!
# ML-DSA key generation on AArch64: `vg_mldsa44_keygen`, `vg_mldsa65_keygen`, `vg_mldsa87_keygen`

The function's first and last pieces, for any parameter set of Table 1 and
any verified implementations of the primitives: it returns 1 with
`KeyGen_internal(ξ)` in `pk` and `sk` if every sampler succeeded (for some
bounds), and 0 if key generation fails within the least bounds; it leaks only
the pointers, `ρ` and what `RejBoundedPoly` leaks. The function is
`KeyGen/OptimizedVerified.lean`'s (`Optimized.keyGen_verified`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt bitPack simpleBitPack keyGenInternal)
open VG.Proof.MlDsa (polyAt Reduced PolyIs)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K pkK skK)
open VG.Spec.Sha3 (bytesAt)

/-! ## The keys in memory -/

theorem flatMap_congr_mem {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      flatMap_congr_mem fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem t1Max_eq : Spec.MlDsa.t1Max = 1023 := by decide

theorem pa_zero (s : State) (r : Reg) : pa s (r, 0) = s.gpr r := BitVec.add_zero _

/-! ## `tr = H(pk, 64)` -/

theorem trHash_chk {p : Params} (hF : PFacts p) :
    hashChk kgR (kgW p) [⟨.x26, 0, p.pkLen⟩] ⟨.x27, 64, 64⟩ = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have hlen : lenS p = 96 ∨ lenS p = 128 := hF.eta.imp And.right And.right
  unfold hashChk pieceChk; lay [hF.pk, hF.sk]

theorem trHash_taint {p : Params} (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    ∀ {P : State → State → Prop}, (∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ bases, x.gpr r = y.gpr r) →
      RelCT isa P ((trHashWith keccak.callee) p) fun _ _ => True := by
  intro P hr
  obtain ⟨hint, hh⟩ := keccak.mldsaTrHashTaint p hp
  exact VectorTaint.relRegs bases hr hh

/-! ## The return -/

theorem outcome_of {p : Params} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64}
    (hl : 0 < p.ℓ) (hG : Good p σ (p.k * p.ℓ) (p.ℓ + p.k) A S R) :
    Spec.MlDsa.Outcome (fun b => keyGenInternal p b (xiOf σ)) (R.setWidth 32)
      (pkK p A S (rhoOf p σ), skK p A S (rhoOf p σ) (kOf p σ)) := by
  rcases hG with ⟨rfl, b, hbA, hbS⟩ | ⟨rfl, hn⟩
  · refine .inl ⟨rfl, b, ?_⟩
    show keyGenInternal p b (xiOf σ) = _
    rw [Proof.MlDsa.KeyGen.keyGenInternal_eq,
      Proof.MlDsa.KeyGen.expandA_some (A := fun r s => A (p.ℓ * r + s)) fun r hr s hs => ?_,
      Option.bind_some, Proof.MlDsa.KeyGen.expandS_some (S := S) hbS, Option.map_some,
      Proof.MlDsa.KeyGen.kgRest_eq]
    have := hbA (p.ℓ * r + s) (idx_lt hr hs)
    rwa [Nat.mul_add_div hl, Nat.div_eq_of_lt hs, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hs] at this
  · exact .inr ⟨rfl, hn⟩

end VG.Proof.MlDsa.AArch64.KeyGen
