module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Correct
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseLCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCTBase
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseD
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Rel

/-!
# ML-DSA signing on AArch64: the signature leaks only the hint

Two runs agree on their hints (`HJ`), whose coefficients, as numbers, are
then the same (`hint_coeffs`).
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

theorem hint_coeffs {x y : State} {k : Nat} {f : Nat → Vector Bool n} (hx : HFam x 5 k f) (hy : HFam y 5 k f) :
    (List.range (256 * k)).map (fun i => (coeffAt x.mem (pa x (Impl.MlDsa.AArch64.Sign.hP 0)) i).toNat) =
      (List.range (256 * k)).map (fun i => (coeffAt y.mem (pa y (Impl.MlDsa.AArch64.Sign.hP 0)) i).toNat) := by
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  have e : ∀ s : State, coeffAt s.mem (pa s (Impl.MlDsa.AArch64.Sign.hP 0)) i =
      coeffAt s.mem (pa s (pS (5 + i / 256))) (i % 256) := fun s => by
    rw [pS_hint s (i / 256)]
    simp only [coeffAt]
    rw [BitVec.add_assoc (pa s (Impl.MlDsa.AArch64.Sign.hP 0)) (BitVec.ofNat 64 (1024 * (i / 256))), ← BitVec.ofNat_add,
      show 1024 * (i / 256) + 4 * (i % 256) = 4 * i by omega]
  have hq : i / 256 < k := by omega
  have hj : i % 256 < n := Nat.mod_lt _ (by decide)
  have ex := (hx _ hq).2 0 (by decide) _ hj
  have ey := (hy _ hq).2 0 (by decide) _ hj
  simp only [Nat.mul_zero, Nat.zero_add] at ex ey
  rw [e x, e y, ex, ey]

/-- Two runs agree on their hints. -/
abbrev HJ (p : Params) (x y : State) : Prop := ∃ f, HFam x 5 p.k f ∧ HFam y 5 p.k f

end VG.Proof.MlDsa.AArch64.Sign
