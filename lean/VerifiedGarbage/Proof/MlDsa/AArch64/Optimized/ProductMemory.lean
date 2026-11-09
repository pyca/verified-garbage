module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductBatch
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Representation
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon (vword_read16)

theorem ofInt_nat_eq (a : Nat) : ofInt (a : Int) = ofNat a := by
  apply Fin.ext
  change ((a : Int) % (q : Int)).toNat % q = a % q
  rw [← Int.natCast_emod,Int.toNat_natCast,Nat.mod_mod]

end VG.Proof.MlDsa.AArch64.Optimized
