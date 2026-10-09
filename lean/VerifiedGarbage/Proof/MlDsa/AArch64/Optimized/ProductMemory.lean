import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductBatch
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Representation
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon (vword_read16)

/-- SIMD lanes follow consecutive coefficients, including modular addresses. -/
theorem productInput_coeff (s : State) (j e : Nat) (he : e<4) :
    productInput s (16*j) e = centeredProduct
      (coeffAt s.mem (s.gpr .x13) (4*j+e)) (coeffAt s.mem (s.gpr .x14) (4*j+e)) := by
  unfold productInput
  rw [vword_read16 _ _ he,vword_read16 _ _ he]
  have ho : 16*j = 4*(4*j) := by omega
  rw [ho]
  change centeredProduct
    (s.mem.readW (coeffAddr (s.gpr .x13) (4*j)+BitVec.ofNat 64 (4*e)) 32)
    (s.mem.readW (coeffAddr (s.gpr .x14) (4*j)+BitVec.ofNat 64 (4*e)) 32) = _
  rw [coeffAddr_add,coeffAddr_add]
  rfl

theorem productInput_bounds {s : State} {f g : Poly}
    (hf : PosPolyIs s.mem (s.gpr .x13) f) (hg : PosPolyIs s.mem (s.gpr .x14) g)
    {j e : Nat} (hj : j<64) (he : e<4) :
    -(q : Int) ≤ (productInput s (16*j) e).toInt ∧
      (productInput s (16*j) e).toInt ≤ 147168 := by
  rw [productInput_coeff s j e he]
  exact centeredProduct_bounds _ _ (hf.bound _ (by change 4*j+e<256; omega))
    (hg.bound _ (by change 4*j+e<256; omega))

theorem ofInt_nat_eq (a : Nat) : ofInt (a : Int) = ofNat a := by
  apply Fin.ext
  change ((a : Int) % (q : Int)).toNat % q = a % q
  rw [← Int.natCast_emod,Int.toNat_natCast,Nat.mod_mod]

/-- The inverse's final R factor recovers the exact pointwise field product,
even when either input uses a positive noncanonical representative. -/
theorem productInput_scaled {s : State} {f g : Poly}
    (hf : PosPolyIs s.mem (s.gpr .x13) f) (hg : PosPolyIs s.mem (s.gpr .x14) g)
    {j e : Nat} (hj : j<64) (he : e<4) :
    ofInt (productInput s (16*j) e).toInt * ofInt 4294967296 = f[4*j+e]! * g[4*j+e]! := by
  have hi : 4*j+e<n := by change 4*j+e<256; omega
  rw [productInput_coeff s j e he,
    centeredProduct_scaled _ _ (hf.bound _ hi) (hg.bound _ hi),
    ofInt_nat_eq,ofInt_nat_eq,← polyAt_get _ _ hi,← polyAt_get _ _ hi,hf.value,hg.value]

end VG.Proof.MlDsa.AArch64.Optimized
