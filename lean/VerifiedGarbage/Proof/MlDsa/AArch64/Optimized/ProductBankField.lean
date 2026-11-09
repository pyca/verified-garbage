module
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductBatch
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Representation
public import VerifiedGarbage.Proof.MlDsa.Arith.Representation

import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon (vword_read16)

/-- Shifted input pointers select the corresponding global coefficient. -/
theorem productInput_offset {s : State} {a b : Addr} {u j e : Nat}
    (ha : s.gpr .x13=a+BitVec.ofNat 64 (128*u))
    (hb : s.gpr .x14=b+BitVec.ofNat 64 (128*u)) (he : e<4) :
    productInput s (16*j) e=centeredProduct
      (coeffAt s.mem a (32*u+4*j+e)) (coeffAt s.mem b (32*u+4*j+e)) := by
  unfold productInput
  rw [ha,hb,vword_read16 _ _ he,vword_read16 _ _ he]
  simp only [coeffAt,BitVec.add_assoc,← BitVec.ofNat_add]
  congr 3 <;> congr 1 <;> omega

end VG.Proof.MlDsa.AArch64.Optimized
