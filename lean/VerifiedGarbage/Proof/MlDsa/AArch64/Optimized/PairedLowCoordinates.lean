import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowPassLow
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa

def lowCoeff (u : Nat) (i : LowIndex) (h : Fin 2) (e : Nat) : Nat :=
  4*u+64*i.2.val+32*h.val+e

theorem lowCoeff_lt {u e : Nat} (hu : u<8) (he : e<4) (i : LowIndex) (h : Fin 2) :
    lowCoeff u i h e<n := by unfold lowCoeff n; omega

/-- The paired strided vector lane names exactly its contiguous polynomial coefficient. -/
theorem lowAddr_coeff (m : Mem) (base : Addr) (u : Nat) (i : LowIndex) (h : Fin 2)
    {e : Nat} (he : e<4) :
    vword (m.read (lowAddr (base+BitVec.ofNat 64 (16*u)) i h) 16) e=
      coeffAt m (base+BitVec.ofNat 64 (1024*i.1.val)) (lowCoeff u i h e) := by
  rw [VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he]
  simp only [lowAddr,lowOff,lowCoeff,coeffAt,BitVec.add_assoc,←BitVec.ofNat_add]
  rw [show 16*u+(1024*i.1.val+256*i.2.val+128*h.val)+4*e=
    1024*i.1.val+4*(4*u+64*i.2.val+32*h.val+e) by omega]

theorem lowCoeff_rawIndex (u : Nat) (i : LowIndex) (h : Fin 2) (e : Nat) :
    4*u+32*(2*i.2.val+h.val)+e=lowCoeff u i h e := by unfold lowCoeff; omega

end VG.Proof.MlDsa.AArch64.Optimized.Paired
