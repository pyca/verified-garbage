import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory
import VerifiedGarbage.Proof.MlDsa.Arith.Representation

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- Centered raw products have the existing Montgomery field interpretation;
no canonicalization is needed before passing them to the inverse. -/
theorem productInput_value {s : State} {f g : Poly}
    (hf : PosPolyIs s.mem (s.gpr .x13) f) (hg : PosPolyIs s.mem (s.gpr .x14) g)
    {j e : Nat} (hj : j<64) (he : e<4) :
    ofInt (productInput s (16*j) e).toInt =
      (Representation.product true f g)[4*j+e]! := by
  have hs := productInput_scaled hf hg hj he
  have hc : ofInt 4294967296 * montgomeryRInv = 1 := by decide +kernel
  have heq := congrArg (fun x : Zq => x * montgomeryRInv) hs
  rw [Fin.mul_assoc,hc,Fin.mul_one] at heq
  change _ = (Montgomery.scale montgomeryRInv (multiplyNTT f g))[4*j+e]!
  rw [Montgomery.scale_get,mul_get _ _ (by change 4*j+e<256; omega)]
  exact heq

/-- A stored raw product meets the signed-input inverse's representation and
bounds, including inputs produced by the lazy forward NTT. -/
theorem productMemory_signed {s : State} {m : Mem} {p : Addr} {f g : Poly}
    (hf : PosPolyIs s.mem (s.gpr .x13) f) (hg : PosPolyIs s.mem (s.gpr .x14) g)
    (hw : ∀ j<64, ∀ e<4, coeffAt m p (4*j+e)=productInput s (16*j) e) :
    SignedPolyIs m p (Representation.product true f g) (-(q : Int)) 147168 := by
  constructor
  · intro k hk
    have hj : k/4<64 := by change k<256 at hk; omega
    have he : k%4<4 := Nat.mod_lt _ (by decide)
    have hidx : 4*(k/4)+k%4=k := by omega
    have hb := productInput_bounds hf hg hj he
    rw [← hw _ hj _ he,hidx] at hb
    exact hb
  · intro k hk
    have hj : k/4<64 := by change k<256 at hk; omega
    have he : k%4<4 := Nat.mod_lt _ (by decide)
    have hidx : 4*(k/4)+k%4=k := by omega
    have hv := productInput_value hf hg hj he
    rw [← hw _ hj _ he,hidx] at hv
    exact hv

end VG.Proof.MlDsa.AArch64.Optimized
