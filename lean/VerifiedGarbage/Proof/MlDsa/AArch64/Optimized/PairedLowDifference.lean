import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowCoordinates
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowFieldValues
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedRawField
import VerifiedGarbage.Spec.MlDsa.PairedResponse

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- A raw inverse lane subtracts to exactly the shared paired difference. -/
theorem lowInputField_difference (m : Mem) (challenge secret out : Addr)
    {u e : Nat} (hu : u<8) (he : e<4) (i : LowIndex) (h : Fin 2) (raw : BitVec 128)
    (hr : ofInt (vword raw e).toInt=(pairedProduct m challenge secret i.1.val)[lowCoeff u i h e]!) :
    lowInputField m (lowAddr (out+BitVec.ofNat 64 (16*u)) i h) raw e=
      (pairedDifference m challenge secret out i.1.val)[lowCoeff u i h e]! := by
  have hk := lowCoeff_lt hu he i h
  rw [lowInputField,lowAddr_coeff _ _ _ _ _ he,ofInt_sub,ofInt_nat_eq,
    ←polyAt_get _ _ hk,hr,pairedDifference,sub_get _ _ hk]
  rfl

/-- The raw paired inverse lane has the shared product value and strict range. -/
theorem lowHalf_raw_field {m : Mem} {work challenge secret : Addr} {u e : Nat}
    (hu : u<8) (he : e<4) (i : LowIndex) (h : Fin 2)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (hp : pairedProductsReduced m challenge secret) :
    let raw := lowHalfValue (fun p => Inverse.rawFinalValues
      (readPair (firstPassMem m work challenge secret 8) (work+BitVec.ofNat 64 (16*u)) 128 p)) i h;
    -8380417<(vword raw e).toInt ∧ (vword raw e).toInt<2*8380417 ∧
      ofInt (vword raw e).toInt=(pairedProduct m challenge secret i.1.val)[lowCoeff u i h e]! := by
  have hv := rawFinal_field hu hc hs i.1 (Inverse.positiveReduced_is hp.1)
    (Inverse.positiveReduced_is (hp.2 i.1.val i.1.isLt))
    ⟨2*i.2.val+h.val,by omega⟩ he
  simpa only [lowHalfValue,pairedProduct,pairPolyPtr,lowCoeff_rawIndex] using hv

end VG.Proof.MlDsa.AArch64.Optimized.Paired
