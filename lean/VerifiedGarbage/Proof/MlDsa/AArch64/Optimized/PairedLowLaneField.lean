import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowFirstFrame

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

/-- Exact high and low field values after the initial inverse pass. -/
theorem lowLane_field {m : Mem} {work challenge secret out : Addr} {u e g : Nat}
    (hu : u<8) (he : e<4) (hg : IsG g) (i : LowIndex) (h : Fin 2) (c : LowConstants)
    (hscale : vword c.scale e=BitVec.ofNat 32 (2*g))
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨out,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) :
    let mem := firstPassMem m work challenge secret 8
    let addr := lowAddr (out+BitVec.ofNat 64 (16*u)) i h
    let raw := lowHalfValue (fun p => Inverse.rawFinalValues (readPair mem (work+BitVec.ofNat 64 (16*u)) 128 p)) i h
    (vword (lowHighOutput g mem addr raw) e).toNat=
        (highBits g (pairedDifference m challenge secret out i.1.val)[lowCoeff u i h e]!).toNat ∧
      (vword (lowLowOutput g mem addr raw c) e).toInt=
        lowBits g (pairedDifference m challenge secret out i.1.val)[lowCoeff u i h e]! := by
  dsimp only
  have hr := lowHalf_raw_field hu he i h hc hs hp
  have hb : (vword ((firstPassMem m work challenge secret 8).read
      (lowAddr (out+BitVec.ofNat 64 (16*u)) i h) 16) e).toNat<q := by
    rw [firstPass_lowInput_read hu i h ho,lowAddr_coeff _ _ _ _ _ he]
    exact hy i.1.val i.1.isLt _ (lowCoeff_lt hu he i h)
  have hv := lowInputField_difference m challenge secret out hu he i h _ hr.2.2
  constructor
  · rw [lowHighOutput_field hg he hb ⟨hr.1,hr.2.1⟩,firstPass_lowInputField hu i h _ e ho,hv]
  · rw [lowLowOutput_field hg he hscale hb ⟨hr.1,hr.2.1⟩,firstPass_lowInputField hu i h _ e ho,hv]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
