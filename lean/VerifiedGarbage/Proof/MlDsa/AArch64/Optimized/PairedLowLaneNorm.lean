import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowLaneField

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round

theorem lowLane_norm {m : Mem} {work challenge secret out : Addr} {u e g B : Nat}
    (hu : u<8) (he : e<4) (hg : IsG g) (i : LowIndex) (h : Fin 2) (c : LowConstants)
    (hscale : vword c.scale e=BitVec.ofNat 32 (2*g))
    (hlower : vword c.lower e=BitVec.ofNat 32 (B-1))
    (hwidth : vword c.width e=BitVec.ofNat 32 (2*B-1))
    (hB : 1≤B) (hB' : B≤524288)
    (hc : (⟨challenge,1024⟩ : Region).Disjoint ⟨work,2048⟩)
    (hs : (⟨secret,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (ho : (⟨out,2048⟩ : Region).Disjoint ⟨work,2048⟩)
    (hp : pairedProductsReduced m challenge secret)
    (hy : ∀j<2,Reduced m (pairPolyPtr out j)) :
    let mem := firstPassMem m work challenge secret 8
    let addr := lowAddr (out+BitVec.ofNat 64 (16*u)) i h
    let raw := lowHalfValue (fun p => Inverse.rawFinalValues (readPair mem (work+BitVec.ofNat 64 (16*u)) 128 p)) i h
    lowMask g mem addr raw c e=0 ↔
      normZq (ofInt (lowBits g (pairedDifference m challenge secret out i.1.val)[lowCoeff u i h e]!))<B := by
  dsimp only
  have hr := lowHalf_raw_field hu he i h hc hs hp
  have hb : (vword ((firstPassMem m work challenge secret 8).read
      (lowAddr (out+BitVec.ofNat 64 (16*u)) i h) 16) e).toNat<q := by
    rw [firstPass_lowInput_read hu i h ho,lowAddr_coeff _ _ _ _ _ he]
    exact hy i.1.val i.1.isLt _ (lowCoeff_lt hu he i h)
  have hv := lowInputField_difference m challenge secret out hu he i h _ hr.2.2
  rw [lowMask_zero hg hscale hlower hwidth hb ⟨hr.1,hr.2.1⟩ hB hB',
    firstPass_lowInputField hu i h _ e ho,hv]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
