import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskRows

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64

def maskFour : Prog isa :=
 .seq (Impl.MlDsa.AArch64.Optimized.BoundedFour.maskOne 0)
 (.seq (Impl.MlDsa.AArch64.Optimized.BoundedFour.maskOne 1)
 (.seq (Impl.MlDsa.AArch64.Optimized.BoundedFour.maskOne 2)
       (Impl.MlDsa.AArch64.Optimized.BoundedFour.maskOne 3)))

theorem maskFour_ok {s : State} {b p : Addr} (hb : s.gpr .x19=b) (hp : s.gpr .x21=p)
    (hbound : ∀i<4,(s.mem.readW (countAt b i) 64).toNat≤256)
    (hrc : ∀i<4,InRegions (s.rd++s.wr) (countAt b i) 8)
    (hr : ∀i<4,∀j<64,InRegions (s.rd++s.wr) (outputAt p i+BitVec.ofNat 64 (16*j)) 16)
    (hw : ∀i<4,∀j<64,InRegions s.wr (outputAt p i+BitVec.ofNat 64 (16*j)) 16)
    (hsep : ∀i<4,∀j<4,(⟨countAt b i,8⟩ : Region).Disjoint (Proof.MlDsa.Sample.polyR (outputAt p j))) :
    WP isa maskFour s (fun t=>MaskRows s t b p 4) := by
  unfold maskFour
  refine WP.seq (WP.mono (maskRows_step (by decide) (maskRows_zero s b p) hb hp hbound hrc hr hw hsep) fun a ha=>?_)
  refine WP.seq (WP.mono (maskRows_step (by decide) ha hb hp hbound hrc hr hw hsep) fun b hb'=>?_)
  refine WP.seq (WP.mono (maskRows_step (by decide) hb' hb hp hbound hrc hr hw hsep) fun c hc=>?_)
  exact maskRows_step (by decide) hc hb hp hbound hrc hr hw hsep

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
