import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedHintPack

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen

/-- All arithmetic uses the same Montgomery factor until the inverse removes
it; packed output is identical to the canonical verification algorithm. -/
theorem row_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {σ s : State} (hp : vPre p S σ) {h : List (Vector Bool n)} {A' : Nat→Nat→Poly}
    {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s) :
    WP isa (Impl.MlDsa.AArch64.Verify.Optimized.row P p r) s (SC p S σ h A' c0 q p.ℓ true (r+1)) := by
  unfold Impl.MlDsa.AArch64.Verify.Optimized.row
  refine WP.seq (WP.mono (dot_ok hF hp hr hs) fun s ⟨hs,hw⟩=>?_)
  refine WP.seq (WP.mono (unpack_ok hP hF hp hr hs hw) fun s ⟨hs,hw,ht⟩=>?_)
  refine WP.seq (WP.mono (nttT_ok hF hp hr hs hw ht) fun s ⟨hs,hw,ht⟩=>?_)
  refine WP.seq (WP.mono (product_ok hF hp hr hs hw ht) fun s ⟨hs,hw,ht⟩=>?_)
  refine WP.seq (WP.mono (subtract_ok hF hp hr hs hw ht) fun s ⟨hs,hw⟩=>?_)
  refine WP.seq (WP.mono (inverse_ok hF hp hr hs hw) fun s ⟨hs,hw⟩=>?_)
  exact hintPack_ok hF hp hr hs hw

end VG.Proof.MlDsa.AArch64.Verify.Optimized
