module

public import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Tag
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Weave

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Tag
open VG VG.AArch64 VG.Impl.AesGcm.AArch64.Contiguous.Tag
open VG.Proof.Gcm.AArch64.Stitch (fps flatten_singles)

private theorem separate : ∀ nr ∈ [10, 12, 14],
    ((fps.blockFp (mask nr)).bind fun a =>
      (fps.blockFp lengths).map fun b => fps.indep a b) = some true := by
  decide +kernel

/-- Each supported key schedule commutes with the final GHASH block. -/
theorem woven_ok {nr : Nat} (hn : nr = 10 ∨ nr = 12 ∨ nr = 14) {s : State} {Q : State → Prop}
    (h : WP isa (.block (mask nr)) s fun t => WP isa (.block lengths) t Q) :
    WP isa (.block (Impl.Weave.weaveG ((mask nr).map (fun x => [x])) (lengths.map (fun x => [x])))) s Q := by
  refine Interleave.WP.weaveG (P := fps.Inv) ?_ trivial ?_
  · rw [flatten_singles, flatten_singles]
    exact fps.indeps_of_check (separate nr (by rcases hn with rfl | rfl | rfl <;> decide))
  · rwa [flatten_singles, flatten_singles]

end VG.Proof.AesGcm.AArch64.Contiguous.Tag
