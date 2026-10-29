module
public import VerifiedGarbage.Impl.Dsa.AArch64.Joint
public import VerifiedGarbage.Proof.Dsa.AArch64.ProductCT

import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Impl.Dsa.AArch64.Joint
meta import VerifiedGarbage.Proof.Dsa.AArch64.ProductCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Constant-time encoding of both bases -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem jointCopy_ct {o a : Nat} (ho : o < 8) (ha : a < 8) (hoa : o ≠ a)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x12 sW, ldh .x16 (sArr a), ldh .x17 (sArr o)])
      hc).isSome = true) :
    RelCT isa (Two fun p : ProductPublic => GoodL p.layout) (seqs (Crt.copyArr o a))
      (Two fun p : ProductPublic => GoodL p.layout) := by
  refine two_post (two_map (fun p : ProductPublic => p.layout.ws) (fun _ _ h => h.goodW)
    (copyArr_ct ho ha hT)) ?_
  intro p s hg
  refine WP.mono (copyArr_ok hg.1 p.fits (by have := p.lower; omega) p.upper ho ha hoa)
    fun t ⟨_, hf, hk⟩ => ?_
  have ha : Arrays p.layout.B p.layout.w [o] s.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self o) hf (Nat.le_refl _) (by omega)
  exact ⟨⟨hg.1.scr.congr hk.wr, (hk.gpr .x0 (by decide)).trans hg.1.x0, ha.hdr hg.1.hdr⟩, p.fits⟩

theorem jointEncode_ct (M : Mont) :
    RelCT isa (Two (Reduced [aR2, aOne])) (Joint.encode M.mm) (fun _ _ => True) := by
  unfold Joint.encode seqs
  apply RelCT.seq (mont_step_ct M (by unfold MmUse; decide) [aR2, aOne] (by decide) (by decide))
  apply RelCT.seq (mont_step_ct M (by unfold MmUse; decide) [aY, aR2, aOne] (by decide) (by decide))
  apply RelCT.seq (mont_step_ct M (by unfold MmUse; decide) [aX, aY, aR2, aOne] (by decide) (by decide))
  apply RelCT.seq (two_map (fun p : ProductPublic => p) (fun p _ h => ⟨h.1.good, p.fits⟩)
    (jointCopy_ct (o := aR2) (a := aX) (by decide) (by decide) (by decide) (by taint_decide)))
  apply RelCT.seq (jointCopy_ct (o := aOne) (a := aY) (by decide) (by decide) (by decide) (by taint_decide))
  exact (jointCopy_ct (o := aX) (a := aY) (by decide) (by decide) (by decide) (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ _ => True.intro)

end VG.Proof.Dsa.AArch64
