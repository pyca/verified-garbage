module

import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTChecked
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend
public import VerifiedGarbage.Impl.Rsa.X86_64.Folded
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTChecked
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend
meta import VerifiedGarbage.Impl.Rsa.X86_64.Folded
meta import VerifiedGarbage.Spec.Rsa.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

theorem adx_final_ct : RelCT isa (Two GoodL) (Mont.adxSquare.mm aY aX aY) (fun _ _ => True) :=
  RelCT.ofW (tiledDispatch_ct (o := aY) (a := aX) (b := aY) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide))

theorem base_final_ct : RelCT isa (Two GoodL) (Mont.base.mm aY aX aY) (fun _ _ => True) :=
  RelCT.ofW (mm_ct (o := aY) (a := aX) (b := aY) (by decide) (by decide) (by decide) (by taint_decide))

theorem adx_verified : Verified target (Impl.Rsa.X86_64.Folded.checked Mont.adxSquare.mm)
    (Spec.Rsa.publicPrecomputedCheckedContract abi) :=
  checked_verified Mont.adxSquare (by decide +kernel) adx_final_ct

theorem base_verified : Verified target (Impl.Rsa.X86_64.Folded.checked Mont.base.mm)
    (Spec.Rsa.publicPrecomputedCheckedContract abi) :=
  checked_verified Mont.base (by decide +kernel) base_final_ct

end VG.Proof.Bignum.X86_64.FoldedPublic
