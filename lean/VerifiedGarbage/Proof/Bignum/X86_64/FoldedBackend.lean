import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTChecked
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

theorem adx_final_ct : RelCT isa (Two GoodL) (Mont.adxSquare.mm aY aX aY) (fun _ _ => True) :=
  RelCT.ofW (squareDispatch_ct (o := aY) (a := aX) (b := aY) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide) (by taint_decide))

theorem adx_verified : Verified target (Impl.Rsa.X86_64.Folded.checked Mont.adxSquare.mm)
    (Spec.Rsa.publicPrecomputedCheckedContract abi) :=
  checked_verified Mont.adxSquare (by decide +kernel) (by decide +kernel) adx_final_ct

end VG.Proof.Bignum.X86_64.FoldedPublic
