module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Secp256k1.X86_64.PointOpsContract
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Secp256k1.X86_64.PointOpsLit

/-! # secp256k1's Jacobian point operations on x86-64 -/

@[expose] public section

namespace VG.Generic.Secp256k1.X86_64.PointOpsSecp256k1

open VG.Impl.Secp256k1.X86_64.PointOps VG.Proof.Secp256k1.X86_64.PointOps

/-- How every function starts and ends, and runs its field operations. -/
def common : String := "The function keeps `rbp` and `r12`–`r15` in `xmm0`–`xmm4` (`movq`) while \
  it runs, and runs the code `vg_ecdsa_secp256k1_verify` would inline: the result into `D` (bytes \
  608 to 703), with the temporaries `t0`–`t5` (bytes 800 to 991), copied back to `P`, its field \
  operations those of secp256k1's verification on four 64-bit words modulo `p` read at byte 64, \
  multiplied with `mul` by word-by-word Montgomery multiplication, the products' temporary area \
  bytes 128 to 159."

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.Secp256k1.curve) : List Artifact :=
  let hFe : Proof.Weierstrass.Point.Fermat C.p := Proof.Weierstrass.Point.fermat_of_law h.law
  [C.doubleApi.artifact X86_64.target {
      code := doubleFn
      verified := double_verified hFe },
    C.addCachedApi.artifact X86_64.target {
      code := addCachedFn
      verified := addCached_verified hFe },
    C.addAffineApi.artifact X86_64.target {
      code := addAffineFn
      verified := addAffine_verified hFe }]

end VG.Generic.Secp256k1.X86_64.PointOpsSecp256k1
