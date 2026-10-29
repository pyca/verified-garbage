module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.Secp256k1.X86_64.PointOpsContract
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Secp256k1.X86_64.PointOpsLit

/-!
# secp256k1's Jacobian point operations on x86-64

`vg_secp256k1_jac_add_cached` and `vg_secp256k1_jac_add_affine`
(`Spec/Weierstrass/PointOps.lean`), which the joint verifier calls. A
generic file (see `TCB/Emit.lean`) over secp256k1's group law `h`, the
variant `Variants/Secp256k1/X86_64/Law.lean`, which gives Fermat's little
theorem in `Fin p`, so that `R⁻¹ = R^(p-2)` in the contracts.
-/

@[expose] public section

namespace VG.Generic.Secp256k1.X86_64.PointOpsSecp256k1

open VG.Impl.Secp256k1.X86_64.PointOps VG.Proof.Secp256k1.X86_64.PointOps

/-- How every function starts and ends, and runs its field operations. -/
def common : String := "The function keeps `rbp` and `r12`–`r15` in `xmm0`–`xmm4` (`movq`) while \
  it runs, and runs the code `vg_ecdsa_secp256k1_verify` would inline: the sum into `D` (bytes 608 \
  to 703), with the temporaries `t0`–`t5` (bytes 800 to 991), copied back to `P`, its field \
  operations those of secp256k1's verification on four 64-bit words modulo `p` read at byte 64, \
  multiplied with `mul` by word-by-word Montgomery multiplication, the products' temporary area \
  bytes 128 to 159."

/-- What the additions run. -/
def addWhat (cached : Bool) : String :=
  "Branches on the coordinates, which are public: `Q` copied if `P`'s `Z` is zero, " ++
  (if cached then "`P` kept if `Q`'s, " else "") ++
  "else `H` and `r` from " ++ (if cached then "six" else "four") ++ " products; the doubling of `P` \
  for `a = 0` (dbl-2009-l) if both are zero, `(0 : 1 : 0)` if only `H` is, else the sum's tail, \
  eight products."

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.Secp256k1.curve) : List Artifact :=
  let hFe : Proof.Weierstrass.Point.Fermat C.p := Proof.Weierstrass.Point.fermat_of_law h.law
  [C.addCachedApi.artifact X86_64.target {
      notes := [common, addWhat true]
      code := addCachedFn
      verified := addCached_verified hFe },
    C.addAffineApi.artifact X86_64.target {
      notes := [common, addWhat false]
      code := addAffineFn
      verified := addAffine_verified hFe }]

end VG.Generic.Secp256k1.X86_64.PointOpsSecp256k1
