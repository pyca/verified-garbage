module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.P384.X86_64.PointOpsContract
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P384.X86_64.PointOpsLit

/-! # P-384's Jacobian point operations on x86-64 -/

@[expose] public section

namespace VG.Generic.P384.X86_64.PointOpsP384

open VG.Impl.P384.X86_64.PointOps VG.Proof.P384.X86_64.PointOps

/-- How every function starts and ends, and runs its field operations. -/
def common (adx : Bool) : String := "The function keeps `rbp` and `r12`–`r15` in `xmm0`–`xmm4` \
  (`movq`) while it runs, and runs the code `vg_ecdsa_p384_verify" ++ (if adx then "_adx" else "") ++
  "` inlined before it called it: the sum into `D` (bytes 880 to 1023), with the temporaries `t0`–`t5` \
  (bytes 1168 to 1455), copied back to `P`, its field operations those of P-384's verification on \
  six 64-bit words modulo `p` read at byte 64, " ++
  (if adx then "multiplied with BMI2's `mulx` and ADX's `adcx` and `adox` (two carry chains at once)"
    else "multiplied with `mul`") ++
  " and reduced by six rounds of `u p` for `u = t₀ (2³² + 1) mod 2⁶⁴`, the products' temporary area \
  bytes 4048 to 4095."

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P384.curve) : List Artifact :=
  let hFe : Proof.Weierstrass.Point.Fermat C.p := Proof.Weierstrass.Point.fermat_of_law h.law
  [false, true].flatMap fun adx => [
    C.addCachedApi.artifact X86_64.target {
      suffix := if adx then "_adx" else ""
      code := addCachedFn adx
      verified := addCached_verified hFe adx
      features := if adx then ["bmi2", "adx"] else [] },
    C.addAffineApi.artifact X86_64.target {
      suffix := if adx then "_adx" else ""
      code := addAffineFn adx
      verified := addAffine_verified hFe adx
      features := if adx then ["bmi2", "adx"] else [] }]

end VG.Generic.P384.X86_64.PointOpsP384
