import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.P384.X86_64.PointOpsContract

/-!
# P-384's Jacobian point operations on x86-64

`vg_p384_jac_add_cached` and `vg_p384_jac_add_affine`
(`Spec/Weierstrass/PointOps.lean`), and their `_adx` forms, which the joint
verifier calls. A generic file (see `TCB/Emit.lean`) over P-384's group law
`h`, the variant `Variants/P384/X86_64/Law.lean`, which gives Fermat's
little theorem in `Fin p`, so that `R⁻¹ = R^(p-2)` in the contracts.
-/

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

/-- What the additions run. -/
def addWhat (cached : Bool) : String :=
  "Branches on the coordinates, which are public: `Q` copied if `P`'s `Z` is zero, " ++
  (if cached then "`P` kept if `Q`'s, " else "") ++
  "else `H` and `r` from " ++ (if cached then "six" else "four") ++ " products; the doubling of `P` \
  if both are zero, `(0 : 1 : 0)` if only `H` is, else the sum's tail, eight products."

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P384.curve) : List Artifact :=
  let hFe : Proof.Weierstrass.Point.Fermat C.p := Proof.Weierstrass.Point.fermat_of_law h.law
  let one (adx : Bool) (a : Artifact) : Artifact :=
    if adx then { a with name := a.name ++ "_adx", features := ["bmi2", "adx"] } else a
  [false, true].flatMap fun adx => [
    one adx { C.addCachedApi with
      target := X86_64.target
      doc := C.addCachedApi.doc (notes := [common adx, addWhat true])
      code := addCachedFn adx
      contract := C.addCachedContract X86_64.abi
      verified := addCached_verified hFe adx
      spSafe := by
        cases adx
        · exact Code.all_of_allInstrs (by rw [addCachedLit.lit_eq]; decide +kernel)
        · exact Code.all_of_allInstrs (by rw [addCachedAdxLit.lit_eq]; decide +kernel) },
    one adx { C.addAffineApi with
      target := X86_64.target
      doc := C.addAffineApi.doc (notes := [common adx, addWhat false])
      code := addAffineFn adx
      contract := C.addAffineContract X86_64.abi
      verified := addAffine_verified hFe adx
      spSafe := by
        cases adx
        · exact Code.all_of_allInstrs (by rw [addAffineLit.lit_eq]; decide +kernel)
        · exact Code.all_of_allInstrs (by rw [addAffineAdxLit.lit_eq]; decide +kernel) }]

end VG.Generic.P384.X86_64.PointOpsP384
