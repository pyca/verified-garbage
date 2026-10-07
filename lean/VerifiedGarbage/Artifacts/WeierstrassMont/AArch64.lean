import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Impl.Weierstrass.AArch64.Mont
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontVerified

/-! # Montgomery products modulo the curves' `p` and `n` on AArch64 -/

namespace VG.Artifacts.WeierstrassMont.AArch64

open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.AArch64.Mont VG.Proof.Weierstrass.AArch64.Mont

/-- How the functions work. -/
def notes : List String := ["The function zero-extends the offsets, saves the callee-saved \
  registers it writes in lanes of `v16`–`v19`, stores the modulus in its own working space, and \
  reads `[a]` and `[b]` and writes `[o]` through pointers. The product is word-by-word Montgomery \
  multiplication (CIOS, with `mul` and `umulh`, the accumulator in registers, up to four of the \
  multiplicand's words in registers and the others loaded for each word of the multiplier), with a \
  final conditional subtraction selected by `csel`."]

def artifacts : List Artifact := [
  { p384p.mulApi with
    target := AArch64.target
    doc := p384p.mulApi.doc (notes := notes)
    code := mulFn p384p.k p384p.m
    contract := p384p.mulContract AArch64.abi
    verified := p384p_mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { p521p.mulApi with
    target := AArch64.target
    doc := p521p.mulApi.doc (notes := notes)
    code := mulFn p521p.k p521p.m
    contract := p521p.mulContract AArch64.abi
    verified := p521p_mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }
]

end VG.Artifacts.WeierstrassMont.AArch64
