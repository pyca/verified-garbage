module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.X86.P384.MulVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.X86.P384.MulLit

/-!
# P-384's point multiplication on x86 (32-bit)

`vg_p384_mul` (`Spec/Weierstrass/Mul.lean`), which the signature, the
public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over P-384's group law `h`, the variant
`Variants/P384/X86/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P384.X86.MulP384

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.Weierstrass.Mul.p384.mulApi.artifact X86.target {
    notes := ["The function saves `ebx`, `esi`, `edi` and `ebp` in bytes 2224 to 2239 of `ws` \
      (its argument, which it keeps in `edi`) while it runs. It expands `k` into a table of its \
      bits, one per byte, at bytes 4096 to 4479, copies `Q` to bytes 1456 to 1551 (slots 29 \
      and 30), and runs a double-and-add ladder over the 384 bits of `k`'s 6 64-bit words, from \
      the top, with the complete addition formulas of Renes, Costello and Batina for every \
      addition and doubling and a masked selection for each bit. Field elements are twelve \
      32-bit words in Montgomery form, multiplied by word-by-word Montgomery multiplication \
      (CIOS, with `mul` and the accumulator in `ws`, in calls of `vg_p384_mul_mod_p` and the \
      other functions of `p384_mont`); nothing depends on `k` or `Q` but through masks."]
    code := Impl.Ecdsa.X86.mulP384
    stack := 20
    verified := Proof.Ecdsa.X86.P384.Mul.mul_verified h.law }]

end VG.Generic.P384.X86.MulP384
