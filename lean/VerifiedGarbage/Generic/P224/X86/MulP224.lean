module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.X86.P224.MulVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.X86.P224.MulLit

/-!
# P-224's point multiplication on x86 (32-bit)

`vg_p224_mul` (`Spec/Weierstrass/Mul.lean`), which the signature, the
public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over P-224's group law `h`, the variant
`Variants/P224/X86/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P224.X86.MulP224

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  Spec.Weierstrass.Mul.p224.mulApi.artifact X86.target {
    notes := ["The function saves `ebx`, `esi`, `edi` and `ebp` in bytes 1504 to 1519 of `ws` \
      (its argument, which it keeps in `edi`) while it runs. It expands `k` into a table of its \
      bits, one per byte, at bytes 4096 to 4351, copies `Q` to bytes 992 to 1055 (slots 29 \
      and 30), and runs a double-and-add ladder over the 256 bits of `k`'s 4 64-bit words, from \
      the top, with the complete addition formulas of Renes, Costello and Batina for every \
      addition and doubling and a masked selection for each bit. Field elements are eight \
      32-bit words in Montgomery form, multiplied by word-by-word Montgomery multiplication \
      (CIOS, with `mul` and the accumulator in `ws`, in calls of `vg_p224_mul_mod_p` and the \
      other functions of `p224_mont`); nothing depends on `k` or `Q` but through masks."]
    code := Impl.Ecdsa.X86.mulP224
    stack := 20
    verified := Proof.Ecdsa.X86.P224.Mul.mul_verified h.law }]

end VG.Generic.P224.X86.MulP224
