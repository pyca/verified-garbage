module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.X86.P521.MulVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.X86.P521.MulLit

/-!
# P-521's point multiplication on x86 (32-bit)

`vg_p521_mul` (`Spec/Weierstrass/Mul.lean`), which the signature, the
public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over P-521's group law `h`, the variant
`Variants/P521/X86/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P521.X86.MulP521

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  Spec.Weierstrass.Mul.p521.mulApi.artifact X86.target {
    notes := ["The function saves `ebx`, `esi`, `edi` and `ebp` in bytes 3304 to 3319 of `ws` \
      (its argument, which it keeps in `edi`) while it runs. It expands `k` into a table of its \
      bits, one per byte, at bytes 4096 to 4671, copies `Q` to bytes 2152 to 2295 (slots 29 \
      and 30), and runs a double-and-add ladder over the 576 bits of `k`'s 9 64-bit words, from \
      the top, with the complete addition formulas of Renes, Costello and Batina for every \
      addition and doubling and a masked selection for each bit. Field elements are eighteen \
      32-bit words in Montgomery form, multiplied by word-by-word Montgomery multiplication \
      (CIOS, with `mul` and the accumulator in `ws`, in calls of `vg_p521_mul_mod_p` and the \
      other functions of `p521_mont`); nothing depends on `k` or `Q` but through masks."]
    code := Impl.Ecdsa.X86.mulP521
    stack := 20
    verified := Proof.Ecdsa.X86.P521.Mul.mul_verified h.law }]

end VG.Generic.P521.X86.MulP521
