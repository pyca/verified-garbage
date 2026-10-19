module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP384r1.X86
public import VerifiedGarbage.Proof.Ecdh.X86.BrainpoolP384r1.Verified
import VerifiedGarbage.Proof.Ecdh.X86.BrainpoolP384r1.Lit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP384r1

/-!
# ECDH over brainpoolP384r1 (SP 800-56A) on x86 (32-bit)

A generic file (see `TCB/Emit.lean`) over brainpoolP384r1's group law `h`, the variant
`Variants/BrainpoolP384r1/X86/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.X86.EcdhBrainpoolP384r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP384r1.curve) : List Artifact := [
  Spec.Ecdh.BrainpoolP384r1.exchangeApi.artifact X86.target {
    notes := ["The function is `vg_ecdsa_brainpoolp384r1_sign`'s setup, \
      field arithmetic, ladder and inversion, with the peer's point in place of `G`: it saves the \
      callee-saved registers `ebx`, `esi`, `edi` and `ebp` in `scratch`; field elements are twelve \
      32-bit words in Montgomery form, multiplied by word-by-word Montgomery multiplication (CIOS, \
      with `mul` and the accumulator in `scratch`, in calls of `vg_brainpoolp384r1_mul_mod_p` and the other \
      functions of `brainpoolp384r1_mont`) with a final conditional subtraction. The \
      peer's key is checked without branches (its first byte, both coordinates below `p`, and \
      the curve's equation), and the ladder multiplies the peer's point if it is valid, else \
      `G`, so it always runs on a point of the curve. `[d]P` is a double-and-add ladder over all \
      384 bits of `d`, with the complete addition formulas of Renes, Costello and Batina (calls of \
      `vg_brainpoolp384r1_point_double` and `vg_brainpoolp384r1_point_add`) and a \
      masked selection for each bit; `Z⁻¹` is Fermat's, by square-and-always-multiply. The \
      result (or zeros) is selected by a mask of the checks, `d` in `[1, n-1]` and `Z ≠ 0`, so \
      the time depends only on the pointers."]
    code := Impl.Ecdh.X86.exchangeBrainpoolP384r1
    stack := 28
    verified := Proof.Ecdh.X86.BrainpoolP384r1.ecdh_verified h.law }]

end VG.Generic.BrainpoolP384r1.X86.EcdhBrainpoolP384r1
