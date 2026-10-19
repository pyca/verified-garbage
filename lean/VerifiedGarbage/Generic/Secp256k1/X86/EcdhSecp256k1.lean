module

public import VerifiedGarbage.Proof.Weierstrass.X86.InvInterface
import VerifiedGarbage.Impl.Ecdh.Secp256k1.X86
public import VerifiedGarbage.Proof.Ecdh.X86.Secp256k1.Verified
import VerifiedGarbage.Proof.Ecdh.X86.Secp256k1.Lit
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.Secp256k1

/-!
# ECDH over secp256k1 (SP 800-56A) on x86 (32-bit)

A generic file (see `TCB/Emit.lean`) over secp256k1's group law `h`, the variant
`Variants/Secp256k1/X86/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.Secp256k1.X86.EcdhSecp256k1

def artifacts (h : Proof.Weierstrass.X86.Inv.HasLawInv Spec.Secp256k1.curve) : List Artifact := [
  Spec.Ecdh.Secp256k1.exchangeApi.artifact X86.target {
    notes := ["The function is `vg_ecdsa_secp256k1_sign`'s setup, \
      field arithmetic, ladder and inversion, with the peer's point in place of `G`: it saves the \
      callee-saved registers `ebx`, `esi`, `edi` and `ebp` in `scratch`; field elements are eight \
      32-bit words in Montgomery form, multiplied by word-by-word Montgomery multiplication (CIOS, \
      with `mul` and the accumulator in `scratch`, in calls of `vg_secp256k1_mul_mod_p` and the other \
      functions of `secp256k1_mont`) with a final conditional subtraction. The \
      peer's key is checked without branches (its first byte, both coordinates below `p`, and \
      the curve's equation), and the ladder multiplies the peer's point if it is valid, else \
      `G`, so it always runs on a point of the curve. `[d]P` is a double-and-add ladder over all \
      256 bits of `d`, with the complete addition formulas of Renes, Costello and Batina (calls of \
      `vg_secp256k1_point_double` and `vg_secp256k1_point_add`) and a \
      masked selection for each bit; `Z⁻¹` is computed by constant-time divsteps. The \
      result (or zeros) is selected by a mask of the checks, `d` in `[1, n-1]` and `Z ≠ 0`, so \
      the time depends only on the pointers."]
    code := Impl.Ecdh.X86.exchangeSecp256k1
    stack := 28
    verified := Proof.Ecdh.X86.Secp256k1.ecdh_verified h.law h.inv }]

end VG.Generic.Secp256k1.X86.EcdhSecp256k1
