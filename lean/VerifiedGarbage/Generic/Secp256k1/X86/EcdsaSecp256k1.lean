module

import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Weierstrass.X86.InvInterface
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86
import VerifiedGarbage.Proof.Ecdsa.X86.Secp256k1.Verified
public import VerifiedGarbage.Proof.Ecdsa.X86.Secp256k1.Lit
import VerifiedGarbage.Impl.Ecdsa.Verify.Secp256k1.X86
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Secp256k1.Verified
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.X25519.X86.Column
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Framework.X86.TaintMono

/-!
# ECDSA over secp256k1 (FIPS 186-5) on x86 (32-bit)

A generic file (see `TCB/Emit.lean`) over secp256k1's group law `h`, the variant
`Variants/Secp256k1/X86/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.Secp256k1.X86.EcdsaSecp256k1

def artifacts (h : Proof.Weierstrass.X86.Inv.HasLawInv Spec.Secp256k1.curve) : List Artifact := [
  { Spec.Ecdsa.Secp256k1.signApi with
    target := X86.target
    doc := Spec.Ecdsa.Secp256k1.signApi.doc (notes := ["The function saves the callee-saved registers \
      `ebx`, `esi`, `edi` and `ebp` in `scratch`. Field elements and scalars are eight 32-bit \
      words in Montgomery form, multiplied by word-by-word Montgomery multiplication (CIOS, \
      with `mul` and the accumulator in `scratch`, in calls of `vg_secp256k1_mul_mod_p` and the other \
      functions of `secp256k1_mont`) with a final conditional subtraction. `[k]G` \
      is a double-and-add ladder over all 256 bits of `k`, with the complete addition formulas \
      of Renes, Costello and Batina for every addition and doubling (calls of `vg_secp256k1_point_double` and \
      `vg_secp256k1_point_add`) and a masked selection for \
      each bit; the inversions modulo `p` and `n` use constant-time divsteps. The signature (or zeros) is selected by a mask, so \
      the time depends only on the pointers."])
    code := Impl.Ecdsa.X86.signSecp256k1
    contract := Spec.Ecdsa.Secp256k1.inst.signContract X86.abi 28
    stack := 28
    verified := Proof.Ecdsa.X86.Secp256k1.sign_verified h.law h.inv
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Ecdsa.Secp256k1.verifyApi with
    target := X86.target
    doc := Spec.Ecdsa.Secp256k1.verifyApi.doc (notes := ["The function is `vg_ecdsa_secp256k1_sign`'s setup, \
      field arithmetic, ladder and inversions, with `vg_ecdh_secp256k1`'s checks of the public key: it \
      saves the callee-saved registers `ebx`, `esi`, `edi` and `ebp` in `scratch`; field elements \
      and scalars are eight 32-bit words in Montgomery form, multiplied by word-by-word Montgomery \
      multiplication (CIOS, with `mul` and the accumulator in `scratch`, in calls of `vg_secp256k1_mul_mod_p` and the other \
      functions of `secp256k1_mont`) with a final conditional \
      subtraction. The key is checked without branches (its first byte, both coordinates below \
      `p`, and the curve's equation), and the second ladder multiplies the key's point if it is \
      valid, else `G`, so it always runs on a point of the curve. `s⁻¹` modulo `n` and `Z⁻¹` are \
      computed by constant-time divsteps; `[u]G` and `[v]Q` are double-and-add ladders over \
      all 256 bits of `u` and `v`, with the complete addition formulas of Renes, Costello and \
      Batina (calls of `vg_secp256k1_point_double` and \
      `vg_secp256k1_point_add` in the ladders), which also add the two. The result is the conjunction of the checks (the key, `r` \
      and `s` in `[1, n-1]`, the sum not the point at infinity, and `x ≡ r` modulo `n`) as a \
      mask, so the time depends only on the pointers, although the contract would let every \
      input affect it."])
    code := Impl.Ecdsa.Verify.X86.verifySecp256k1
    contract := Spec.Ecdsa.Secp256k1.inst.verifyContract X86.abi 28
    stack := 28
    verified := Proof.Ecdsa.Verify.X86.Secp256k1.verify_verified h.law h.inv
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Generic.Secp256k1.X86.EcdsaSecp256k1
