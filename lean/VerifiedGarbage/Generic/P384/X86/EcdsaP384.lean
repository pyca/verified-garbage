module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.X86.P384.Verified
import VerifiedGarbage.Proof.Ecdsa.X86.P384.Lit
public import VerifiedGarbage.Impl.Ecdsa.Verify.P384.X86
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86.P384.Verified
import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdsa.Verify.P384
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.X86.Peer
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.Final
import VerifiedGarbage.Proof.Ecdsa.X86.Inv
import VerifiedGarbage.Proof.Ecdsa.X86.Lays
import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
import VerifiedGarbage.Proof.Ecdsa.X86.Setup
import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.NativeTaint
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Mont.X86.Csub
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.P256Red
import VerifiedGarbage.Proof.Mont.X86.RedRow
import VerifiedGarbage.Proof.Mont.X86.Row
import VerifiedGarbage.Proof.Mont.X86.SparseShift
import VerifiedGarbage.Proof.Mont.X86.SparseStep
import VerifiedGarbage.Proof.Mont.X86.Step
import VerifiedGarbage.Proof.P384.Point
import VerifiedGarbage.Proof.Rc2.Memory32
import VerifiedGarbage.Proof.Weierstrass.InvToM
import VerifiedGarbage.Proof.Weierstrass.Words32
import VerifiedGarbage.Proof.Weierstrass.X86.Bits
import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.InvFinishPrep
import VerifiedGarbage.Proof.Weierstrass.X86.InvShiftMath
import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareArithmetic
import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareRed
import VerifiedGarbage.Proof.Weierstrass.X86.P256Power
import VerifiedGarbage.Proof.Weierstrass.X86.Rep
import VerifiedGarbage.Proof.Weierstrass.X86.ScalarPower
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.X25519.X86.Arith
import VerifiedGarbage.Proof.X25519.X86.Fold
import VerifiedGarbage.Impl.Ecdsa.P384.X86
import VerifiedGarbage.Proof.X25519.X86.Column
import VerifiedGarbage.Proof.Framework.X86.TaintMono

/-!
# ECDSA over P-384 (FIPS 186-5) on x86 (32-bit)

A generic file (see `TCB/Emit.lean`) over P-384's group law `h`, the variant
`Variants/P384/X86/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P384.X86.EcdsaP384

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.Ecdsa.P384.signApi.artifact X86.target {
    notes := ["The function saves the callee-saved registers \
      `ebx`, `esi`, `edi` and `ebp` in `scratch`. Field elements and scalars are twelve 32-bit \
      words in Montgomery form, multiplied by word-by-word Montgomery multiplication (CIOS, \
      with `mul` and the accumulator in `scratch`, in calls of `vg_p384_mul_mod_p` and the other \
      functions of `p384_mont`) with a final conditional subtraction. `[k]G` \
      is a double-and-add ladder over all 384 bits of `k`, with the complete addition formulas \
      of Renes, Costello and Batina for every addition and doubling (calls of `vg_p384_point_double` and \
      `vg_p384_point_add`) and a masked selection for \
      each bit; the inversions modulo `p` and `n` are Fermat's, by square-and-always-multiply \
      over the bits of `p - 2` and `n - 2`. The signature (or zeros) is selected by a mask, so \
      the time depends only on the pointers."]
    code := Impl.Ecdsa.X86.signP384
    stack := 28
    verified := Proof.Ecdsa.X86.P384.sign_verified h.law },
  Spec.Ecdsa.P384.verifyApi.artifact X86.target {
    notes := ["The function is `vg_ecdsa_p384_sign`'s setup, \
      field arithmetic, ladder and inversions, with `vg_ecdh_p384`'s checks of the public key: it \
      saves the callee-saved registers `ebx`, `esi`, `edi` and `ebp` in `scratch`; field elements \
      and scalars are twelve 32-bit words in Montgomery form, multiplied by word-by-word Montgomery \
      multiplication (CIOS, with `mul` and the accumulator in `scratch`, in calls of `vg_p384_mul_mod_p` and the other \
      functions of `p384_mont`) with a final conditional \
      subtraction. The key is checked without branches (its first byte, both coordinates below \
      `p`, and the curve's equation), and the second ladder multiplies the key's point if it is \
      valid, else `G`, so it always runs on a point of the curve. `s⁻¹` modulo `n` and `Z⁻¹` are \
      Fermat's, by square-and-always-multiply; `[u]G` and `[v]Q` are double-and-add ladders over \
      all 384 bits of `u` and `v`, with the complete addition formulas of Renes, Costello and \
      Batina (calls of `vg_p384_point_double` and \
      `vg_p384_point_add` in the ladders), which also add the two. The result is the conjunction of the checks (the key, `r` \
      and `s` in `[1, n-1]`, the sum not the point at infinity, and `x ≡ r` modulo `n`) as a \
      mask, so the time depends only on the pointers, although the contract would let every \
      input affect it."]
    code := Impl.Ecdsa.Verify.X86.verifyP384
    stack := 28
    verified := Proof.Ecdsa.Verify.X86.P384.verify_verified h.law }]

end VG.Generic.P384.X86.EcdsaP384
