module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Ed25519.X86.VerifyVerified
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Impl.Mont.Mod
import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Spec.Rc2
public import VerifiedGarbage.Proof.Framework.Registration

/-! The complete strict verification equation on baseline i686. -/

@[expose] public section

namespace VG.Artifacts.Ed25519Verify.X86

def artifacts : List Artifact := [
  Spec.Ed25519.verifyEquationApi.artifact X86.target {
    notes := ["Checks canonical point encodings (A's, then R's, by one loop running \
      the decoding twice) and S < L, then evaluates the uncofactored equation using all 512 challenge bits. \
      Computes [k]A - [S]B with one chain of doublings and 4-bit windows of the public \
      scalars, from a table of [1]A to [15]A and one of -[1]B to -[15]B copied into `scratch` \
      from the static `VG_ED25519_VERIFY_NEG_BASE`, skipping the \
      leading zero bytes of k above its low 32, and compares it with -R projectively. \
      Point additions call `vg_ed25519_r32_point_add`, and the decodings' square root's \
      addition chain `vg_gf25519_r32_pow250`. Point tables and callee-saved registers \
      reside in `scratch`."]
    consts := Impl.Ed25519.X86.bConsts
    code := Impl.Ed25519.X86.verifyEquation
    verified := Proof.Ed25519.X86.verify_verified
    stack := 8 }]

end VG.Artifacts.Ed25519Verify.X86
