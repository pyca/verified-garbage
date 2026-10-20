module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery multiplication at offsets of a working space, on baseline i686

One function for every width, `vg_rsa_mont_mul_at`, which the RSA functions call. -/

@[expose] public section

namespace VG.Artifacts.RsaMont.X86

def runtime : Artifact :=
  Spec.Rsa.MontMul.mulApi.artifact X86.target {
    notes := ["Coarsely integrated operand scanning on 32-bit words through pointers into the working \
      space, each loop counting its bytes down in a register: every public value is in a register or \
      computed from the arguments, which are read-only. The callee-saved registers, the rows' multiplier, \
      the product and the subtraction's temporary are in the function's range; the result is selected \
      into `o` by a mask."]
    code := Impl.Mont.X86.Rt.body
    verified := Proof.Mont.X86.Rt.rt_verified }

def artifacts : List Artifact := [runtime]

end VG.Artifacts.RsaMont.X86
