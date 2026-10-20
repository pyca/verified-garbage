module

public import VerifiedGarbage.Impl.Mont.X86.StaticSquare
public import VerifiedGarbage.Proof.Mont.X86.Rt.Verified
public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape
public import VerifiedGarbage.Proof.Mont.X86.Compact.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery multiplication at offsets of a working space, on baseline i686

One function for every width, `vg_rsa_mont_mul_at`, which the RSA functions call. -/

@[expose] public section

namespace VG.Artifacts.RsaMont.X86

def runtime : Artifact :=
  Spec.Rsa.MontMul.mulApi.artifact X86.target {
    notes := ["Equal public input offsets select a symmetric product-scanning square. At 2048, 3072 and 4096 bits, \
      fixed scalar MUL columns use 96-bit accumulators; other widths retain SSE2 low/high sums. Other \
      products use coarsely integrated operand scanning. Pointers address the working \
      space; byte counts and pointer comparisons control the loops. Every public value is in a register or \
      computed from the arguments, which are read-only. The callee-saved registers, the rows' multiplier, \
      the product and the subtraction's temporary are in the function's range; the result is selected \
      into `o` by a mask."]
    code := Impl.Mont.X86.Rt.body
    verified := Proof.Mont.X86.Rt.rt_verified
    spSafe := Proof.Mont.X86.StaticSquare.body_spSafe }

def prepared : Artifact :=
  Spec.Rsa.Mont.mulApi.artifact X86.target {
    stack := 16
    notes := ["Prepared Montgomery multiplication on paired 32-bit words. Arrays 2 and 3 hold the \
      product and row multiplier; subtraction goes directly into the result after all inputs have \
      been consumed. Four callee-saved registers use a 16-byte stack frame. The prepared modulus \
      and inverse are reused across Miller–Rabin products without operand copies."]
    code := Impl.Mont.X86.Compact.body
    verified := Proof.Mont.X86.Compact.verified }

def artifacts : List Artifact := [runtime, prepared]

end VG.Artifacts.RsaMont.X86
