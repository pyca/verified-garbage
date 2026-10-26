module

public import VerifiedGarbage.Impl.Mont.X86.Sse2
public import VerifiedGarbage.Proof.Mont.X86.Sse2.AtVerified
public import VerifiedGarbage.Proof.Mont.X86.Sse2.PreparedVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery multiplication on i686 with SSE2

`vg_rsa_mont_mul_at`, at offsets of a working space, which the RSA functions
call, and `vg_rsa_mont_mul`, in the prepared working space, which the
Miller–Rabin rounds call: one kernel, each with its own parameters. -/

@[expose] public section

namespace VG.Artifacts.RsaMont.X86

def runtime : Artifact :=
  Spec.Rsa.MontMul.mulApi.artifact X86.target {
    stack := 56
    notes := ["Product scanning with SSE2: PMULUDQ multiplies two pairs of 32-bit words at once and \
      PADDQ accumulates each column's products and their high halves in 64-bit lanes. Four-word \
      groups use two 128-bit operand loads and PSHUFD for the odd words, inside an MCDT frame \
      (Intel's MXCSR prologue and epilogue). Each column folds the lanes, adds the carry, and stores a \
      quotient digit or a word of the result; equal operand offsets select a square's half of the \
      products, doubled, and the diagonal. The final subtraction's result is selected by a mask. \
      Pointers, counts and the column index control the loops; they are in registers or in a frame of \
      28 bytes of parameters, computed from the arguments."]
    code := Impl.Mont.X86.Sse2.atBody
    verified := Proof.Mont.X86.Sse2.at_verified }

def prepared : Artifact :=
  Spec.Rsa.Mont.mulApi.artifact X86.target {
    stack := 56
    notes := ["The kernel of `vg_rsa_mont_mul_at` (product scanning with SSE2 PMULUDQ in an MCDT \
      frame), its parameters from the header: the arrays' addresses, `-m⁻¹ mod 2³²` and `w`. Arrays 2 and \
      3 hold the columns' sums, carry, quotient digits and product."]
    code := Impl.Mont.X86.Sse2.preparedBody
    verified := Proof.Mont.X86.Sse2.prepared_verified }

def artifacts : List Artifact := [runtime, prepared]

end VG.Artifacts.RsaMont.X86
