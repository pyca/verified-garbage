module

public import VerifiedGarbage.Proof.Mont.X86.MulAtVerified
public import VerifiedGarbage.Proof.Mont.X86.Rt.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery multiplication in the RSA functions' context, as a function, on baseline i686

One function per width of the RSA functions' Montgomery context
(`Impl.Mont.X86.Context`): `PublicFn.widths` and their halves, the CRT
factors' widths; and one function for every width, `vg_rsa_mont_mul`. -/

@[expose] public section

namespace VG.Artifacts.RsaMont.X86

def helper (n : Nat)
    (v : Verified X86.target (Impl.Mont.X86.Dynamic.mulAtBody n)
      (Spec.Rsa.MontMulAt.mulContract (Impl.Mont.X86.Dynamic.ctxLayout n) X86.abi 20)) : Artifact :=
  (Spec.Rsa.MontMulAt.mulApi (Impl.Mont.X86.Dynamic.ctxLayout n)).artifact X86.target {
    notes := ["Coarsely integrated operand scanning on 32-bit words, as the RSA functions' Montgomery \
      multiplication, with each row's multiplier read from `a` through its argument; then the \
      subtraction of the modulus selected by a mask. It saves the callee-saved registers, and \
      copies `b`, in slot 1 of the context, and keeps the product in slot 2 until it copies it to \
      `o`."]
    code := Impl.Mont.X86.Dynamic.mulAtBody n
    verified := v
    stack := 20
    spSafe := Code.all_of_allInstrs (Proof.Mont.X86.Dynamic.mulAt_spSafe n) }

def runtime : Artifact :=
  Spec.Rsa.MontMul.mulApi.artifact X86.target {
    notes := ["Coarsely integrated operand scanning on 32-bit words through pointers into the working \
      space, each loop counting its bytes down in a register: every public value is in a register or \
      computed from the arguments, which are read-only. The callee-saved registers, the rows' multiplier, \
      the product and the subtraction's temporary are in the function's range; the result is selected \
      into `o` by a mask."]
    code := Impl.Mont.X86.Rt.body
    verified := Proof.Mont.X86.Rt.rt_verified }

open Proof.Mont.X86.Dynamic in
def artifacts : List Artifact :=
  runtime :: Impl.Mont.X86.Dynamic.mulWidths.attach.map fun ⟨n, h⟩ => helper n (mulAt_verified_mem h)

end VG.Artifacts.RsaMont.X86
