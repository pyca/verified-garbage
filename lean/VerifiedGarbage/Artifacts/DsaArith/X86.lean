module

public import VerifiedGarbage.Proof.Dsa.X86.MulVerified
public import VerifiedGarbage.Proof.Dsa.X86.MulCall
public import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Framework.Registration

/-! # DSA's products on baseline i686

One product for each width of p and q, that `vg_dsa_sign` and `vg_dsa_verify`
use (`Impl.Dsa.X86.Core.productMod`). -/

@[expose] public section

namespace VG.Artifacts.DsaArith.X86

def mulHelper (n : Nat)
    (v : Verified X86.target (Impl.Dsa.X86.Arith.mulBody n)
      (Spec.Dsa.ModArith.mulContract (Impl.Dsa.X86.Arith.mulLayout n) X86.abi 20)) : Artifact :=
  (Spec.Dsa.ModArith.mulApi (Impl.Dsa.X86.Arith.mulLayout n)).artifact X86.target {
    notes := ["The context's setup of the DSA functions, then two Montgomery multiplications: \
      by R² mod m, which encodes the first operand, and by the second, which decodes their \
      product. The callee-saved registers reside in the header of `ws`."]
    code := Impl.Dsa.X86.Arith.mulBody n
    verified := v
    stack := 20
    spSafe := Code.all_of_allInstrs (Proof.Dsa.X86.Mul.body_spSafe n) }

open Proof.Dsa.X86.Mul in
def artifacts : List Artifact := [
  mulHelper 3 (verified 3),
  mulHelper 4 (verified 4),
  mulHelper 16 (verified 16),
  mulHelper 32 (verified 32),
  mulHelper 48 (verified 48)]

end VG.Artifacts.DsaArith.X86
