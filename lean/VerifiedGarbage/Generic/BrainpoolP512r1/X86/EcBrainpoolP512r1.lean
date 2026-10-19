module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.BrainpoolP512r1.X86
import VerifiedGarbage.Proof.EcKey.X86.BrainpoolP512r1.Verified
public import VerifiedGarbage.Proof.EcKey.X86.BrainpoolP512r1.Lit
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1

/-!
# brainpoolP512r1 public keys (FIPS 186-5 §A.2) on x86 (32-bit)

A generic file (see `TCB/Emit.lean`) over brainpoolP512r1's group law `h`, the variant
`Variants/BrainpoolP512r1/X86/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.X86.EcBrainpoolP512r1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.BrainpoolP512r1.curve) : List Artifact := [
  Spec.EcKey.BrainpoolP512r1.publicKeyApi.artifact X86.target {
    notes := ["The function uses the generic Weierstrass ladder and inversion of `Z`: it \
      saves the callee-saved registers `ebx`, `esi`, `edi` and `ebp` in `scratch`; field \
      elements are sixteen 32-bit words in Montgomery form, multiplied by word-by-word Montgomery \
      multiplication (CIOS, with `mul` and the accumulator in `scratch`, in calls of `vg_brainpoolp512r1_mul_mod_p` and the other \
      functions of `brainpoolp512r1_mont`) with a final \
      conditional subtraction; `[d]G` is a double-and-add ladder over all 512 bits of `d`, with \
      the complete addition formulas of Renes, Costello and Batina for every addition and \
      doubling (inlined for eight-word coordinates) and a masked \
      selection for each bit; and `Z⁻¹` is Fermat's, by \
      square-and-always-multiply over the bits of `p - 2`. The result (or zeros) is selected \
      by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, so the time depends only on the pointers."]
    code := Impl.EcKey.X86.publicKeyBrainpoolP512r1
    stack := 20
    verified := Proof.EcKey.X86.BrainpoolP512r1.pk_verified h.law }]

end VG.Generic.BrainpoolP512r1.X86.EcBrainpoolP512r1
