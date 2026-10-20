module

public import VerifiedGarbage.Spec.Ffdh.VettedKeyGeneration
public import VerifiedGarbage.Spec.Rsa.FixedBaseComb

/-!
# Reusable public FFDH key-generation context

**Trusted.** The sampling policy is the already reviewed `generationScalarBits`.
The context changes no scalar distribution or acceptance rule. Its public
metadata fixes the exponentiation schedule, including secret leading zeros.
-/

@[expose] public section
namespace VG.Spec.Ffdh

/-- Three metadata words, RSA's modulus/R-squared prefix, and 32 comb entries. -/
def generationPrecomputedWords (pLen : Nat) : Nat :=
  3 + Rsa.FixedBaseComb.precomputedWords pLen

/-- Canonical backend-independent context for one domain.

Words 0, 1 and 2 contain the public maximum bit length, its byte length,
and the number of five-tooth comb rows. The remaining words are exactly
`Rsa.FixedBaseComb.precompute`: `p`, `R² mod p`, then `T[0]` through `T[31]`,
each as `w = ceil(pLen/8)` little-endian 64-bit words, with `R = 2^(64*w)`.
There are no stored pointers. In particular, word 1 may be used as the
public exponent encoding length of a generated private key.

A context contains only public data and may be shared by concurrent calls
that each have their own writable outputs, controller and scratch space.
Its words are immutable while a cached operation uses them. -/
def generationPrecompute (pLen : Nat) (dom : List Byte) : Option (List (BitVec 64)) := do
  let a := domainOf pLen dom
  let bits := generationScalarBits a
  let values ← Rsa.FixedBaseComb.precompute (dom.take pLen) a.g bits
  return [BitVec.ofNat 64 bits, BitVec.ofNat 64 ((bits + 7) / 8),
    BitVec.ofNat 64 (Rsa.FixedBaseComb.rows bits)] ++ values

end VG.Spec.Ffdh
