module

public import VerifiedGarbage.Spec.Ffdh.KeyGeneration
public import VerifiedGarbage.Spec.Ffdh.VettedGroups

/-!
# Short-exponent key generation for exact vetted safe-prime groups

**Trusted.** RFC 7919 Appendix A.1–A.5 gives the short-exponent minima
for its safe-prime groups (see also §5.2); OpenSSL applies these same lengths to same-size RFC 3526 groups.
Sampling is uniform in `1 .. min(2^N, q)-1` after range rejection, as in
OpenSSL 3.5.7 `crypto/ffc/ffc_key_generate.c`. It does not force the high bit,
reduce modulo q, or reveal the actual sampled exponent length.

Unrecognized domains retain the existing full-width distribution. Imported
keys and their range checks retain their existing meaning. The new native
entry points have distinct names and contracts; existing implementations
continue to implement the original full-width contracts.

Entropy requests remain `p_len` bytes, preserving the native controller
protocol. Only the public exponentiation schedule may use the shorter,
domain-selected maximum bit length (including secret leading zeros).

Sampling source:
https://github.com/openssl/openssl/blob/openssl-3.5.7/crypto/ffc/ffc_key_generate.c
-/

@[expose] public section
namespace VG.Spec.Ffdh

open VG.Spec.Rsa (os2ip powMod)
open VG.Spec.RsaKeyGen (bitLength Rand)

/-- Public sampling width: a vetted group's recommendation, capped by its
scalar bound; otherwise the existing full-width sampling width. -/
def generationScalarBits (a : Parameters) : Nat :=
  match vettedExponentBits a with
  | some bits => min bits (bitLength (scalarBound a))
  | none => bitLength (scalarBound a)

/-- One entropy draw cut to the public policy width. Range and degenerate
public-value rejection remain `keyStatus`, without modulo-q bias. -/
def vettedScalarOfOctets (a : Parameters) (r : List Byte) : Nat :=
  os2ip r % 2 ^ generationScalarBits a

/-- The existing rejection budgets, entropy-refill protocol and permitted
status leakage, with only the scalar-sampling policy replaced. -/
def vettedKeySearch (a : Parameters) (len : Nat) (retries : KeyRetries) (rand : Rand) : KeySearchResult :=
  if retries.keys = 0 ∨ retries.scalars = 0 then ⟨.exhausted, 0, []⟩ else
  if rand.length < len then ⟨.entropy retries, 0, []⟩ else
  let x := vettedScalarOfOctets a (rand.take len)
  let status := keyStatus a x
  if status = 1 then ⟨.accepted x (powMod a.g x a.p), len, [1]⟩ else
  if status = 2 then
    if retries.scalars ≤ 1 then ⟨.exhausted, len, [2]⟩ else
      (vettedKeySearch a len ⟨retries.keys, retries.scalars - 1⟩ (rand.drop len)).consume len 2
  else if status = 3 then
    if retries.keys ≤ 1 then ⟨.exhausted, len, [3]⟩ else
      (vettedKeySearch a len ⟨retries.keys - 1, 128⟩ (rand.drop len)).consume len 3
  else ⟨.exhausted, len, [status]⟩
termination_by 128 * retries.keys + retries.scalars
decreasing_by all_goals omega

end VG.Spec.Ffdh
