module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.P224.Comb7
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.MulBaseVerified
import VerifiedGarbage.Proof.Ecdsa.X86_64.P224.Lit

/-!
# P-224's base point multiplication on x86-64

`vg_p224_mul_base` (`Spec/Weierstrass/MulBase.lean`), which the signature
and the public key derivation call. A generic file (see `TCB/Emit.lean`)
over P-224's group law and inversions `h`, the variant
`Variants/P224/X86_64/Law.lean`: the comb's proof takes the group law, and
the curve's facts (`p224_ok`) its inversions.
-/

@[expose] public section

namespace VG.Generic.P224.X86_64.MulBaseP224

open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P224.MulBase

/-- What the function runs. -/
def note : String :=
  "The function keeps `rbx`, `rbp`, `r12` and `r13` in bytes 992 to 1023 of `ws` (slot 29) and \
  `r14` and `r15` in bytes 1376 to 1391 (slot 41) while it runs, expands `k` into a table of its \
  bits, one per byte, at bytes 1504 to 1767, and runs the fixed-base comb of \
  `vg_ecdsa_p224_sign`: field elements are four 64-bit words in Montgomery form, multiplied by \
  word-by-word Montgomery multiplication (CIOS) with a final conditional subtraction; the 37 \
  windows `k_j` of the bits of the four words of `k` are digits `k_j - 64` from `-64` to `63`, \
  `[k]G = [64 Σ 2^(7j)]G + Σ [(k_j - 64) 2^(7j)]G`, from 37 tables of `[m 2^(7j)]G` \
  (`m = 1 … 64`, affine, in Montgomery form) in the static `VG_P224_COMB` (148 KB), with no \
  doublings: each entry is selected in constant time by loading every entry of its table, 16 \
  bytes at a time, and keeping (`pand`, `por`) the one of the digit's magnitude, negated by a \
  mask of its sign, and added by the mixed complete addition formulas of Renes, Costello and \
  Batina for `a = -3` (Algorithm 5: the entry's `Z` is 1), the sum replacing the accumulator \
  unless the digit is zero; the result is in projective coordinates."

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P224.curve) : List Artifact :=
  [C.mulBaseApi.artifact X86_64.target {
      notes := [note]
      consts := p224.combConsts
      code := cfg.mulBaseFn
      verified := mb_verified h.law (Proof.P224.combOk7 h.law) h.inv }]

end VG.Generic.P224.X86_64.MulBaseP224
