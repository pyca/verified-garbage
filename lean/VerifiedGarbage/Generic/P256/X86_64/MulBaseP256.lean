module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
import VerifiedGarbage.Proof.P256.Comb7
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P256.MulBaseVerified
public import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# P-256's base point multiplication on x86-64

`vg_p256_mul_base_adx` (`Spec/Weierstrass/MulBase.lean`'s `vg_p256_mul_base`
with BMI2's and ADX's products and AVX2's selection), which the signature and
the public key derivation call with those features; without them their comb
stays inline, where the call measured slower. A generic file (see `TCB/Emit.lean`)
over P-256's group law and inversions `h`, the variant
`Variants/P256/X86_64/Law.lean`: the comb's proof takes the group law, and
the curve's facts (`p256_ok`) its inversions.
-/

@[expose] public section

namespace VG.Generic.P256.X86_64.MulBaseP256

open VG.Impl.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P256.MulBase

/-- What the function runs. -/
def note : String :=
  "The function keeps `rbx`, `rbp`, `r12` and `r13` in bytes 992 to 1023 of `ws` (slot 29) and \
  `r14` and `r15` in bytes 1376 to 1391 (slot 41) while it runs, expands `k` into a table of its \
  bits, one per byte, at bytes 1504 to 1767, and runs the fixed-base comb of \
  `vg_ecdsa_p256_sign_adx`: field elements are four 64-bit words in Montgomery form, " ++
  Proof.Ecdsa.X86_64.mulNote true ++ "; the 37 windows `k_j` of \
  `k`'s bits are Booth's digits `d_j = k_j + c_j - 128 c_(j+1)` from `-64` to `64` (`c_j` the bit \
  below window `j`, `c_0 = 0`), `[k]G = Σ [d_j 2^(7j)]G`, from 37 tables of `[m 2^(7j)]G` \
  (`m = 1 … 64`, affine, in Montgomery form) in the static `VG_P256_COMB` (148 KB), with no \
  doublings: each entry is selected in constant time by loading every entry of its table, \
  32 bytes at a time with AVX2, and keeping (`vpand`, `vpor`, under the mask of `vpcmpeqd` of a \
  counter and the magnitude, broadcast) the one of the digit's magnitude (or the point at infinity for a zero \
  digit), negated by a mask of its sign, and added, from `j = 0` up, to a Jacobian accumulator \
  by the mixed addition formulas madd-2004-hmv, which fail only for equal points: the \
  accumulator, the sum of the digits' terms below `j`, is never the entry, since `n` is prime, \
  `[n]G` is the point at infinity and the sums are smaller than any nonzero digit's term modulo \
  `n`. The entry replaces the sum where the accumulator is the point at infinity, and the sum \
  replaces the accumulator unless the digit is zero; the result is `(XZ : Y : Z³)` in projective \
  coordinates (with `Y = 1` for the point at infinity)."

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P256.curve) : List Artifact :=
  [C.mulBaseApi.artifact X86_64.target {
      suffix := "_adx"
      notes := [note]
      consts := p256.combConsts
      code := cfg.mulBaseFn
      verified := mb_verified h.law (Proof.P256.combOk7 h.law) h.inv
      features := ["bmi2", "adx", "avx", "avx2"] }]

end VG.Generic.P256.X86_64.MulBaseP256
