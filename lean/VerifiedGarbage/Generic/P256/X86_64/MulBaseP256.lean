module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
import VerifiedGarbage.Proof.P256.Comb7
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P256.MulBaseVerified
public import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.P256.Comb7
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
public import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Framework.X86_64.Bswap
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.Inline
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Mont.Words128
public import VerifiedGarbage.Proof.Mont.X86_64.Blocks
public import VerifiedGarbage.Proof.Mont.X86_64.CsubS
public import VerifiedGarbage.Proof.Mont.X86_64.Friendly
public import VerifiedGarbage.Proof.Mont.X86_64.Ops
public import VerifiedGarbage.Proof.Mont.X86_64.Round
public import VerifiedGarbage.Proof.Mont.X86_64.Sparse
public import VerifiedGarbage.Proof.Mont.X86_64.SparseX
public import VerifiedGarbage.Proof.Mont.X86_64.SqrPX
public import VerifiedGarbage.Proof.Mont.X86_64.Wide
public import VerifiedGarbage.Proof.Mont.X86_64.WideOps
public import VerifiedGarbage.Proof.P256.Order
public import VerifiedGarbage.Proof.P256.Point
public import VerifiedGarbage.Proof.P256.Prime
public import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
public import VerifiedGarbage.Proof.Weierstrass.TCombWords
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogJ
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontCall
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJ
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Words
public import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Bswap
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Mont.Words128
import VerifiedGarbage.Proof.Mont.X86_64.Blocks
import VerifiedGarbage.Proof.Mont.X86_64.CsubS
import VerifiedGarbage.Proof.Mont.X86_64.Friendly
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Proof.Mont.X86_64.Round
import VerifiedGarbage.Proof.Mont.X86_64.Sparse
import VerifiedGarbage.Proof.Mont.X86_64.SparseX
import VerifiedGarbage.Proof.Mont.X86_64.SqrPX
import VerifiedGarbage.Proof.Mont.X86_64.WideOps
import VerifiedGarbage.Proof.P256.Order
import VerifiedGarbage.Proof.P256.Point
import VerifiedGarbage.Proof.P256.Prime
import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogJ
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontCall
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJ
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
import VerifiedGarbage.Proof.Weierstrass.X86_64.Words

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
  digit), negated by a mask of its sign (the loads of window `j + 1`'s entries spread between the field \
  operations of window `j`'s addition, whose multiplications' latency they fill), and added, from `j = 0` up, to a Jacobian accumulator \
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
