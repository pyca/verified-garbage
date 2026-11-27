module

public import VerifiedGarbage.Spec.Weierstrass

/-!
# The curve brainpoolP320r1 (RFC 5639)

**Trusted** (as every file in `Spec/`). The domain parameters of brainpoolP320r1,
transcribed from RFC 5639, *Elliptic Curve Cryptography (ECC) Brainpool
Standard Curves and Curve Generation* (March 2010), §3.5, where they are
given in hexadecimal: `p`, `A`, `B`, the base point's `x` and `y`, and its
order `q` (here `n`). The cofactor is 1. Field elements and scalars have
320 bits, so their octet strings have 40 octets (SEC 1 §2.3.5, §2.3.7).
-/

@[expose] public section

namespace VG.Spec.BrainpoolP320r1

/-- The prime `p`. -/
def p : Nat :=
  0xd35e472036bc4fb7e13c785ed201e065f98fcfa6f6f40def4f92b9ec7893ec28fcd412b1f1b32e27

/-- The order of the base point (RFC 5639's `q`). -/
def n : Nat :=
  0xd35e472036bc4fb7e13c785ed201e065f98fcfa5b68f12a32d482ec7ee8658e98691555b44c59311

instance : NeZero p := ⟨by decide +kernel⟩
instance : NeZero n := ⟨by decide +kernel⟩

/-- brainpoolP320r1: `y² = x³ + Ax + B` over `GF(p)`, with 40-octet field elements
and scalars. -/
def curve : Weierstrass.Curve where
  p := p
  a := 0x3ee30b568fbab0f883ccebd46d3f3bb8a2a73513f5eb79da66190eb085ffa9f492f375a97d860eb4
  b := 0x520883949dfdbc42d3ad198640688a6fe13f41349554b49acc31dccd884539816f5eb4ac8fb1f1a6
  gx := 0x43bd7e9afb53d8b85289bcc48ee5bfe6f20137d10a087eb6e7871e2a10a599c710af8d0d39e20611
  gy := 0x14fdd05545ec1cc8ab4093247f77275e0743ffed117182eaa9c77877aaac6ac7d35245d1692e8ee1
  n := n
  len := 40

end VG.Spec.BrainpoolP320r1
