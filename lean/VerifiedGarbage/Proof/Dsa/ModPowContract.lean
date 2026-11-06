module

public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.Impl.Dsa.HelperLayout

/-!
# Modular exponentiation at fixed offsets of a working space

Not trusted: the contracts of internal functions (`Rust.Internal`), which only
verified code calls, that their proofs and their callers' compose.

A callable piece of the DSA functions: `vg_dsa_pow_{n}_{e}`
raises the number at one fixed offset of a working space to the power of
the number at another, modulo the number at a third, and writes the result
at a fourth. DSA's signing and verification exponentiate at many places,
for a few widths; with the offsets fixed in the function's identity, as the
fixed-index products of `Proof/Rsa/MontMulFixedContract.lean` fix theirs, they share one
copy of the code per width instead of repeating it at every use. It is not
an algorithm of a standard but the arithmetic DSA is built from: what it
computes is stated on integers.

A `Layout` gives the widths and the offsets, which the implementation
chooses for its working space: the modulus, the base and the result are
numbers of `8 n` bytes, the exponent of `4 e` bytes, each little-endian.
The function may change the bytes of its `scratch` ranges, which include
the result's; every other byte of the working space keeps its value. Its
timing may depend on the working space's address and length, not on the
numbers.
-/

@[expose] public section

namespace VG.Proof.Dsa.ModPow

open VG.Impl.Dsa.ModPow (Layout)

/-- The number of `bytes` bytes, little-endian, at byte `off` of `ws`. -/
def numAt (m : Mem) (ws : Addr) (off bytes : Nat) : Nat :=
  (m.read (ws + BitVec.ofNat 64 off) bytes).toNat

/-- Every byte of `ws` outside the ranges `rs` keeps its value. -/
def Keeps (ws : Addr) (wsLen : Nat) (rs : List (Nat × Nat)) (m m' : Mem) : Prop :=
  ∀ i < 8 * wsLen, (∀ r ∈ rs, i < r.1 ∨ r.1 + r.2 ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

end VG.Proof.Dsa.ModPow
