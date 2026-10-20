module

public import VerifiedGarbage.TCB.Artifact

/-!
# Modular exponentiation at fixed offsets of a working space

**Trusted.** A callable piece of the DSA functions: `vg_dsa_pow_{n}_{e}`
raises the number at one fixed offset of a working space to the power of
the number at another, modulo the number at a third, and writes the result
at a fourth. DSA's signing and verification exponentiate at many places,
for a few widths; with the offsets fixed in the function's identity, as the
fixed-index products of `Rsa/MontMulFixed.lean` fix theirs, they share one
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

namespace VG.Spec.Dsa.ModPow

/-- The widths and byte offsets of an exponentiation in its working space. -/
structure Layout where
  /-- The 64-bit words of the modulus, the base and the result. -/
  n : Nat
  /-- The 32-bit words of the exponent. -/
  e : Nat
  /-- Byte offsets in the working space. -/
  modulus : Nat
  base : Nat
  exponent : Nat
  result : Nat
  /-- The ranges `(offset, bytes)` of the working space that the function
  may change, the result's among them. -/
  scratch : List (Nat × Nat)
  /-- The bytes of the working space that the function uses. -/
  size : Nat

/-- The number of `bytes` bytes, little-endian, at byte `off` of `ws`. -/
def numAt (m : Mem) (ws : Addr) (off bytes : Nat) : Nat :=
  (m.read (ws + BitVec.ofNat 64 off) bytes).toNat

/-- Every byte of `ws` outside the ranges `rs` keeps its value. -/
def Keeps (ws : Addr) (wsLen : Nat) (rs : List (Nat × Nat)) (m m' : Mem) : Prop :=
  ∀ i < 8 * wsLen, (∀ r ∈ rs, i < r.1 ∨ r.1 + r.2 ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- The working space, in 64-bit words; its address and length are public. -/
def sig : Sig where
  params := [("ws", .slice true .u64 "ws_len")]

/-- For a working space of at least `L.size` bytes and an odd modulus `M`
above 1: the number at `L.result` is `b ^ x mod M`, for the base `b` and the
exponent `x` on entry. Only the bytes of `L.scratch` may change. The address
and length of the working space are public; the numbers, the modulus among
them, are secret. -/
def powContract {I : ISA} (L : Layout) (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws wsLen m =>
      let M := numAt m ws L.modulus (8 * L.n)
      L.size ≤ 8 * wsLen.toNat ∧ M % 2 = 1 ∧ 1 < M)
    (post := fun ws wsLen m m' _ =>
      numAt m' ws L.result (8 * L.n) =
        numAt m ws L.base (8 * L.n) ^ numAt m ws L.exponent (4 * L.e) % numAt m ws L.modulus (8 * L.n) ∧
      Keeps ws wsLen.toNat L.scratch m m')
    (stack := stack)

/-- The ranges as the documentation lists them. -/
def rangesDoc (rs : List (Nat × Nat)) : String :=
  ", ".intercalate (rs.map fun (o, k) => s!"{o}..{o + k}")

/-- The exponentiation of layout `L`, with the same meaning on every target
that registers it. -/
def powApi (L : Layout) : Api where
  module := "dsa"
  name := s!"vg_dsa_pow_{L.n}_{L.e}"
  sig := sig
  contracts := some fun A stack => powContract L A stack
  summary := s!"Modular exponentiation at fixed offsets of a working space: writes at byte \
    {L.result} of `ws` the number `b^x mod m` of {8 * L.n} bytes, for the modulus `m` of \
    {8 * L.n} bytes at byte {L.modulus}, the base `b` of {8 * L.n} bytes at byte {L.base} and \
    the exponent `x` of {4 * L.e} bytes at byte {L.exponent}, each little-endian. Every byte \
    of `ws` but those of the ranges {rangesDoc L.scratch} (the function's own, and the \
    result's) keeps its value.\n\n\
    Contract: `VG.Spec.Dsa.ModPow.powContract`. Constant time but for the address and length \
    of `ws`: timing does not depend on the numbers."
  safety := [s!"`ws_len` must be at least {(L.size + 7) / 8}.",
    s!"The modulus, the {8 * L.n} bytes at byte {L.modulus} of `ws`, must be odd and above 1.",
    s!"The bytes {rangesDoc L.scratch} of `ws` but the result's are unspecified on return and \
      may hold intermediate values, which the caller must destroy if they are secret."]

end VG.Spec.Dsa.ModPow
