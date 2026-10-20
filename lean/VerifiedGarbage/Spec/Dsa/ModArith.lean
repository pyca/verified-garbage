module

public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Dsa.ModPow

/-!
# Modular reduction and products at fixed offsets of a working space

**Trusted.** Two more callable pieces of the DSA functions, beside the
exponentiation of `Dsa/ModPow.lean`, in the same working space and with the
same conventions (`ModPow.numAt`, `ModPow.Keeps`):

* `vg_dsa_reduce_{n}` reduces a big-endian byte string modulo the number at
  a fixed offset, into another (DSA reduces digests and powers modulo q);
* `vg_dsa_mulmod_{n}` multiplies the numbers at two fixed offsets modulo the
  number at a third, into a fourth.

Each `Layout` gives the width and the offsets, which the implementation
chooses for its working space: the modulus, the operands and the result are
numbers of `8 n` bytes, each little-endian. The function may change the bytes
of its `scratch` ranges, which include the result's; every other byte of the
working space keeps its value. Their timing may depend on the addresses and
lengths of their buffers, not on the numbers or the bytes.
-/

@[expose] public section

namespace VG.Spec.Dsa.ModArith

open VG.Spec.Dsa.ModPow (numAt Keeps rangesDoc)

/-! ## Reduction of a byte string -/

/-- The width and byte offsets of a reduction in its working space. -/
structure ReduceLayout where
  /-- The 64-bit words of the modulus and the result. -/
  n : Nat
  /-- Byte offsets in the working space. -/
  modulus : Nat
  result : Nat
  /-- The ranges `(offset, bytes)` of the working space that the function
  may change, the result's among them. -/
  scratch : List (Nat × Nat)
  /-- The bytes of the working space that the function uses. -/
  size : Nat

/-- The working space, in 64-bit words, and the bytes; their addresses and
lengths are public. -/
def reduceSig : Sig where
  params := [("ws", .slice true .u64 "ws_len"), ("data", .slice false .u8 "data_len")]

/-- For a working space of at least `L.size` bytes and an odd modulus `M`
above 255: the number at `L.result` is the bytes' big-endian value modulo
`M`. Only the bytes of `L.scratch` may change. -/
def reduceContract {I : ISA} (L : ReduceLayout) (A : Abi I) (stack : Nat := 0) : Contract I :=
  reduceSig.contract A
    (pre := fun ws wsLen _ _ m =>
      let M := numAt m ws L.modulus (8 * L.n)
      L.size ≤ 8 * wsLen.toNat ∧ M % 2 = 1 ∧ 255 < M)
    (post := fun ws wsLen data dataLen m m' _ =>
      numAt m' ws L.result (8 * L.n) =
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m data dataLen.toNat) % numAt m ws L.modulus (8 * L.n) ∧
      Keeps ws wsLen.toNat L.scratch m m')
    (stack := stack)

/-- The reduction of layout `L`, with the same meaning on every target that
registers it. -/
def reduceApi (L : ReduceLayout) : Api where
  module := "dsa"
  name := s!"vg_dsa_reduce_{L.n}"
  sig := reduceSig
  contracts := some fun A stack => reduceContract L A stack
  summary := s!"Modular reduction at fixed offsets of a working space: writes at byte \
    {L.result} of `ws` the number of {8 * L.n} bytes congruent modulo `m` to the big-endian \
    value of the `data_len` bytes at `data`, and below `m`, for the modulus `m` of {8 * L.n} \
    bytes at byte {L.modulus}, little-endian. Every byte of `ws` but those of the ranges \
    {rangesDoc L.scratch} (the function's own, and the result's) keeps its value.\n\n\
    Contract: `VG.Spec.Dsa.ModArith.reduceContract`. Constant time but for the addresses and \
    lengths of `ws` and `data`: timing does not depend on the numbers or the bytes."
  safety := [s!"`ws_len` must be at least {(L.size + 7) / 8}.",
    s!"The modulus, the {8 * L.n} bytes at byte {L.modulus} of `ws`, must be odd and above 255.",
    s!"The bytes {rangesDoc L.scratch} of `ws` but the result's are unspecified on return and \
      may hold intermediate values, which the caller must destroy if they are secret."]

/-! ## Products -/

/-- The width and byte offsets of a product in its working space. -/
structure MulLayout where
  /-- The 64-bit words of the modulus, the operands and the result. -/
  n : Nat
  /-- Byte offsets in the working space. -/
  modulus : Nat
  a : Nat
  b : Nat
  result : Nat
  /-- The ranges `(offset, bytes)` of the working space that the function
  may change, the result's among them. -/
  scratch : List (Nat × Nat)
  /-- The bytes of the working space that the function uses. -/
  size : Nat

/-- For a working space of at least `L.size` bytes and an odd modulus `M`
above 1: the number at `L.result` is `a b mod M`, for the numbers `a` and `b`
at `L.a` and `L.b` on entry. Only the bytes of `L.scratch` may change. -/
def mulContract {I : ISA} (L : MulLayout) (A : Abi I) (stack : Nat := 0) : Contract I :=
  ModPow.sig.contract A
    (pre := fun ws wsLen m =>
      let M := numAt m ws L.modulus (8 * L.n)
      L.size ≤ 8 * wsLen.toNat ∧ M % 2 = 1 ∧ 1 < M)
    (post := fun ws wsLen m m' _ =>
      numAt m' ws L.result (8 * L.n) =
        numAt m ws L.a (8 * L.n) * numAt m ws L.b (8 * L.n) % numAt m ws L.modulus (8 * L.n) ∧
      Keeps ws wsLen.toNat L.scratch m m')
    (stack := stack)

/-- The product of layout `L`, with the same meaning on every target that
registers it. -/
def mulApi (L : MulLayout) : Api where
  module := "dsa"
  name := s!"vg_dsa_mulmod_{L.n}"
  sig := ModPow.sig
  contracts := some fun A stack => mulContract L A stack
  summary := s!"Modular multiplication at fixed offsets of a working space: writes at byte \
    {L.result} of `ws` the number `a b mod m` of {8 * L.n} bytes, for the modulus `m` of \
    {8 * L.n} bytes at byte {L.modulus} and the numbers `a` and `b` of {8 * L.n} bytes at bytes \
    {L.a} and {L.b}, each little-endian. Every byte of `ws` but those of the ranges \
    {rangesDoc L.scratch} (the function's own, and the result's) keeps its value.\n\n\
    Contract: `VG.Spec.Dsa.ModArith.mulContract`. Constant time but for the address and length \
    of `ws`: timing does not depend on the numbers."
  safety := [s!"`ws_len` must be at least {(L.size + 7) / 8}.",
    s!"The modulus, the {8 * L.n} bytes at byte {L.modulus} of `ws`, must be odd and above 1.",
    s!"The bytes {rangesDoc L.scratch} of `ws` but the result's are unspecified on return and \
      may hold intermediate values, which the caller must destroy if they are secret."]

end VG.Spec.Dsa.ModArith
