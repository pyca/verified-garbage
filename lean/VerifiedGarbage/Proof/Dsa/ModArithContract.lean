module

public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Dsa.ModPowContract
public import VerifiedGarbage.Impl.Dsa.HelperLayout

/-!
# Modular reduction and products at fixed offsets of a working space

Not trusted: the contracts of internal functions (`Rust.Internal`), which only
verified code calls, that their proofs and their callers' compose.

Two more callable pieces of the DSA functions, beside the
exponentiation of `Proof/Dsa/ModPowContract.lean`, in the same working space and with the
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

namespace VG.Proof.Dsa.ModArith

open VG.Spec VG.Spec.Dsa
open VG.Impl.Dsa.ModArith (ReduceLayout MulLayout)

open VG.Proof.Dsa.ModPow (numAt Keeps)

/-! ## Reduction of a byte string -/

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

/-! ## Products -/

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

end VG.Proof.Dsa.ModArith
