module

public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.Impl.Weierstrass.Layout.Mont

/-!
# Montgomery arithmetic modulo a curve's `p` or `n`, a step at a time: the contracts of its internal functions

Not trusted: the contracts of three functions for
each modulus `m` of `moduli` (the primes `p` and the orders `n` of P-192,
P-224, P-256, P-384, P-521, secp256k1, brainpoolP256r1, brainpoolP384r1 and
brainpoolP512r1),
so that the code of a curve's functions can call one copy of its field arithmetic instead of
repeating it at every use:

* `vg_<curve>_mul_mod_<p|n>`: Montgomery's product, the number below `m`
  congruent to `a b R⁻¹` modulo `m`, with `R = 2^(64 k)` for numbers of `k`
  64-bit words, for `b` below `m` (and any `a`);
* `vg_<curve>_add_mod_<p|n>`: `(a + b) mod m`, for `a + b` below `2 m`;
* `vg_<curve>_sub_mod_<p|n>`: `(a - b) mod m`, for `a` and `b` below `m`.

They are not algorithms of a standard but the arithmetic every algorithm on
the curve is built from: what they compute is stated on integers, and an
implementation is free to call them in any form (Montgomery's or not) as long
as its own proof follows what they are.

The numbers live in a working space `ws` of 8192 bytes (`[u64; 1024]`, the
working space of the curve's functions), each `k` 64-bit words, little-endian,
at a byte offset: `o` for the result, `a` and `b` for the operands
(`numAt`). The offsets are arguments, so that the result may be either
operand (`o = a` or `o = b`) and the caller keeps its numbers where it
likes. The `64 k` bytes below byte 4096 of `ws` (`ownAt`) are the function's
own working space, and the numbers lie below them (`Fits`), so that an
implementation reaches all of them with short offsets from the start of
`ws`. On return the function's own bytes are unspecified and may hold
intermediate values; every other byte of `ws` keeps its value but the
result's (`Keeps`).

The result is below `m`. The operands' bounds are those an implementation
by Montgomery's multiplication and a conditional subtraction needs, which
let a caller convert a number below `R` to Montgomery's form (by `R² mod m`)
or reduce one below `2 m` (by adding zero). Everything is secret but the
pointer and the offsets, which are public, and the functions are constant
time.

These are internal functions (`Rust.Internal`): only verified code calls them, so
only their callers' contracts, in `Spec/`, are trusted. The structures, the
layout of the working space and the curves are the code's, in
`Impl/Weierstrass/Layout/Mont.lean`; the definitions here are in their
namespaces, so that they read as fields of them.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.Mont

/-- The number of `k` 64-bit words, little-endian, at byte offset `o` of the
working space `ws`. -/
def numAt (m : Mem) (ws : Addr) (o : BitVec 32) (k : Nat) : Nat :=
  (m.read (ws + BitVec.ofNat 64 o.toNat) (8 * k)).toNat

/-- The number at offset `o` lies below the function's own working space. -/
abbrev Fits (k : Nat) (o : BitVec 32) : Prop := o.toNat + 8 * k ≤ ownAt k

/-- Every byte of `ws` but those of the function's own working space and of
the result at `o` keeps its value. -/
def Keeps (k : Nat) (ws : Addr) (o : BitVec 32) (m m' : Mem) : Prop :=
  ∀ i < wsBytes, (i < ownAt k ∨ 4096 ≤ i) → (i < o.toNat ∨ o.toNat + 8 * k ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- `ws: *mut [u64; 1024], o: u32, a: u32, b: u32`, the offsets public. -/
def sig : Sig where
  params := [("ws", .array true .u64 1024), ("o", .int .u32 true), ("a", .int .u32 true),
    ("b", .int .u32 true)]

namespace Modulus

variable (M : Modulus)

/-- `R = 2^(64 k)`. -/
def R : Nat := 2 ^ (64 * M.k)

/-- What each function requires of the offsets: the numbers lie below its
own working space. -/
def Fit (o a b : BitVec 32) : Prop := Fits M.k o ∧ Fits M.k a ∧ Fits M.k b

/-- `mul`: for `b` below `m`, the number at `o` is below `m` and congruent to
`a b R⁻¹`, that is, its product with `R` is congruent to `a b`. -/
def mulContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws o a b m => M.Fit o a b ∧ numAt m ws b M.k < M.m)
    (post := fun ws o a b m m' _ =>
      numAt m' ws o M.k < M.m ∧
      numAt m' ws o M.k * M.R % M.m = numAt m ws a M.k * numAt m ws b M.k % M.m ∧
      Keeps M.k ws o m m')
    (stack := stack)

/-- `sqr`: `mul` with `a` for `b` (the number at `b` is not read): for `a`
below `m`, the number at `o` is below `m` and congruent to `a² R⁻¹`. -/
def sqrContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws o a b m => M.Fit o a b ∧ numAt m ws a M.k < M.m)
    (post := fun ws o a _ m m' _ =>
      numAt m' ws o M.k < M.m ∧
      numAt m' ws o M.k * M.R % M.m = numAt m ws a M.k * numAt m ws a M.k % M.m ∧
      Keeps M.k ws o m m')
    (stack := stack)

/-- `add`: for `a + b` below `2 m`, the number at `o` is `(a + b) mod m`. -/
def addContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws o a b m => M.Fit o a b ∧ numAt m ws a M.k + numAt m ws b M.k < 2 * M.m)
    (post := fun ws o a b m m' _ =>
      numAt m' ws o M.k = (numAt m ws a M.k + numAt m ws b M.k) % M.m ∧ Keeps M.k ws o m m')
    (stack := stack)

/-- `sub`: for `a` and `b` below `m`, the number at `o` is `(a - b) mod m`,
that is, `(a + m - b) mod m`. -/
def subContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws o a b m => M.Fit o a b ∧ numAt m ws a M.k < M.m ∧ numAt m ws b M.k < M.m)
    (post := fun ws o a b m m' _ =>
      numAt m' ws o M.k = (numAt m ws a M.k + M.m - numAt m ws b M.k) % M.m ∧ Keeps M.k ws o m m')
    (stack := stack)

end Modulus

end VG.Impl.Weierstrass.Mont
