module

public import VerifiedGarbage.Impl.Weierstrass.Layout.Inverse
public import VerifiedGarbage.Proof.Weierstrass.PointContract

/-!
# Inverses modulo a curve's prime and order, in its working space, as internal functions

Not trusted: the contracts of two functions for
each curve of `curves` (so far P-192, P-224, P-256, secp256k1, P-384,
P-521, brainpoolP256r1, brainpoolP384r1 and brainpoolP512r1), on the working
space where the
x86-64 code of
the curve's ECDSA signature, verification and public key derivation keeps
its numbers, so that they can call one copy of each inversion instead of
repeating it:

* `vg_<curve>_inv_mod_p(ws)`: `A = Z^(p - 2)` modulo the curve's prime `p`,
  for the number `Z` at slot 16 (the code's `Z` coordinate of `[k]G`);
* `vg_<curve>_inv_mod_n(ws)`: `A = x^(n - 2)` modulo the curve's order `n`,
  for the number `x` at slot 37 (the code's scalar to invert).

Both numbers and the result `A` (slot 29) are in Montgomery's form modulo
their modulus `m` (`p` or `n`): `k` 64-bit words, little-endian, below `m`,
standing for `x R⁻¹` with `R = 2^(64 k)` and `R⁻¹ = R^(m-2)` (`dec`, as
`Proof/Weierstrass/PointContract.lean` decodes coordinates modulo `p`). The result is
stated as the power `pow (dec Z) (m - 2)` of `Weierstrass.pow`, which for a
prime `m` is the inverse of a nonzero `Z` (Fermat's little theorem) and zero
for zero; the code computes it as an inverse, by divsteps, which the proofs
show equal for the curve's prime `p` and order `n`.

The working space `ws` of 8192 bytes is the x86-64 code's: numbers of `k`
words in slots from byte 64 (`slot`), where the caller provides `p` (slot 0)
or `n` (slot 1) and the number to invert. The functions take no offsets.
Slot 30, the curve's temporary slot (`tmpAt`) and the `64 k + 64` bytes from
`workAt` (past the code's three tables of bits), and for P-521 72 more and
for brainpoolP512r1 48 more (`workExtra`, where the AArch64 code keeps the
callee-saved registers its products change), are the functions' own working
space (`Own`); on return they are unspecified and may hold intermediate
values, secret ones among them, and the caller's callee-saved registers.
Every other byte of `ws` keeps its value but the result's (`Keeps`).

Everything is secret but the pointer, which is public, and the functions are
constant time.

These are internal functions (`Rust.Internal`): only verified code calls them, so
only their callers' contracts, in `Spec/`, are trusted. The structures, the
layout of the working space and the curves are the code's, in
`Impl/Weierstrass/Layout/Inverse.lean`; the definitions here are in their
namespaces, so that they read as fields of them.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.Inverse

open Mont (wsBytes numAt)

/-- `ws: *mut [u64; 1024]`. -/
def sig : Sig where
  params := [("ws", .array true .u64 1024)]

namespace Curve

variable (C : Curve)

/-- Byte `i` is in the functions' own working space: slot 30, the temporary
slot, or the working area. -/
def Own (i : Nat) : Prop :=
  (C.slot 30 ≤ i ∧ i < C.slot 31) ∨ (C.tmpAt ≤ i ∧ i < C.tmpAt + 8 * C.k) ∨
    (C.workAt ≤ i ∧ i < C.workAt + C.workLen)

/-- Every byte of `ws` but those of the own working space and of the result
keeps its value. -/
def Keeps (ws : Addr) (m m' : Mem) : Prop :=
  ∀ i < wsBytes, ¬ C.Own i → (i < C.outAt ∨ C.outAt + 8 * C.k ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- The number of `k` words at offset `o` of `ws`. -/
def num (ws : Addr) (m : Mem) (o : Nat) : Nat := numAt m ws (BitVec.ofNat 32 o) C.k

/-- The element of `ℤ/mℤ` that the number `x` stands for in Montgomery's
form: `x R⁻¹`, with `R = 2^(64 k)` and `R⁻¹ = R^(m-2)`. -/
def dec (mod : Nat) [NeZero mod] (x : Nat) : Fin mod :=
  Fin.ofNat mod x * Spec.Weierstrass.pow (Fin.ofNat mod (2 ^ (64 * C.k))) (mod - 2)

/-- The inversion modulo `mod`, at `modAt`, of the number at `inAt`: the
result below `mod`, standing for the power `(m - 2)` of what the number
stands for, and every other byte of `ws` but the own working space's kept. -/
def invContract {I : ISA} (A : Abi I) (mod : Nat) [NeZero mod] (modAt inAt : Nat)
    (stack : Nat := 0) : Contract I :=
  sig.contract A (pre := fun ws m => C.num ws m modAt = mod ∧ C.num ws m inAt < mod)
    (post := fun ws m m' _ => C.num ws m' C.outAt < mod ∧
      C.dec mod (C.num ws m' C.outAt) = Spec.Weierstrass.pow (C.dec mod (C.num ws m inAt)) (mod - 2) ∧
      C.Keeps ws m m')
    (stack := stack)

/-- `inv_mod_p`: `A = Z^(p-2)` modulo `p`. -/
def invPContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  C.invContract A C.W.p C.pAt C.zAt stack

/-- `inv_mod_n`: `A = x^(n-2)` modulo `n`. -/
def invNContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  C.invContract A C.W.n C.nAt C.xAt stack

end Curve

end VG.Impl.Weierstrass.Inverse
