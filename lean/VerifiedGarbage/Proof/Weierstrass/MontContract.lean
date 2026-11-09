module

public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.Impl.Weierstrass.Layout.Mont

/-!
# Montgomery arithmetic modulo a curve's `p` or `n`, a step at a time: the working space of its internal functions

Not trusted: where three functions for each modulus `m` (the primes `p` and
the orders `n` of P-192, P-224, P-256, P-384, P-521, secp256k1,
brainpoolP256r1, brainpoolP384r1 and brainpoolP512r1) keep their numbers,
which the code of a curve's functions calls instead of repeating its field
arithmetic at every use:

* `vg_<curve>_mul_mod_<p|n>`: Montgomery's product, the number below `m`
  congruent to `a b R⁻¹` modulo `m`, with `R = 2^(64 k)` for numbers of `k`
  64-bit words, for `b` below `m` (and any `a`);
* `vg_<curve>_add_mod_<p|n>`: `(a + b) mod m`, for `a + b` below `2 m`;
* `vg_<curve>_sub_mod_<p|n>`: `(a - b) mod m`, for `a` and `b` below `m`.

The numbers live in a working space `ws` of 8192 bytes (`[u64; 1024]`, the
working space of the curve's functions), each `k` 64-bit words, little-endian,
at a byte offset: `o` for the result, `a` and `b` for the operands
(`numAt`). The offsets are arguments, so that the result may be either
operand (`o = a` or `o = b`) and the caller keeps its numbers where it
likes. The `64 k` bytes below byte 4096 of `ws` (`ownAt`) are the function's
own working space, and the numbers lie below them (`Fits`), so that an
implementation reaches all of them with short offsets from the start of
`ws`. A target whose layout needs more of the working space below them (as
RISC-V's for numbers of more than six words) states the own working space's
start and end itself (`own` and `ownEnd`); every other caller
takes these defaults. On return the function's own bytes are unspecified and may hold
intermediate values; every other byte of `ws` keeps its value but the
result's (`Keeps`).

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

/-- The number at offset `o` lies below the function's own working space,
at `own` (`ownAt k` but where a target's layout puts it elsewhere). -/
abbrev Fits (k : Nat) (o : BitVec 32) (own : Nat := ownAt k) : Prop := o.toNat + 8 * k ≤ own

/-- Every byte of `ws` but those of the function's own working space (from
`own` to `ownEnd`, by default `ownAt k` to 4096) and of the result at `o`
keeps its value. -/
def Keeps (k : Nat) (ws : Addr) (o : BitVec 32) (m m' : Mem) (own : Nat := ownAt k) (ownEnd : Nat := 4096) :
    Prop :=
  ∀ i < wsBytes, (i < own ∨ ownEnd ≤ i) → (i < o.toNat ∨ o.toNat + 8 * k ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

namespace Modulus

variable (M : Modulus)

/-- `R = 2^(64 k)`. -/
def R : Nat := 2 ^ (64 * M.k)

/-- What each function requires of the offsets: the numbers lie below its
own working space. -/
def Fit (o a b : BitVec 32) (own : Nat := ownAt M.k) : Prop := Fits M.k o own ∧ Fits M.k a own ∧ Fits M.k b own

end Modulus

end VG.Impl.Weierstrass.Mont
