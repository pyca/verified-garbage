module

public import VerifiedGarbage.Proof.Dsa.ModPowContract
public import VerifiedGarbage.Spec.Rsa.FixedBaseComb
public import VerifiedGarbage.Impl.Dsa.HelperLayout

/-!
# Shared public-base exponentiation for DSA key generation

Not trusted: the contracts of internal functions (`Rust.Internal`), which only
verified code calls, that their proofs and their callers' compose.

Two new callable helpers share RSA's five-tooth comb between
DSA's public subgroup check `g^q mod p` and private-key power `g^x mod p`.
The first initializes the context and computes a public exponentiation;
the second reads that context and computes a secret exponentiation.

These helpers do not validate DSA parameters or sample a scalar. They do
not change `generateKeyContract`, its rejection policy, or `ModPow`'s
existing secret-modulus contract. Callers must still check the domain and
all key-generation results. No parameter-generation API is introduced.

Unlike RSA's byte-oriented precompute API, these helpers accept padded
moduli: the storage width fixes R even when the modulus has leading zeros.
The table itself is exactly `Rsa.FixedBaseComb.table`, not a second comb
algorithm. Context words contain only public data, have no pointers, and
remain immutable during private exponentiation. No cross-call cache or
Rust API is required: a caller may retain the context in its own scratch
for the duration of one key-generation operation.
-/

@[expose] public section
namespace VG.Proof.Dsa.FixedBaseComb

open VG.Spec
open VG.Impl.Dsa.FixedBaseComb (Layout)
open ModPow (numAt Keeps)

/-- Modulus, R-squared, then the existing 32-entry RSA comb table. -/
def contextWords (L : Layout) : Nat := (2 + Rsa.FixedBaseComb.entries) * L.n

/-- Canonical little-endian 64-bit words, with R = 2^(64*n).
The exponent's public storage width, including leading zeros, fixes the
comb schedule. Neither the exponent value nor its actual bit length does. -/
def context (L : Layout) (p g : Nat) : List (BitVec 64) :=
  Rsa.toWords p L.n ++ Rsa.toWords (2 ^ (128 * L.n) % p) L.n ++
    Rsa.FixedBaseComb.table p g (32 * L.e) L.n

/-- The context matches this call's modulus, base and exponent width.
In particular, a table from different parameters cannot satisfy this by
merely having the right length. -/
def contextAt (L : Layout) (m : Mem) (ws : Addr) : Prop :=
  Rsa.wordsAt m (ws + BitVec.ofNat 64 L.context) (contextWords L) =
    context L (numAt m ws L.modulus (8 * L.n)) (numAt m ws L.base (8 * L.n))

/-- Layout bounds and context separation are independent of secret values.
The private helper's scratch cannot overlap the retained context. -/
def LayoutValid (L : Layout) : Prop :=
  0 < L.n ∧ 0 < L.e ∧
    L.context + 8 * contextWords L ≤ L.size ∧
    (∀ r ∈ [(L.modulus, 8 * L.n), (L.base, 8 * L.n),
        (L.exponent, 4 * L.e), (L.result, 8 * L.n)] ++ L.scratch,
      r.1 + r.2 ≤ L.size ∧
        (r.1 + r.2 ≤ L.context ∨ L.context + 8 * contextWords L ≤ r.1))

/-- All arithmetic is defined for every odd modulus above one; primality,
normalization and a subgroup-order relation are not preconditions. -/
def arithmeticPre (L : Layout) (ws : Addr) (wsLen : Nat) (m : Mem) : Prop :=
  LayoutValid L ∧ L.size ≤ 8 * wsLen ∧
    numAt m ws L.modulus (8 * L.n) % 2 = 1 ∧
    1 < numAt m ws L.modulus (8 * L.n)

/-- The ordinary modular-power result, expressed in terms of entry memory. -/
def powerResult (L : Layout) (ws : Addr) (m m' : Mem) : Prop :=
  numAt m' ws L.result (8 * L.n) =
    numAt m ws L.base (8 * L.n) ^ numAt m ws L.exponent (4 * L.e) %
      numAt m ws L.modulus (8 * L.n)

/-- Initialize the context and compute the public exponentiation. The
caller may inspect the result to check g^q = 1 before using the context
for a private exponent. The context is defined even when that check fails. -/
def prepareContract {I : ISA} (L : Layout) (A : Abi I) (stack : Nat := 0) : Contract I :=
  ModPow.sig.contract A
    (pre := fun ws wsLen m => arithmeticPre L ws wsLen.toNat m)
    (post := fun ws wsLen m m' _ =>
      powerResult L ws m m' ∧
      Rsa.wordsAt m' (ws + BitVec.ofNat 64 L.context) (contextWords L) =
        context L (numAt m ws L.modulus (8 * L.n)) (numAt m ws L.base (8 * L.n)) ∧
      Keeps ws wsLen.toNat (L.scratch ++ [(L.context, 8 * contextWords L)]) m m')
    (stack := stack)
    (leak := some fun ws _ m =>
      [numAt m ws L.modulus (8 * L.n), numAt m ws L.base (8 * L.n),
        numAt m ws L.exponent (4 * L.e)])

/-- Use the retained public context with a secret exponent. Only the
modulus and base may affect timing; neither exponent bits, leading zeros,
nor the power result are declassified. The context and all other bytes
outside the arithmetic scratch keep their values. -/
def powerContract {I : ISA} (L : Layout) (A : Abi I) (stack : Nat := 0) : Contract I :=
  ModPow.sig.contract A
    (pre := fun ws wsLen m => arithmeticPre L ws wsLen.toNat m ∧ contextAt L m ws)
    (post := fun ws wsLen m m' _ =>
      powerResult L ws m m' ∧ Keeps ws wsLen.toNat L.scratch m m')
    (stack := stack)
    (leak := some fun ws _ m =>
      [numAt m ws L.modulus (8 * L.n), numAt m ws L.base (8 * L.n)])

end VG.Proof.Dsa.FixedBaseComb
