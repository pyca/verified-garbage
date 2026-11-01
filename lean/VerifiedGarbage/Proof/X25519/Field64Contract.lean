module

public import VerifiedGarbage.Spec.X25519
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Inversion and powers in curve25519's field, in radix `2^64`, as functions

Not trusted: the contracts of internal functions (`Rust.Internal`), which
only verified code calls, that their proofs are of and that the proofs of
their callers compose. Only the callers' contracts, in `Spec/`, are trusted.
They are the contracts of functions on elements of `GF(p)`, `p = 2^255 - 19`,
each four 64-bit words, so that the code of X25519 and Ed25519 that keeps
elements this way (on x86-64 and AArch64) can call one copy of each instead
of repeating it at every use:

* `vg_gf25519_r64_invert`: the inverse `z^(p-2)` (X25519's last step, and
  Ed25519's encoding of a point);
* `vg_gf25519_r64_pow250`: `a^(2^250 - 1)` and `a^11`, the addition chain
  that inversion (`a^(p-2)`) and decoding's square root (`a^((p-5)/8)`)
  share, for code that computes both with the same field operations.

They are not algorithms of a standard but the arithmetic X25519 and Ed25519
are built from, in the representation that code keeps elements in: what they
compute is stated on integers, modulo `p`.

An element is 32 bytes, a little-endian number below `2^256` (`valAt`), not
necessarily below `p`: any 32 bytes are an element. The elements live in a
working space `ws` of 4096 bytes (`[u64; 512]`, X25519's working space and
the start of Ed25519's), at fixed offsets, those where that code keeps them.
The inversion reads `z` at byte 128 (`zAt`) and writes `z^(p-2)` at byte 544
(`invAt`); bytes 512 to 767 (`invOwnAt` to `invOwnEnd`) are its own working
space and its result. On return those bytes but the result are unspecified
and may hold intermediate values; every other byte of `ws` keeps its value
(`InvKeeps`).

`pow250` reads `a` at byte 128 too and writes `a^11` at byte 512 (`p11At`)
and `a^(2^250 - 1)` at byte 544 (`p250At`); bytes 576 to 767 are its own
working space, unspecified on return. Every byte of `ws` outside bytes 512
to 767 keeps its value (`PowKeeps`).

Everything is secret but the pointer, which is public, and the functions are
constant time.
-/

@[expose] public section

namespace VG.Proof.X25519.Field64

open VG.Spec VG.Spec.X25519

/-- The bytes of the working space. -/
def wsBytes : Nat := 4096

/-- The bytes of an element. -/
def elemBytes : Nat := 32

/-- The value of the element at byte offset `o` of the working space `ws`:
its 32 bytes, little-endian. -/
def valAt (m : Mem) (ws : Addr) (o : BitVec 32) : Nat :=
  (m.read (ws + BitVec.ofNat 64 o.toNat) elemBytes).toNat

/-! ## Inversion -/

/-- Where `vg_gf25519_r64_invert` reads `z`. -/
def zAt : BitVec 32 := 128

/-- Where it writes `z^(p-2)`. -/
def invAt : BitVec 32 := 544

/-- Where its own working space, and its result, start. -/
def invOwnAt : Nat := 512

/-- Where they end. -/
def invOwnEnd : Nat := 768

/-- Every byte of `ws` but those of the inversion's own working space and
result (bytes 512 to 767) keeps its value. -/
def InvKeeps (ws : Addr) (m m' : Mem) : Prop :=
  ∀ i < wsBytes, (i < invOwnAt ∨ invOwnEnd ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- `ws: *mut [u64; 512]`, the pointer public. -/
def invSig : Sig where
  params := [("ws", .array true .u64 512)]

/-- `invert`: the element at `invAt` is congruent to `z^(p-2)` modulo `P`, for
`z` the element at `zAt`: the inverse of `z` if `z` is not a multiple of `P`,
and a multiple of `P` if it is. -/
def invertContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  invSig.contract A
    (post := fun ws m m' _ =>
      valAt m' ws invAt % P = valAt m ws zAt ^ (P - 2) % P ∧ InvKeeps ws m m')
    (stack := stack)

/-! ## `pow250` -/

/-- Where `vg_gf25519_r64_pow250` writes `a^11`. -/
def p11At : BitVec 32 := 512

/-- Where it writes `a^(2^250 - 1)`. -/
def p250At : BitVec 32 := 544

/-- Every byte of `ws` but those of `pow250`'s results and own working space
(bytes 512 to 767) keeps its value. -/
def PowKeeps (ws : Addr) (m m' : Mem) : Prop :=
  ∀ i < wsBytes, (i < invOwnAt ∨ invOwnEnd ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- `pow250`: the element at `p250At` is congruent to `a^(2^250 - 1)` and the
one at `p11At` to `a^11`, modulo `P`, for `a` the element at `zAt`. -/
def pow250Contract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  invSig.contract A
    (post := fun ws m m' _ =>
      valAt m' ws p250At % P = valAt m ws zAt ^ (2 ^ 250 - 1) % P ∧
        valAt m' ws p11At % P = valAt m ws zAt ^ 11 % P ∧ PowKeeps ws m m')
    (stack := stack)

end VG.Proof.X25519.Field64
