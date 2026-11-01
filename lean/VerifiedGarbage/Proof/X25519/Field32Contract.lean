module

public import VerifiedGarbage.Spec.X25519
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Multiplication and powers in curve25519's field, in radix `2^32`, as functions

Not trusted: the contracts of internal functions (`Rust.Internal`), which
only verified code calls, that their proofs are of and that the proofs of
their callers compose. Only the callers' contracts, in `Spec/`, are trusted.

The contract of a function on
elements of `GF(p)`, `p = 2^255 - 19`, each eight 32-bit words, so that the
code of X25519 and Ed25519 that keeps elements this way (the x86 code) can
call one copy of the product instead of repeating it at every use:

* `vg_gf25519_r32_mul`: the product `a b`;
* `vg_gf25519_r32_pow250`: the powers `a^(2^250 - 1)` and `a^11`, the
  addition chain that inversion (`a^(p-2) = (a^(2^250-1))^(2^5) a^11`) and
  decoding's square root (`a^((p-5)/8) = (a^(2^250-1))^(2^2) a`) share, so
  that each finishes it with a few squarings and a product.

It is not an algorithm of a standard but the arithmetic X25519 and Ed25519
are built from, in the representation that code keeps elements in: what it
computes is stated on integers, modulo `p`.

An element is 32 bytes, a little-endian number below `2^256` (`valAt`), not
necessarily below `p`: any 32 bytes are an element. The elements live in a
working space `ws` of 4096 bytes (`[u64; 512]`, X25519's working space and
the start of Ed25519's), each at a byte offset: `o` for the result, `a`
and `b` for the operands. The offsets are arguments, so that the result may
be an operand and the caller keeps its elements where it likes. `pow250`'s
elements are at fixed offsets instead, where the x86 Ed25519 code keeps
them: `a` at byte 128 (`aAt`), `a^11` at byte 512 (`eAt`) and
`a^(2^250 - 1)` at byte 544 (`oAt`). Bytes 768 to 1023 of `ws` are `mul`'s
own working space (`ownAt` to `ownEnd`), and the elements lie below them
(`Fits`); bytes 576 to 1023 are `pow250`'s (`powOwnAt` to `ownEnd`). On
return a function's own bytes are unspecified and may hold intermediate
values; every other byte of `ws` keeps its value but the results'
(`Keeps`, `Keeps₂`).

Everything is secret but the pointer and `mul`'s offsets, which are public,
and the functions are constant time.
-/

@[expose] public section

namespace VG.Proof.X25519.Field32

open VG.Spec VG.Spec.X25519

/-- The bytes of the working space. -/
def wsBytes : Nat := 4096

/-- The bytes of an element. -/
def elemBytes : Nat := 32

/-- Where the function's own working space starts. -/
def ownAt : Nat := 768

/-- Where it ends. -/
def ownEnd : Nat := 1024

/-- The value of the element at byte offset `o` of the working space `ws`:
its 32 bytes, little-endian. -/
def valAt (m : Mem) (ws : Addr) (o : BitVec 32) : Nat :=
  (m.read (ws + BitVec.ofNat 64 o.toNat) elemBytes).toNat

/-- The element at `o` lies below the function's own working space. -/
abbrev Fits (o : BitVec 32) : Prop := o.toNat + elemBytes ≤ ownAt

/-- Every byte of `ws` but those of the function's own working space and of
the result at `o` keeps its value. -/
def Keeps (ws : Addr) (o : BitVec 32) (m m' : Mem) : Prop :=
  ∀ i < wsBytes, (i < ownAt ∨ ownEnd ≤ i) → (i < o.toNat ∨ o.toNat + elemBytes ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- `ws: *mut [u64; 512], o: u32, a: u32, b: u32`, the offsets public. -/
def sig : Sig where
  params := [("ws", .array true .u64 512), ("o", .int .u32 true), ("a", .int .u32 true),
    ("b", .int .u32 true)]

/-- `mul`: for elements that fit, the result at `o` is congruent to `a b`
modulo `P`. -/
def mulContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun _ o a b _ => Fits o ∧ Fits a ∧ Fits b)
    (post := fun ws o a b m m' _ =>
      valAt m' ws o % P = valAt m ws a * valAt m ws b % P ∧ Keeps ws o m m')
    (stack := stack)

/-! ## `pow250` -/

/-- Where `pow250` reads `a`. -/
def aAt : Nat := 128

/-- Where `pow250` writes `a^11`. -/
def eAt : Nat := 512

/-- Where `pow250` writes `a^(2^250 - 1)`. -/
def oAt : Nat := 544

/-- Where `pow250`'s own working space starts; it ends at `ownEnd`. -/
def powOwnAt : Nat := 576

/-- Every byte of `ws` but those of `pow250`'s results (bytes 512 to 575) and
own working space (bytes 576 to 1023) keeps its value. -/
def Keeps₂ (ws : Addr) (m m' : Mem) : Prop :=
  ∀ i < wsBytes, (i < eAt ∨ ownEnd ≤ i) → m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- `ws: *mut [u64; 512]`, the pointer public. -/
def pow250Sig : Sig where
  params := [("ws", .array true .u64 512)]

/-- `pow250`: the element at `oAt` is congruent to `a^(2^250 - 1)` and the one
at `eAt` to `a^11`, modulo `P`, for `a` the element at `aAt`. -/
def pow250Contract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  pow250Sig.contract A
    (post := fun ws m m' _ =>
      valAt m' ws (BitVec.ofNat 32 oAt) % P = valAt m ws (BitVec.ofNat 32 aAt) ^ (2 ^ 250 - 1) % P ∧
        valAt m' ws (BitVec.ofNat 32 eAt) % P = valAt m ws (BitVec.ofNat 32 aAt) ^ 11 % P ∧
        Keeps₂ ws m m')
    (stack := stack)

end VG.Proof.X25519.Field32
