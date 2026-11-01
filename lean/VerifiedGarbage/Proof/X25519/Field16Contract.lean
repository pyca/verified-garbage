module

public import VerifiedGarbage.Spec.X25519
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Multiplication and powers in curve25519's field, in radix `2^16`, as functions

Not trusted: the contracts of internal functions (`Rust.Internal`), which
only verified code calls, that their proofs are of and that the proofs of
their callers compose. Only the callers' contracts, in `Spec/`, are trusted.

The contracts of functions on
elements of `GF(p)`, `p = 2^255 - 19`, each sixteen 16-bit limbs, so that
the code of Ed25519 that keeps elements this way (the ARMv7 code) can call
one copy of the product instead of repeating it at every use:

* `vg_gf25519_r16_mul`: the product `a b`;
* `vg_gf25519_r16_pow250`: the powers `a^(2^250 - 1)` and `a^11`, the
  addition chain that inversion (`a^(p-2) = (a^(2^250-1))^(2^5) a^11`) and
  decoding's square root (`a^((p-5)/8) = (a^(2^250-1))^(2^2) a`) share, so
  that each finishes it with a few squarings and a product.

It is not an algorithm of a standard but the arithmetic Ed25519 is built
from, in the representation that code keeps elements in: what it computes is
stated on integers, modulo `p`.

An element is sixteen limbs, each a 32-bit little-endian word below `2^16`,
least significant first (`Limbs`): the element `Σ lᵢ 2^(16 i)` (`valAt`),
any number below `2^256` (so not necessarily below `p`). The elements live
in a working space `ws` of 4096 bytes (`[u64; 512]`, the start of Ed25519's
working space), each at a byte offset: `o` for the result, `a` and `b` for
the operands. The offsets are arguments, so that the result may be an
operand and the caller keeps its elements where it likes. `pow250`'s
elements are at fixed offsets instead, of the whole of Ed25519's working
space of 8192 bytes (`[u64; 1024]`, `powWsBytes`), where the ARMv7 Ed25519
code keeps them: `a` at byte 192 (`aAt`), `a^11` at byte 960 (`eAt`) and
`a^(2^250 - 1)` at byte 1024 (`oAt`), with two elements of its own after
them, to byte 1215 (`tmpEnd`). Bytes 1472 to 1631 of `ws` are the functions'
own working space (`ownAt` to `ownEnd`): the 32 limbs of the product, and
room to save the registers they use, so that they need no stack. `mul`'s
elements lie below them (`Fits`). On return a function's own bytes are
unspecified and may hold intermediate values; every other byte of `ws` keeps
its value but the results' (`Keeps`, `Keeps₂`).

The results' limbs are below `2^16` again, so that they can be operands.
Everything is secret but the pointer and `mul`'s offsets, which are public,
and the functions are constant time.
-/

@[expose] public section

namespace VG.Proof.X25519.Field16

open VG.Spec VG.Spec.X25519

/-- The limbs of an element. -/
def limbs : Nat := 16

/-- The bytes of an element: a 32-bit word per limb. -/
def elemBytes : Nat := 4 * limbs

/-- The bytes of the working space. -/
def wsBytes : Nat := 4096

/-- Where the function's own working space starts. -/
def ownAt : Nat := 1472

/-- Where it ends. -/
def ownEnd : Nat := 1632

/-- Limb `i` of the element at byte offset `o` of the working space `ws`. -/
def limbAt (m : Mem) (ws : Addr) (o : BitVec 32) (i : Nat) : Nat :=
  (m.readW (ws + BitVec.ofNat 64 (o.toNat + 4 * i)) 32).toNat

/-- The value of the first `n` limbs of the element at `o`: `Σ lᵢ 2^(16 i)`. -/
def valN (m : Mem) (ws : Addr) (o : BitVec 32) : Nat → Nat
  | 0 => 0
  | n + 1 => valN m ws o n + 2 ^ (16 * n) * limbAt m ws o n

/-- The value of the element at `o`. -/
def valAt (m : Mem) (ws : Addr) (o : BitVec 32) : Nat := valN m ws o limbs

/-- Every limb of the element at `o` is below `2^16`. -/
def Limbs (m : Mem) (ws : Addr) (o : BitVec 32) : Prop := ∀ i < limbs, limbAt m ws o i < 2 ^ 16

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

/-- `mul`: for operands that fit, with limbs below `2^16`, the result at `o`
has limbs below `2^16` and is congruent to `a b` modulo `P`. -/
def mulContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws o a b m => Fits o ∧ Fits a ∧ Fits b ∧ Limbs m ws a ∧ Limbs m ws b)
    (post := fun ws o a b m m' _ =>
      Limbs m' ws o ∧ valAt m' ws o % P = valAt m ws a * valAt m ws b % P ∧ Keeps ws o m m')
    (stack := stack)

/-! ## `pow250` -/

/-- Where `pow250` reads `a`. -/
def aAt : Nat := 192

/-- Where `pow250` writes `a^11`. -/
def eAt : Nat := 960

/-- Where `pow250` writes `a^(2^250 - 1)`. -/
def oAt : Nat := 1024

/-- Where `pow250`'s two elements of its own, after `a^(2^250 - 1)`, end. -/
def tmpEnd : Nat := 1216

/-- The bytes of `pow250`'s working space: Ed25519's. -/
def powWsBytes : Nat := 8192

/-- Every byte of `ws` but those of `pow250`'s results and its own elements
(bytes 960 to 1215) and of its own working space (bytes 1472 to 1631) keeps
its value. -/
def Keeps₂ (ws : Addr) (m m' : Mem) : Prop :=
  ∀ i < powWsBytes, (i < eAt ∨ tmpEnd ≤ i) → (i < ownAt ∨ ownEnd ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- `ws: *mut [u64; 1024]`, the pointer public. -/
def pow250Sig : Sig where
  params := [("ws", .array true .u64 1024)]

/-- `pow250`: for `a` at `aAt` with limbs below `2^16`, the elements at `oAt`
and `eAt` have limbs below `2^16` and are congruent to `a^(2^250 - 1)` and
`a^11` modulo `P`. -/
def pow250Contract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  pow250Sig.contract A
    (pre := fun ws m => Limbs m ws (BitVec.ofNat 32 aAt))
    (post := fun ws m m' _ =>
      Limbs m' ws (BitVec.ofNat 32 oAt) ∧ Limbs m' ws (BitVec.ofNat 32 eAt) ∧
        valAt m' ws (BitVec.ofNat 32 oAt) % P = valAt m ws (BitVec.ofNat 32 aAt) ^ (2 ^ 250 - 1) % P ∧
        valAt m' ws (BitVec.ofNat 32 eAt) % P = valAt m ws (BitVec.ofNat 32 aAt) ^ 11 % P ∧
        Keeps₂ ws m m')
    (stack := stack)

end VG.Proof.X25519.Field16
