import VerifiedGarbage.Spec.X25519
import VerifiedGarbage.TCB.Artifact

/-!
# Multiplication in curve25519's field, in radix `2^16`, as a function

**Trusted** (as every file in `Spec/`). The contract of a function on
elements of `GF(p)`, `p = 2^255 - 19`, each sixteen 16-bit limbs, so that
the code of Ed25519 that keeps elements this way (the ARMv7 code) can call
one copy of the product instead of repeating it at every use:

* `vg_gf25519_r16_mul`: the product `a b`.

It is not an algorithm of a standard but the arithmetic Ed25519 is built
from, in the representation that code keeps elements in: what it computes is
stated on integers, modulo `p`.

An element is sixteen limbs, each a 32-bit little-endian word below `2^16`,
least significant first (`Limbs`): the element `Σ lᵢ 2^(16 i)` (`valAt`),
any number below `2^256` (so not necessarily below `p`). The elements live
in a working space `ws` of 4096 bytes (`[u64; 512]`, the start of Ed25519's
working space), each at a byte offset: `o` for the result, `a` and `b` for
the operands. The offsets are arguments, so that the result may be an
operand and the caller keeps its elements where it likes. Bytes 1472 to 1599
of `ws` are the function's own working space (`ownAt` to `ownEnd`), and the
elements lie below them (`Fits`). On return the function's own bytes are unspecified and
may hold intermediate values; every other byte of `ws` keeps its value but
the result's (`Keeps`).

The result's limbs are below `2^16` again, so that it can be an operand.
Everything is secret but the pointer and the offsets, which are public, and
the function is constant time.
-/

namespace VG.Spec.X25519.Field16

/-- The limbs of an element. -/
def limbs : Nat := 16

/-- The bytes of an element: a 32-bit word per limb. -/
def elemBytes : Nat := 4 * limbs

/-- The bytes of the working space. -/
def wsBytes : Nat := 4096

/-- Where the function's own working space starts. -/
def ownAt : Nat := 1472

/-- Where it ends. -/
def ownEnd : Nat := 1600

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

/-- `vg_gf25519_r16_mul` on every target. -/
def mulApi : Api where
  module := "gf25519_r16"
  name := "vg_gf25519_r16_mul"
  sig := sig
  contracts := some fun A stack => mulContract A stack
  summary := "Multiplication in curve25519's field: writes an element congruent to `a b` modulo \
    `p = 2^255 - 19` to `o`. An element is sixteen 32-bit little-endian words, least \
    significant first, each a limb below `2^16`: the number `Σ l_i 2^(16 i)`, not necessarily \
    below `p`. The elements are at the byte offsets `o`, `a` and `b` of the working space `ws`; \
    `o` may be `a` or `b`. The result's limbs are below `2^16`. Every byte of `ws` but the \
    result's and the function's own working space (bytes 1472 to 1599) keeps its value.\n\n\
    Contract: `mulContract` of `VG.Spec.X25519.Field16`. Constant time: only the pointer and \
    the offsets may affect timing."
  safety :=
    ["`o`, `a` and `b` plus 64 must be at most 1472: bytes 1472 to 1599 of `ws` are the \
        function's own working space.",
      "Each limb of the operands must be below `2^16`.",
      "Bytes 1472 to 1599 of `ws` are unspecified on return and may hold intermediate values, \
        which the caller must destroy if they are secret."]

end VG.Spec.X25519.Field16
