module

public import VerifiedGarbage.Spec.X448
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Arithmetic in curve448's field, in radix `2^16`, as functions

Not trusted: the contracts of internal functions (`Rust.Internal`), which
only verified code calls, that their proofs are of and that the proofs of
their callers compose. Only the callers' contracts, in `Spec/`, are trusted.

The contracts of four functions on
elements of `GF(p)`, `p = 2^448 - 2^224 - 1`, each twenty-eight 16-bit limbs,
so that the code of X448 and Ed448 can call one copy of its field arithmetic
instead of repeating it at every use:

* `vg_gf448_r16_mul`: the product `a b`;
* `vg_gf448_r16_add`: the sum `a + b`;
* `vg_gf448_r16_sub`: the difference `a - b`;
* `vg_gf448_r16_mul_a24`: the product `39081 a` (`a24` of RFC 7748 §5).

They are not algorithms of a standard but the arithmetic X448 and Ed448 are
built from, in the representation the 32-bit targets' code keeps elements
in: what they compute is stated on integers, modulo `p`.

An element is twenty-eight limbs, each a 32-bit little-endian word below
`2^16`, least significant first (`Limbs`): the element `Σ lᵢ 2^(16 i)`
(`valAt`), any number below `2^448` (so not necessarily below `p`). The
elements live in a working space `ws` of 8192 bytes (`[u64; 1024]`, the
working space of X448's and Ed448's functions), each at a byte offset: `o`
for the result, `a` and `b` for the operands. The offsets are arguments, so
that the result may be an operand and the caller keeps its elements where
it likes. Bytes 3584 to 4095 of `ws` are the function's own working space
(`ownAt`), and the elements lie below them (`Fits`). On return the
function's own bytes are unspecified and may hold intermediate values;
every other byte of `ws` keeps its value but the result's (`Keeps`).

The result's limbs are below `2^16` again, so that it can be the operand of
any of the functions. Everything is secret but the pointer and the offsets,
which are public, and the functions are constant time.
-/

@[expose] public section

namespace VG.Proof.X448.Field16

open VG.Spec VG.Spec.X448

/-- The limbs of an element. -/
def limbs : Nat := 28

/-- The bytes of an element: a 32-bit word per limb. -/
def elemBytes : Nat := 4 * limbs

/-- Where the function's own working space starts; it ends at byte 4096. -/
def ownAt : Nat := 3584

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
  ∀ i < 8192, (i < ownAt ∨ 4096 ≤ i) → (i < o.toNat ∨ o.toNat + elemBytes ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- `ws: *mut [u64; 1024], o: u32, a: u32, b: u32`, the offsets public. -/
def sig : Sig where
  params := [("ws", .array true .u64 1024), ("o", .int .u32 true), ("a", .int .u32 true),
    ("b", .int .u32 true)]

/-- `ws: *mut [u64; 1024], o: u32, a: u32`, the offsets public. -/
def sig1 : Sig where
  params := [("ws", .array true .u64 1024), ("o", .int .u32 true), ("a", .int .u32 true)]

/-- A binary operation `f` on the values: for operands that fit, with limbs
below `2^16`, the result at `o` has limbs below `2^16`, and `r` (the
relation of the values of the result and the operands, modulo `P`) holds. -/
def binContract {I : ISA} (A : Abi I) (r : Nat → Nat → Nat → Prop) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws o a b m => Fits o ∧ Fits a ∧ Fits b ∧ Limbs m ws a ∧ Limbs m ws b)
    (post := fun ws o a b m m' _ =>
      Limbs m' ws o ∧ r (valAt m' ws o) (valAt m ws a) (valAt m ws b) ∧ Keeps ws o m m')
    (stack := stack)

/-- `mul`: the result is congruent to `a b` modulo `P`. -/
def mulContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  binContract A (fun o a b => o % P = a * b % P) stack

/-- `add`: the result is congruent to `a + b` modulo `P`. -/
def addContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  binContract A (fun o a b => o % P = (a + b) % P) stack

/-- `sub`: the result is congruent to `a - b` modulo `P`, that is, its sum
with `b` is congruent to `a`. -/
def subContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  binContract A (fun o a b => (o + b) % P = a % P) stack

/-- `mul_a24`: for an operand that fits, with limbs below `2^16`, the result
at `o` has limbs below `2^16` and is congruent to `39081 a` modulo `P`. -/
def mulA24Contract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig1.contract A
    (pre := fun ws o a m => Fits o ∧ Fits a ∧ Limbs m ws a)
    (post := fun ws o a m m' _ =>
      Limbs m' ws o ∧ valAt m' ws o % P = 39081 * valAt m ws a % P ∧ Keeps ws o m m')
    (stack := stack)

end VG.Proof.X448.Field16
