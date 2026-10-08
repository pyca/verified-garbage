import VerifiedGarbage.Spec.X25519
import VerifiedGarbage.TCB.Artifact

/-!
# Multiplication in curve25519's field, in radix `2^64`, as functions

**Trusted** (as every file in `Spec/`). The contracts of two functions on
elements of `GF(p)`, `p = 2^255 - 19`, each four 64-bit words, so that the
code of X25519 and Ed25519 that keeps elements this way (the x86-64 code) can
call one copy of each product instead of repeating it at every use:

* `vg_gf25519_r64_mul`: the product `a b`;
* `vg_gf25519_r64_mul2`: twice the product, `2 a b` (Ed25519's point
  doubling and cached points multiply by 2 with the product).

They are not algorithms of a standard but the arithmetic X25519 and Ed25519
are built from, in the representation that code keeps elements in: what they
compute is stated on integers, modulo `p`.

An element is 32 bytes, a little-endian number below `2^256` (`valAt`), not
necessarily below `p`: any 32 bytes are an element. The elements live in a
working space `ws` of 768 bytes (`[u64; 96]`, the start of X25519's and
Ed25519's working spaces), each at a byte offset: `o` for the result, `a`
and `b` for the operands (`Fits`). The offsets are arguments, so that the
result may be an operand and the caller keeps its elements where it likes.
The functions have no working space of their own in `ws`: every byte of
`ws` keeps its value but the result's (`Keeps`).

Everything is secret but the pointer and the offsets, which are public, and
the functions are constant time.
-/

namespace VG.Spec.X25519.Field64

/-- The bytes of the working space. -/
def wsBytes : Nat := 768

/-- The bytes of an element. -/
def elemBytes : Nat := 32

/-- The value of the element at byte offset `o` of the working space `ws`:
its 32 bytes, little-endian. -/
def valAt (m : Mem) (ws : Addr) (o : BitVec 32) : Nat :=
  (m.read (ws + BitVec.ofNat 64 o.toNat) elemBytes).toNat

/-- The element at `o` lies in the working space. -/
abbrev Fits (o : BitVec 32) : Prop := o.toNat + elemBytes ≤ wsBytes

/-- Every byte of `ws` but those of the result at `o` keeps its value. -/
def Keeps (ws : Addr) (o : BitVec 32) (m m' : Mem) : Prop :=
  ∀ i < wsBytes, (i < o.toNat ∨ o.toNat + elemBytes ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- `ws: *mut [u64; 96], o: u32, a: u32, b: u32`, the offsets public. -/
def sig : Sig where
  params := [("ws", .array true .u64 96), ("o", .int .u32 true), ("a", .int .u32 true),
    ("b", .int .u32 true)]

/-- A product `f` of the values: for elements that fit, `r` (the relation of
the values of the result and the operands, modulo `P`) holds. -/
def prodContract {I : ISA} (A : Abi I) (r : Nat → Nat → Nat → Prop) (stack : Nat := 0) :
    Contract I :=
  sig.contract A
    (pre := fun _ o a b _ => Fits o ∧ Fits a ∧ Fits b)
    (post := fun ws o a b m m' _ =>
      r (valAt m' ws o) (valAt m ws a) (valAt m ws b) ∧ Keeps ws o m m')
    (stack := stack)

/-- `mul`: the result is congruent to `a b` modulo `P`. -/
def mulContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  prodContract A (fun o a b => o % P = a * b % P) stack

/-- `mul2`: the result is congruent to `2 a b` modulo `P`. -/
def mul2Contract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  prodContract A (fun o a b => o % P = 2 * a * b % P) stack

/-- The Rust module of the functions. -/
def module : String := "gf25519_r64"

/-- What the documentation says of every function. -/
def common : String :=
  "An element is 32 bytes, a little-endian number below `2^256`, not necessarily below `p`. The \
    elements are at the byte offsets `o`, `a` and `b` of the working space `ws`; `o` may be `a` \
    or `b`. Every byte of `ws` but the result's keeps its value.\n\n\
    Contract: `mulContract` or `mul2Contract` of `VG.Spec.X25519.Field64`. Constant time: only \
    the pointer and the offsets may affect timing."

/-- The `# Safety` items but for what the signature gives. -/
def safety : List String :=
  ["`o`, `a` and `b` plus 32 must be at most 768: the elements lie in `ws`."]

/-- `vg_gf25519_r64_mul` on every target. -/
def mulApi : Api where
  module := module
  name := "vg_gf25519_r64_mul"
  sig := sig
  contracts := some fun A stack => mulContract A stack
  summary := "Multiplication in curve25519's field: writes an element congruent to `a b` modulo \
    `p = 2^255 - 19` to `o`. " ++ common
  safety := safety

/-- `vg_gf25519_r64_mul2` on every target. -/
def mul2Api : Api where
  module := module
  name := "vg_gf25519_r64_mul2"
  sig := sig
  contracts := some fun A stack => mul2Contract A stack
  summary := "Twice a product in curve25519's field: writes an element congruent to `2 a b` \
    modulo `p = 2^255 - 19` to `o`. " ++ common
  safety := safety

end VG.Spec.X25519.Field64
