import VerifiedGarbage.Spec.X25519
import VerifiedGarbage.TCB.Artifact

/-!
# Multiplication in curve25519's field, in radix `2^32`, as a function

**Trusted** (as every file in `Spec/`). The contract of a function on
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
be an operand and the caller keeps its elements where it likes. Bytes 768 to
1023 of `ws` are `mul`'s own working space (`ownAt` to `ownEnd`), and bytes
704 to 1023 `pow250`'s (`powOwnAt` to `ownEnd`); the elements lie below them
(`Fits`, `PowFits`). On return a function's own bytes are unspecified and may
hold intermediate values; every other byte of `ws` keeps its value but the
results' (`Keeps`, `Keeps₂`).

Everything is secret but the pointer and the offsets, which are public, and
the functions are constant time.
-/

namespace VG.Spec.X25519.Field32

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

/-- `vg_gf25519_r32_mul` on every target. -/
def mulApi : Api where
  module := "gf25519_r32"
  name := "vg_gf25519_r32_mul"
  sig := sig
  contracts := some fun A stack => mulContract A stack
  summary := "Multiplication in curve25519's field: writes an element congruent to `a b` modulo \
    `p = 2^255 - 19` to `o`. An element is 32 bytes, a little-endian number below `2^256`, not \
    necessarily below `p`. The elements are at the byte offsets `o`, `a` and `b` of the working \
    space `ws`; `o` may be `a` or `b`. Every byte of `ws` but the result's and the function's \
    own working space (bytes 768 to 1023) keeps its value.\n\n\
    Contract: `mulContract` of `VG.Spec.X25519.Field32`. Constant time: only the pointer and \
    the offsets may affect timing."
  safety :=
    ["`o`, `a` and `b` plus 32 must be at most 768: bytes 768 to 1023 of `ws` are the \
        function's own working space.",
      "Bytes 768 to 1023 of `ws` are unspecified on return and may hold intermediate values, \
        which the caller must destroy if they are secret."]

/-! ## `pow250` -/

/-- Where `pow250`'s own working space starts; it ends at `ownEnd`. -/
def powOwnAt : Nat := 704

/-- The element at `o` lies below `pow250`'s own working space. -/
abbrev PowFits (o : BitVec 32) : Prop := o.toNat + elemBytes ≤ powOwnAt

/-- Every byte of `ws` but those of `pow250`'s own working space and of the
results at `o` and `e` keeps its value. -/
def Keeps₂ (ws : Addr) (o e : BitVec 32) (m m' : Mem) : Prop :=
  ∀ i < wsBytes, (i < powOwnAt ∨ ownEnd ≤ i) → (i < o.toNat ∨ o.toNat + elemBytes ≤ i) →
    (i < e.toNat ∨ e.toNat + elemBytes ≤ i) → m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- `ws: *mut [u64; 512], o: u32, e: u32, a: u32`, the offsets public. -/
def pow250Sig : Sig where
  params := [("ws", .array true .u64 512), ("o", .int .u32 true), ("e", .int .u32 true),
    ("a", .int .u32 true)]

/-- `pow250`: for elements that fit, with the results at `o` and `e` apart, the
result at `o` is congruent to `a^(2^250 - 1)` and the one at `e` to `a^11`,
modulo `P`. `a` may be `o` or `e`. -/
def pow250Contract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  pow250Sig.contract A
    (pre := fun _ o e a _ => PowFits o ∧ PowFits e ∧ PowFits a ∧
      (o.toNat + elemBytes ≤ e.toNat ∨ e.toNat + elemBytes ≤ o.toNat))
    (post := fun ws o e a m m' _ =>
      valAt m' ws o % P = valAt m ws a ^ (2 ^ 250 - 1) % P ∧
        valAt m' ws e % P = valAt m ws a ^ 11 % P ∧ Keeps₂ ws o e m m')
    (stack := stack)

/-- `vg_gf25519_r32_pow250` on every target. -/
def pow250Api : Api where
  module := "gf25519_r32"
  name := "vg_gf25519_r32_pow250"
  sig := pow250Sig
  contracts := some fun A stack => pow250Contract A stack
  summary := "Powers in curve25519's field: writes an element congruent to `a^(2^250 - 1)` \
    modulo `p = 2^255 - 19` to `o`, and one congruent to `a^11` to `e`: the addition chain \
    that inversion (`a^(p-2)`, five squarings of the first and a product with the second) and \
    decoding's square root (`a^((p-5)/8)`, two squarings of the first and a product with `a`) \
    share. An element is 32 bytes, a little-endian number below `2^256`, not necessarily below \
    `p`. The elements are at the byte offsets `o`, `e` and `a` of the working space `ws`; `a` \
    may be `o` or `e`. Every byte of `ws` but the results' and the function's own working \
    space (bytes 704 to 1023) keeps its value.\n\n\
    Contract: `pow250Contract` of `VG.Spec.X25519.Field32`. Constant time: only the pointer \
    and the offsets may affect timing."
  safety :=
    ["`o`, `e` and `a` plus 32 must be at most 704: bytes 704 to 1023 of `ws` are the \
        function's own working space.",
      "The 32 bytes at `o` and those at `e` must not overlap.",
      "Bytes 704 to 1023 of `ws` are unspecified on return and may hold intermediate values, \
        which the caller must destroy if they are secret."]

end VG.Spec.X25519.Field32
