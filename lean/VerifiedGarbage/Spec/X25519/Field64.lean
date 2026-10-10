module

public import VerifiedGarbage.Spec.X25519
public import VerifiedGarbage.TCB.Artifact

/-!
# Multiplication, inversion and powers in curve25519's field, in radix `2^64`, as functions

**Trusted** (as every file in `Spec/`). The contracts of functions on
elements of `GF(p)`, `p = 2^255 - 19`, each four 64-bit words, so that the
code of X25519 and Ed25519 that keeps elements this way (on x86-64 and
AArch64) can call one copy of each instead of repeating it at every use:

* `vg_gf25519_r64_mul`: the product `a b`;
* `vg_gf25519_r64_mul2`: twice the product, `2 a b` (Ed25519's point
  doubling and cached points multiply by 2 with the product);
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
the start of Ed25519's), each at a byte offset: `o` for the result, `a` and
`b` for the operands. The offsets are arguments, so that the result may
be an operand and the caller keeps its elements where it likes. Bytes 3584
to 4095 of `ws` are the functions' own working space (`ownAt`), and the
elements lie below them (`Fits`). On return the function's own bytes are
unspecified and may hold intermediate values; every other byte of `ws` keeps
its value but the result's (`Keeps`).

The inversion's elements are at fixed offsets instead, those where that code
keeps them, in a working space of the same 4096 bytes: it reads `z` at byte
128 (`zAt`) and writes `z^(p-2)` at byte 544 (`invAt`); bytes 512 to 767 (`invOwnAt` to `invOwnEnd`) are its own working space and its
result. On return those bytes but the result are unspecified and may hold
intermediate values; every other byte of `ws` keeps its value (`InvKeeps`).

`pow250` reads `a` at byte 128 too and writes `a^11` at byte 512 (`p11At`)
and `a^(2^250 - 1)` at byte 544 (`p250At`); bytes 576 to 767 are its own
working space, unspecified on return. Every byte of `ws` outside bytes 512
to 767 keeps its value (`PowKeeps`).

Everything is secret but the pointer and the offsets, which are public, and
the functions are constant time.
-/

@[expose] public section

namespace VG.Spec.X25519.Field64

/-- The bytes of the working space. -/
def wsBytes : Nat := 4096

/-- The bytes of an element. -/
def elemBytes : Nat := 32

/-- Where the functions' own working space starts; it ends at byte
`wsBytes`. -/
def ownAt : Nat := 3584

/-- The value of the element at byte offset `o` of the working space `ws`:
its 32 bytes, little-endian. -/
def valAt (m : Mem) (ws : Addr) (o : BitVec 32) : Nat :=
  (m.read (ws + BitVec.ofNat 64 o.toNat) elemBytes).toNat

/-- The element at `o` lies below the functions' own working space. -/
abbrev Fits (o : BitVec 32) : Prop := o.toNat + elemBytes ≤ ownAt

/-- Every byte of `ws` but those of the functions' own working space and of
the result at `o` keeps its value. -/
def Keeps (ws : Addr) (o : BitVec 32) (m m' : Mem) : Prop :=
  ∀ i < ownAt, (i < o.toNat ∨ o.toNat + elemBytes ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- `ws: *mut [u64; 512], o: u32, a: u32, b: u32`, the offsets public. -/
def sig : Sig where
  params := [("ws", .array true .u64 512), ("o", .int .u32 true), ("a", .int .u32 true),
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
    or `b`. Every byte of `ws` but the result's and the function's own working space (bytes \
    3584 to 4095) keeps its value.\n\n\
    Contract: `mulContract` or `mul2Contract` of `VG.Spec.X25519.Field64`. Constant time: only \
    the pointer and the offsets may affect timing."

/-- The `# Safety` items but for what the signature gives. -/
def safety : List String :=
  ["`o`, `a` and `b` plus 32 must be at most 3584: bytes 3584 to 4095 of `ws` are the \
      function's own working space.",
    "Bytes 3584 to 4095 of `ws` are unspecified on return and may hold intermediate values, \
      which the caller must destroy if they are secret."]

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

/-- `vg_gf25519_r64_invert` on every target. -/
def invertApi : Api where
  module := module
  name := "vg_gf25519_r64_invert"
  sig := invSig
  contracts := some fun A stack => invertContract A stack
  summary := "Inversion in curve25519's field: for `z` the element at byte 128 of the working \
    space `ws`, writes an element congruent to `z^(p-2)` modulo `p = 2^255 - 19` (the inverse \
    of `z`, or `0` if `z` is a multiple of `p`) to byte 544. An element is 32 bytes, a \
    little-endian number below `2^256`, not necessarily below `p`. Every byte of `ws` but \
    those from byte 512 to byte 767 (the function's own working space and its result) keeps \
    its value.\n\n\
    Contract: `invertContract` of `VG.Spec.X25519.Field64`. Constant time: only the pointer \
    may affect timing."
  safety :=
    ["Bytes 512 to 767 of `ws` but the result are unspecified on return and may hold \
        intermediate values, which the caller must destroy if they are secret."]

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

/-- `vg_gf25519_r64_pow250` on every target. -/
def pow250Api : Api where
  module := module
  name := "vg_gf25519_r64_pow250"
  sig := invSig
  contracts := some fun A stack => pow250Contract A stack
  summary := "Powers in curve25519's field: for `a` the element at byte 128 of the working \
    space `ws`, writes an element congruent to `a^(2^250 - 1)` modulo `p = 2^255 - 19` to byte \
    544, and one congruent to `a^11` to byte 512: the addition chain that inversion \
    (`a^(p-2)`, five squarings of the first and a product with the second) and decoding's \
    square root (`a^((p-5)/8)`, two squarings of the first and a product with `a`) share. An \
    element is 32 bytes, a little-endian number below `2^256`, not necessarily below `p`. \
    Every byte of `ws` but those from byte 512 to byte 767 (the results and the function's own \
    working space) keeps its value.\n\n\
    Contract: `pow250Contract` of `VG.Spec.X25519.Field64`. Constant time: only the pointer \
    may affect timing."
  safety :=
    ["Bytes 576 to 767 of `ws` are unspecified on return and may hold intermediate values, \
        which the caller must destroy if they are secret."]

end VG.Spec.X25519.Field64
