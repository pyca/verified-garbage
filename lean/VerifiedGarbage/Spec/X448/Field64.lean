module

public import VerifiedGarbage.Spec.X448
public import VerifiedGarbage.TCB.Artifact

/-!
# Curve448's field in radix `2^64`, and the addition chain its powers share, as a function

**Trusted** (as every file in `Spec/`). The representation of elements of
`GF(p)`, `p = 2^448 - 2^224 - 1`, that the x86-64 code of X448 and Ed448
keeps them in, and the contract of one function on it, so that that code can
call one copy of the addition chain that inversion and decoding's square root
share instead of repeating it (in X448, in Ed448's base-point multiplication
and in Ed448's verification):

* `vg_gf448_r64_pow223`: the powers `a^(2^223 - 1)` and `a^(2^222 - 1)`.

Inversion is `a^(p-2) = (a^(2^223 - 1))^(2^225) · (a^(2^222 - 1))^4 · a`, and
the power in RFC 8032 §5.2.3's square root is
`a^((p-3)/4) = (a^(2^223 - 1))^(2^223) · a^(2^222 - 1)`: the caller finishes
either one with a few squarings and products.

It is not an algorithm of a standard but the arithmetic X448 and Ed448 are
built from, in the representation that code keeps elements in: what it
computes is stated on integers, modulo `p`.

An element is 56 bytes, a little-endian number below `2^448` (`valAt`), not
necessarily below `p`: any 56 bytes are an element. The elements live in a
working space `ws` of 8192 bytes (`[u64; 1024]`, the working space of X448's
and Ed448's functions) in slots of 64 bytes, slot `n` at byte `64 + 64 n`
(`slotAt`), of which an element takes the first 56 bytes. The function reads
`a` in slot 12 and writes `a^(2^223 - 1)` to slot 21 and `a^(2^222 - 1)` to
slot 20, the slots where that code keeps them. Bytes 960 to 1647 of `ws`
(slots 14 to 21 and the 176 bytes above them) are the function's own working
space and its results (`ownAt` to `ownEnd`). On return the bytes of the
working space but the results are unspecified and may hold intermediate
values; every other byte of `ws` keeps its value (`Keeps`).

Everything is secret but the pointer, which is public, and the function is
constant time.
-/

@[expose] public section

namespace VG.Spec.X448.Field64

/-- The bytes of the working space. -/
def wsBytes : Nat := 8192

/-- The bytes of an element. -/
def elemBytes : Nat := 56

/-- Where slot `n` is. -/
def slotAt (n : Nat) : Nat := 64 + 64 * n

/-- Where the function reads `a`: slot 12. -/
def aAt : Nat := slotAt 12

/-- Where it writes `a^(2^222 - 1)`: slot 20. -/
def eAt : Nat := slotAt 20

/-- Where it writes `a^(2^223 - 1)`: slot 21. -/
def oAt : Nat := slotAt 21

/-- Where the function's own working space, and its results, start: slot 14. -/
def ownAt : Nat := slotAt 14

/-- Where they end. -/
def ownEnd : Nat := 1648

/-- The value of the element at byte offset `o` of the working space `ws`: its
56 bytes, little-endian. -/
def valAt (m : Mem) (ws : Addr) (o : Nat) : Nat :=
  (m.read (ws + BitVec.ofNat 64 o) elemBytes).toNat

/-- Every byte of `ws` but those of the function's own working space and
results (bytes 960 to 1647) keeps its value. -/
def Keeps (ws : Addr) (m m' : Mem) : Prop :=
  ∀ i < wsBytes, (i < ownAt ∨ ownEnd ≤ i) → m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- `ws: *mut [u64; 1024]`, the pointer public. -/
def sig : Sig where
  params := [("ws", .array true .u64 1024)]

/-- `pow223`: the element at `oAt` is congruent to `a^(2^223 - 1)` and the one
at `eAt` to `a^(2^222 - 1)`, modulo `P`, for `a` the element at `aAt`. -/
def pow223Contract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (post := fun ws m m' _ =>
      valAt m' ws oAt % P = valAt m ws aAt ^ (2 ^ 223 - 1) % P ∧
        valAt m' ws eAt % P = valAt m ws aAt ^ (2 ^ 222 - 1) % P ∧
        Keeps ws m m')
    (stack := stack)

/-- `vg_gf448_r64_pow223` on every target. -/
def pow223Api : Api where
  module := "gf448_r64"
  name := "vg_gf448_r64_pow223"
  sig := sig
  contracts := some fun A stack => pow223Contract A stack
  summary := "Powers in curve448's field: for `a` the element at byte 832 (slot 12) of the \
    working space `ws`, writes an element congruent to `a^(2^223 - 1)` modulo \
    `p = 2^448 - 2^224 - 1` to byte 1408 (slot 21), and one congruent to `a^(2^222 - 1)` to \
    byte 1344 (slot 20): the addition chain that inversion (`a^(p-2)`, 225 squarings of the \
    first times two squarings of the second and `a`) and decoding's square root \
    (`a^((p-3)/4)`, 223 squarings of the first times the second) share. An element is 56 \
    bytes, a little-endian number below `2^448`, not necessarily below `p`. Every byte of \
    `ws` but those from byte 960 to byte 1647 (the function's own working space and its \
    results) keeps its value.\n\n\
    Contract: `pow223Contract` of `VG.Spec.X448.Field64`. Constant time: only the pointer \
    may affect timing."
  safety :=
    ["Bytes 960 to 1647 of `ws` but the results are unspecified on return and may hold \
        intermediate values, which the caller must destroy if they are secret."]

end VG.Spec.X448.Field64
