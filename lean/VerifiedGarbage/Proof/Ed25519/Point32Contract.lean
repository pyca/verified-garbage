module

public import VerifiedGarbage.Proof.Ed25519.Point64Contract

/-!
# Ed25519's points in radix `2^32`, in the working space

Not trusted: how the proofs of the functions on points in radix `2^32` state
where their operands are.

A coordinate is 32 bytes, a little-endian number below `2^256`, standing for
its residue modulo `p` (`elemAt`), `p = 2^255 - 19`: any 32 bytes are a
coordinate. A point of edwards25519 in extended coordinates (`Point`) is four
coordinates, `X, Y, Z, T`, at consecutive offsets (`pointAt`). The points
live in Ed25519's working space `ws` of 8192 bytes (`[u64; 1024]`), at fixed
offsets, where that code keeps the operands of its additions: `p` at byte 64
(`pAt`), `q` at byte 192 (`qAt`), and the curve's constant `d` at byte 576
(`dAt`), which `vg_ed25519_r32_point_add`'s caller provides; the result
replaces `p`. Bytes 320 to 575 and 864 to 1023 of `ws` are the functions' own
working space: every other byte of `ws` keeps its value but the result's
(`Keeps`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.Point32

open VG.Spec VG.Spec.Ed25519

open X25519 (P Fe)

/-- The bytes of the working space. -/
def wsBytes : Nat := 8192

/-- The bytes of a coordinate. -/
def elemBytes : Nat := 32

/-- Where the first point, and the sum, is. -/
def pAt : Nat := 64

/-- Where the second point is. -/
def qAt : Nat := 192

/-- Where `d` is. -/
def dAt : Nat := 576

/-- The coordinate at byte offset `o` of the working space `ws`: its 32
bytes, little-endian, modulo `P`. -/
def elemAt (m : Mem) (ws : Addr) (o : Nat) : Fe :=
  Fin.ofNat P (m.read (ws + BitVec.ofNat 64 o) elemBytes).toNat

/-- The point at byte offset `o`: its coordinates `X, Y, Z, T` at `o`,
`o + 32`, `o + 64` and `o + 96`. -/
def pointAt (m : Mem) (ws : Addr) (o : Nat) : Point :=
  ⟨elemAt m ws o, elemAt m ws (o + elemBytes), elemAt m ws (o + 2 * elemBytes),
    elemAt m ws (o + 3 * elemBytes)⟩

/-- Every byte of `ws` but those of the sum (bytes 64 to 191) and of the
function's own working space (bytes 320 to 575 and 864 to 1023) keeps its
value. -/
def Keeps (ws : Addr) (m m' : Mem) : Prop :=
  ∀ i < wsBytes, (i < pAt ∨ pAt + 4 * elemBytes ≤ i) → (i < 320 ∨ 576 ≤ i) → (i < 864 ∨ 1024 ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

end VG.Proof.Ed25519.Point32
