module

public import VerifiedGarbage.Spec.X25519
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Curve25519's field elements in radix `2^64`, in the working space

Not trusted: how the proofs of the inversion in radix `2^64`
(`vg_gf25519_r64_invert`, `z^(p-2)` in `GF(p)`, `p = 2^255 - 19`, each element
four 64-bit words) state where its operands are.

An element is 32 bytes, a little-endian number below `2^256` (`valAt`), not
necessarily below `p`: any 32 bytes are an element. The elements live in a
working space `ws` of 4096 bytes (`[u64; 512]`, X25519's working space and
the start of Ed25519's), at fixed offsets, those where that code keeps them.
The inversion reads `z` at byte 128 (`zAt`) and writes `z^(p-2)` at byte 544
(`invAt`); bytes 512 to 767 (`invOwnAt` to `invOwnEnd`) are its own working
space and its result. Every other byte of `ws` keeps its value (`InvKeeps`).
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

end VG.Proof.X25519.Field64
