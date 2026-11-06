module

public import VerifiedGarbage.Spec.X25519
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Curve25519's field elements in radix `2^32`, in the working space

Not trusted: how the proofs of the field functions in radix `2^32`
(`vg_gf25519_r32_mul`, `vg_gf25519_r32_pow250`), elements of `GF(p)`,
`p = 2^255 - 19`, each eight 32-bit words, state where their operands are.

An element is 32 bytes, a little-endian number below `2^256` (`valAt`), not
necessarily below `p`: any 32 bytes are an element. The elements live in a
working space `ws` of 4096 bytes (`[u64; 512]`, X25519's working space and
the start of Ed25519's), each at a byte offset: `o` for the result, `a`
and `b` for the operands, which `mul` takes as arguments. `pow250`'s
elements are at fixed offsets instead, where the x86 Ed25519 code keeps
them: `a` at byte 128 (`aAt`), `a^11` at byte 512 (`eAt`) and
`a^(2^250 - 1)` at byte 544 (`oAt`). Bytes 768 to 1023 of `ws` are `mul`'s
own working space (`ownAt` to `ownEnd`), and the elements lie below them
(`Fits`). Every other byte of `ws` keeps its value but the results'
(`Keeps`, `Keeps₂`).
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

/-! ## `pow250` -/

/-- Where `pow250` reads `a`. -/
def aAt : Nat := 128

/-- Where `pow250` writes `a^11`. -/
def eAt : Nat := 512

/-- Where `pow250` writes `a^(2^250 - 1)`. -/
def oAt : Nat := 544

/-- Every byte of `ws` but those of `pow250`'s results (bytes 512 to 575) and
own working space (bytes 576 to 1023) keeps its value. -/
def Keeps₂ (ws : Addr) (m m' : Mem) : Prop :=
  ∀ i < wsBytes, (i < eAt ∨ ownEnd ≤ i) → m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

end VG.Proof.X25519.Field32
