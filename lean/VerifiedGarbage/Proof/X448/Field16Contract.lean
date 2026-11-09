module

public import VerifiedGarbage.Spec.X448
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Curve448's field in radix `2^16`

Not trusted: the representation of elements of `GF(p)`,
`p = 2^448 - 2^224 - 1`, each twenty-eight 16-bit limbs, that the 32-bit
targets' code of X448 and Ed448 keeps them in, and on which their field
functions (`vg_gf448_r16_mul`, `_add`, `_sub` and `_mul_a24`) work.

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
any of the functions.
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

end VG.Proof.X448.Field16
