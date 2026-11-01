module

public import VerifiedGarbage.Proof.X448.Field56Contract

/-!
# Multiplication in curve448's field, in radix `2^56`, as a function

Not trusted: the contracts of internal functions (`Rust.Internal`), which
only verified code calls, that their proofs are of and that the proofs of
their callers compose. Only the callers' contracts, in `Spec/`, are trusted.

The contract of the product of two
elements of `GF(p)`, `p = 2^448 - 2^224 - 1`, in the representation of
`Proof/X448/Field56Contract.lean` (eight limbs of 56 bits, the AArch64 code's), so that
the code of X448 and Ed448 can call one copy of it instead of repeating it at
every use:

* `vg_gf448_r56_mul`: the product `a b`.

It is not an algorithm of a standard but the arithmetic X448 and Ed448 are
built from, in the representation that code keeps elements in: what it
computes is stated on the elements' values, modulo `p` (`Field56.elemAt`).

The elements live in the working space `ws` of `Field56` (8192 bytes), each
at a byte offset: `o` for the result, `a` and `b` for the operands. The
offsets are arguments, so that the caller keeps its elements where it likes
(in practice the slots of `Field56`, but any offset will do), and they lie
below the function's own bytes, `Field56.own` (`Fits`). The operands' limbs
are below `3·2^56 + 2^9` (`Field56.opBound`), the bound an operand of the
code's products may have, and the result's below `2^56 + 2^8`
(`Field56.resBound`). The result may be the first operand (or overlap it),
since the code reads all of it before writing any of the result, but not
the second, which it reads while writing the result. On return the
function's own bytes are unspecified and may hold intermediate values;
every other byte of `ws` keeps its value but the result's
(`Field56.Keeps`).

Everything is secret but the pointer and the offsets, which are public, and
the function is constant time.
-/

@[expose] public section

namespace VG.Proof.X448.Field56

open VG.Spec VG.Spec.X448

/-- The bytes of an element: a 64-bit word per limb. -/
def elemBytes : Nat := 8 * limbs

/-- The element at byte offset `o` lies below the function's own bytes. -/
abbrev Fits (o : BitVec 64) : Prop := o.toNat + elemBytes ≤ accAt

/-- Every limb of the element at byte offset `o` is below `bound`. -/
def LimbsLt (m : Mem) (ws : Addr) (o : Nat) (bound : Nat) : Prop :=
  ∀ i < limbs, limbAt m ws o i < bound

/-- `ws: *mut [u64; 1024], o: u64, a: u64, b: u64`, the pointer and the
offsets public. -/
def mulSig : Sig where
  params := [("ws", .array true .u64 1024), ("o", .int .u64 true), ("a", .int .u64 true),
    ("b", .int .u64 true)]

/-- `mul`: for elements that fit, `o` not overlapping `b`, and operands with
limbs below `opBound`, the element at `o` is the product of those at `a` and
`b`, with limbs below `resBound`. -/
def mulContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  mulSig.contract A
    (pre := fun ws o a b m =>
      Fits o ∧ Fits a ∧ Fits b ∧
        (o.toNat + elemBytes ≤ b.toNat ∨ b.toNat + elemBytes ≤ o.toNat) ∧
        LimbsLt m ws a.toNat opBound ∧ LimbsLt m ws b.toNat opBound)
    (post := fun ws o a b m m' _ =>
      LimbsLt m' ws o.toNat resBound ∧
        elemAt m' ws o.toNat = elemAt m ws a.toNat * elemAt m ws b.toNat ∧
        Keeps ws ((o.toNat, o.toNat + elemBytes) :: own) m m')
    (stack := stack)

end VG.Proof.X448.Field56
