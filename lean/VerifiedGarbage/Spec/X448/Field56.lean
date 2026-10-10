module

public import VerifiedGarbage.Spec.X448
public import VerifiedGarbage.TCB.Artifact

/-!
# Curve448's field in radix `2^56`, and its square root's power, as a function

**Trusted** (as every file in `Spec/`). The representation of elements of
`GF(p)`, `p = 2^448 - 2^224 - 1`, that the AArch64 code of X448 and Ed448
keeps them in, and the contract of one function on it, so that the code
that decodes points (twice in Ed448's verification) can call one copy of it
instead of repeating it:

* `vg_gf448_r56_pow_p34`: the power `a^((p-3)/4)`, the exponent of
  decoding's square root (RFC 8032 §5.2.3: `x = u^3 v (u^5 v^3)^((p-3)/4)`).

It is not an algorithm of a standard but the arithmetic X448 and Ed448 are
built from, in the representation that code keeps elements in: what it
computes is stated on the elements' values, modulo `p`.

An element is eight limbs, each a 64-bit little-endian word, least
significant first (`limbAt`): the element `Σ lᵢ 2^(56 i)` (`valAt`), not
necessarily below `p`, and its residue modulo `p` (`elemAt`). The elements
live in a working space `ws` of 8192 bytes (`[u64; 1024]`, the working space
of X448's and Ed448's functions) in 22 slots of 128 bytes, slot `n` at byte
`64 + 128 n` (`slotAt`), of which an element takes the first 64 bytes. The
code bounds every limb of every slot by `3·2^56 + 2^9` (`opBound`), the
bound an operand of its products may have (`Bounded`), and products, which
some operations need of an operand, by `2^56 + 2^8` (`resBound`, `Res`).
Functions on this representation take and keep `Bounded` for all 22 slots.

The working space holds the functions' operands and results at fixed slots,
where that code keeps them, and their own bytes (`Keeps`, which keeps every
byte of `ws` outside a list of ranges): the 1152 bytes from byte 3584
(`accAt`), where the products accumulate. `pow_p34` reads `a` in slot 12 and
writes the power to slot 21, with temporaries in slots 14 to 20. On return
the function's own bytes are unspecified and may hold intermediate values.

Everything is secret but the pointer, which is public, and the functions are
constant time.
-/

@[expose] public section

namespace VG.Spec.X448.Field56

/-- The limbs of an element. -/
def limbs : Nat := 8

/-- The bytes of the working space. -/
def wsBytes : Nat := 8192

/-- The slots of the working space. -/
def slots : Nat := 22

/-- Where slot `n` is. -/
def slotAt (n : Nat) : Nat := 64 + 128 * n

/-- The bytes of a slot. -/
def slotBytes : Nat := 128

/-- Where the products accumulate, for 1152 bytes. -/
def accAt : Nat := 3584

/-- Where the products' bytes end. -/
def accEnd : Nat := 4736

/-- The bound of an operand's limbs: `3·2^56 + 2^9`. -/
def opBound : Nat := 3 * 2 ^ 56 + 2 ^ 9

/-- The bound of a product's limbs: `2^56 + 2^8`. -/
def resBound : Nat := 2 ^ 56 + 2 ^ 8

/-- Limb `i` of the element at byte offset `o` of the working space `ws`. -/
def limbAt (m : Mem) (ws : Addr) (o : Nat) (i : Nat) : Nat :=
  (m.readW (ws + BitVec.ofNat 64 (o + 8 * i)) 64).toNat

/-- The value of the first `n` limbs of the element at `o`: `Σ lᵢ 2^(56 i)`. -/
def valN (m : Mem) (ws : Addr) (o : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => valN m ws o n + 2 ^ (56 * n) * limbAt m ws o n

/-- The value of the element at `o`. -/
def valAt (m : Mem) (ws : Addr) (o : Nat) : Nat := valN m ws o limbs

/-- The element at `o`, modulo `P`. -/
def elemAt (m : Mem) (ws : Addr) (o : Nat) : Fe := Fin.ofNat P (valAt m ws o)

/-- Every limb of every slot is below `opBound`. -/
def Bounded (m : Mem) (ws : Addr) : Prop :=
  ∀ n < slots, ∀ i < limbs, limbAt m ws (slotAt n) i < opBound

/-- Every limb of slot `n` is below `resBound`. -/
def Res (m : Mem) (ws : Addr) (n : Nat) : Prop := ∀ i < limbs, limbAt m ws (slotAt n) i < resBound

/-- Every byte of `ws` outside the ranges `[a, b)` of `rs` keeps its value. -/
def Keeps (ws : Addr) (rs : List (Nat × Nat)) (m m' : Mem) : Prop :=
  ∀ i < wsBytes, (∀ r ∈ rs, i < r.1 ∨ r.2 ≤ i) →
    m' (ws + BitVec.ofNat 64 i) = m (ws + BitVec.ofNat 64 i)

/-- What the products change. -/
def own : List (Nat × Nat) := [(accAt, accEnd)]

/-! ## `pow_p34` -/

/-- Where `pow_p34` reads `a`. -/
def aSlot : Nat := 12

/-- Where `pow_p34` writes the power. -/
def oSlot : Nat := 21

/-- Where `pow_p34`'s temporaries, and its result, are: slots 14 to 21. -/
def powSlots : Nat × Nat := (slotAt 14, slotAt 22)

/-- `ws: *mut [u64; 1024]`, the pointer public. -/
def sig : Sig where
  params := [("ws", .array true .u64 1024)]

/-- `pow_p34`: with every slot `Bounded`, the element in slot 21 is that in
slot 12 to the power `(P - 3) / 4`, and every slot is `Bounded` again. -/
def powContract {I : ISA} (A : Abi I) (stack : Nat := 0) : Contract I :=
  sig.contract A
    (pre := fun ws m => Bounded m ws)
    (post := fun ws m m' _ =>
      Bounded m' ws ∧ elemAt m' ws (slotAt oSlot) = pow (elemAt m ws (slotAt aSlot)) ((P - 3) / 4) ∧
        Keeps ws (powSlots :: own) m m')
    (stack := stack)

/-- What the functions on this representation require. -/
def boundedDoc : String :=
  "Each of the 8 limbs of the 22 slots of 128 bytes of `ws` from byte 64 (the element of slot `n` \
    is the first 64 bytes from byte `64 + 128 n`) must be below `3 * 2^56 + 2^9`; they are \
    again on return."

/-- What the documentation of the functions on this representation says of
their elements. -/
def elemDoc : String :=
  "An element is eight 64-bit little-endian words, least significant first, each a limb: the \
    number `Σ l_i 2^(56 i)`, standing for its residue modulo `p = 2^448 - 2^224 - 1`, not \
    necessarily reduced. Bytes 3584 to 4735 of `ws` are the function's own working space."

/-- `vg_gf448_r56_pow_p34` on every target. -/
def powApi : Api where
  module := "gf448_r56"
  name := "vg_gf448_r56_pow_p34"
  sig := sig
  contracts := some fun A stack => powContract A stack
  summary := "A power in curve448's field: for `a` the element in slot 12 (byte 1600) of the \
    working space `ws`, writes `a^((p-3)/4)` to slot 21 (byte 2752), the exponent of RFC 8032's \
    square root for decoding points. " ++ elemDoc ++ " Every byte of `ws` but slots 14 to 21 \
    (bytes 1856 to 2879) and the function's own working space keeps its value.\n\n\
    Contract: `powContract` of `VG.Spec.X448.Field56`. Constant time: only the pointer may \
    affect timing."
  safety :=
    [boundedDoc,
      "Bytes 1856 to 2751 and 3584 to 4735 of `ws` are unspecified on return and may hold \
        intermediate values, which the caller must destroy if they are secret."]

end VG.Spec.X448.Field56
