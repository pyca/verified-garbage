module

public import VerifiedGarbage.Proof.Sha3.Stream
public import VerifiedGarbage.Spec.MlKem
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# `H(ek)` absorbed one block at a time

`hstate E b`: the state of SHA3-256's sponge (rate 136, suffix `0x06`) before
block `b` of `pad(E)` is absorbed: the sponge of the first `b` blocks of
`E`, and, once every block is absorbed, `absorb 136 (pad 136 6 E)`, the state
`H(E)` is squeezed from (`H_of_hstate`). A whole block of `E` takes
`hstate E b` to `hstate E (b + 1)` (`hstate_full`), and so does the last,
partial block, followed by the padding (`hstate_last`, `hstate_padBlock`:
the padding as bytes of the block, `E`'s rest, `0x06`, zeros and `0x80`).

(AArch64's encapsulation absorbs `ek` in the same way, in
`Proof/MlKem/AArch64/Hybrid/Absorb.lean`.)
-/

@[expose] public section

namespace VG.Proof.MlKem.HSponge

open VG.Spec.Sha3 (State keccakF absorb pad stateAt bytesAt toBytes)
open VG.Proof.Sha3 (Rep xorAt xorByte byteOf)

/-- The state before block `b` of `pad(E)` is absorbed. -/
def hstate (E : List Byte) (b : Nat) : State :=
  if 136 * b ≤ E.length then Rep 136 (E.take (136 * b)) else absorb 136 (pad 136 (BitVec.ofNat 8 6) E)

theorem hstate_zero (E : List Byte) : hstate E 0 = Spec.Sha3.zero := by
  simp only [hstate, Nat.mul_zero, Nat.zero_le, ite_true, List.take_zero, Proof.Sha3.rep_nil]

theorem hstate_done {E : List Byte} {b : Nat} (h : E.length < 136 * b) :
    hstate E b = absorb 136 (pad 136 (BitVec.ofNat 8 6) E) := by
  simp only [hstate, ite_eq_right (show ¬136 * b ≤ E.length by omega)]

theorem xorAt_nil (A : State) (j : Nat) : xorAt A j [] = A := rfl

theorem xorAt_append (A : State) (j : Nat) (bs : List Byte) :
    ∀ cs, xorAt A j (bs ++ cs) = xorAt (xorAt A j bs) (j + bs.length) cs := by
  refine Proof.Sha3.snoc_induction ?_ ?_
  · rw [List.append_nil]; exact (xorAt_nil _ _).symm
  · intro cs c ih
    rw [← List.append_assoc, Proof.Sha3.xorAt_snoc, ih, Proof.Sha3.xorAt_snoc, List.length_append,
      Nat.add_assoc]

theorem xorAt_zeros (A : State) (j : Nat) : ∀ n, xorAt A j (List.replicate n 0) = A
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ', Proof.Sha3.xorAt_snoc, xorAt_zeros A j n]
    refine Proof.Sha3.ext_bytes fun i hi => ?_
    rw [Proof.Sha3.byteOf_xorByte _ _ _ hi]
    split <;> simp

/-- A whole block. -/
theorem hstate_full {E : List Byte} {b : Nat} (h : 136 * b + 136 ≤ E.length) :
    keccakF (xorAt (hstate E b) 0 ((E.drop (136 * b)).take 136)) = hstate E (b + 1) := by
  have hl : (E.take (136 * b)).length = 136 * b := List.length_take_of_le (by omega)
  have hbs : ((E.drop (136 * b)).take 136).length = 136 := by
    rw [List.length_take, List.length_drop]; omega
  have ra := Proof.Sha3.rep_append (rate := 136) (by decide) (by decide) (E.take (136 * b))
    ((E.drop (136 * b)).take 136) (by omega) (by rw [hl, hbs]; omega)
  rw [hl, hbs, show 136 * b % 136 = 0 by omega, ite_eq_left (by decide)] at ra
  have ht : E.take (136 * (b + 1)) = E.take (136 * b) ++ (E.drop (136 * b)).take 136 := by
    rw [show 136 * (b + 1) = 136 * b + 136 by omega, List.take_add]
  simp only [hstate, ite_eq_left (show 136 * b ≤ E.length by omega),
    ite_eq_left (show 136 * (b + 1) ≤ E.length by omega), ht, ra]

/-- The last, partial block, and the padding. -/
theorem hstate_last {E : List Byte} {b : Nat} (hlo : 136 * b < E.length) (hhi : E.length < 136 * b + 136) :
    keccakF (xorByte (xorByte (xorAt (hstate E b) 0 (E.drop (136 * b))) (E.length - 136 * b)
      (BitVec.ofNat 8 6)) 135 128) = hstate E (b + 1) := by
  have hl : (E.take (136 * b)).length = 136 * b := List.length_take_of_le (by omega)
  have hbs : (E.drop (136 * b)).length = E.length - 136 * b := List.length_drop
  have ra := Proof.Sha3.rep_append (rate := 136) (by decide) (by decide) (E.take (136 * b))
    (E.drop (136 * b)) (by omega) (by rw [hl, hbs]; omega)
  rw [hl, hbs, show 136 * b % 136 = 0 by omega, ite_eq_right (show ¬0 + (E.length - 136 * b) = 136 by omega),
    List.take_append_drop] at ra
  rw [hstate_done (show E.length < 136 * (b + 1) by omega),
    Proof.Sha3.absorb_pad (by decide) (by decide), show E.length % 136 = E.length - 136 * b by omega]
  simp only [hstate, ite_eq_left (show 136 * b ≤ E.length by omega), ← ra]

/-- The last block of `pad(E)`, of 136 bytes: `E`'s rest `X`, the suffix `0x06`, zeros, and `0x80`. -/
def padBlock (X : List Byte) : List Byte :=
  X ++ [BitVec.ofNat 8 6] ++ List.replicate (134 - X.length) 0 ++ [BitVec.ofNat 8 0x80]

theorem padBlock_length {X : List Byte} (h : X.length ≤ 134) : (padBlock X).length = 136 := by
  simp only [padBlock, List.length_append, List.length_singleton, List.length_replicate]; omega

theorem xorAt_padBlock (A : State) {X : List Byte} (h : X.length ≤ 134) :
    xorAt A 0 (padBlock X) = xorByte (xorByte (xorAt A 0 X) X.length (BitVec.ofNat 8 6)) 135 128 := by
  rw [padBlock, xorAt_append, xorAt_append, xorAt_append, xorAt_zeros, Proof.Sha3.xorAt_single,
    Proof.Sha3.xorAt_single]
  simp only [Nat.zero_add, List.length_append, List.length_singleton, List.length_replicate,
    show X.length + 1 + (134 - X.length) = 135 by omega]
  rfl

/-- The last, partial block, as bytes of the padded block. -/
theorem hstate_padBlock {E : List Byte} {b : Nat} (hlo : 136 * b < E.length) (hhi : E.length < 136 * b + 135) :
    keccakF (xorAt (hstate E b) 0 (padBlock (E.drop (136 * b)))) = hstate E (b + 1) := by
  rw [xorAt_padBlock _ (by rw [List.length_drop]; omega), List.length_drop]
  exact hstate_last hlo (by omega)

/-- `H(E)`, from the state after the last block. -/
theorem H_of_hstate {E : List Byte} {b : Nat} (h : E.length < 136 * b) :
    Spec.MlKem.H E = (toBytes (hstate E b)).take 32 := by
  rw [hstate_done h]
  show (List.take 32 ((toBytes _).take 136 ++ [])) = _
  rw [List.append_nil, List.take_take]
  rfl

/-- The first 32 bytes of a state in memory. -/
theorem bytesAt_stateAt (m : Mem) (p : Addr) : bytesAt m p 32 = (toBytes (stateAt m p)).take 32 := by
  refine List.ext_getElem (by simp [bytesAt, Proof.Sha3.length_toBytes]) fun i h₁ h₂ => ?_
  simp only [bytesAt, List.length_map, List.length_range] at h₁
  rw [List.getElem_take, Proof.Sha3.toBytes_getElem _ (by omega), Proof.Sha3.byteOf_stateAt _ _ (by omega)]
  simp [bytesAt]

end VG.Proof.MlKem.HSponge
