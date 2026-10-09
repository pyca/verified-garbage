import VerifiedGarbage.Spec.Ccm
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.Omega

/-!
# AES-CCM: the MAC as chaining over pieces

Untrusted: everything here is checked by Lean. CCM's MAC (§6.1 steps 1–4)
is the CBC-MAC of the formatted blocks `B₀, …, Bᵣ`, which is CMAC's
chaining (`Spec.Cmac.chain`, what `vg_cmac_aes_update` computes) from a
zero block (`mac_eq`). The formatting (A.2) splits into `B₀`, the blocks of
the associated data (none if there is none; otherwise the encoding of its
length followed by its first bytes, then the rest of it padded,
`adataBlocks`) and the blocks of the payload padded (`format_eq`); a string
padded to whole blocks is its whole blocks followed, unless there are none
left, by its last bytes padded (`blocks_pad16`).
-/

namespace VG.Proof.AesCcm

open VG.Spec

theorem blocks_eq (bs : List Byte) : Ccm.blocks bs = Cmac.blocks 16 bs := rfl

theorem xor_eq : Ccm.xor = Cmac.xor := rfl

theorem zeros_eq (n : Nat) : Ccm.zeros n = Cmac.zeros n := rfl

theorem length_be (k x : Nat) : (Ccm.be k x).length = k := by simp [Ccm.be]

theorem length_zeros (n : Nat) : (Ccm.zeros n).length = n := by simp [Ccm.zeros]

/-- `B₀` is a block for a nonce of at most 15 bytes. -/
theorem length_b0 (t : Nat) {nonce : List Byte} (hn : nonce.length ≤ 15) (a p : Nat) :
    (Ccm.b0 t nonce a p).length = 16 := by
  simp only [Ccm.b0, List.cons_append, List.length_cons, List.length_append, length_be]; omega_arith

/-! ## Padding -/

theorem length_pad16 (bs : List Byte) :
    (Ccm.pad16 bs).length = bs.length + (16 - bs.length % 16) % 16 := by
  simp [Ccm.pad16, length_zeros]

theorem length_pad16_mod (bs : List Byte) : (Ccm.pad16 bs).length % 16 = 0 := by
  rw [length_pad16]; omega_arith

theorem pad16_nil : Ccm.pad16 [] = [] := rfl

/-- Padding a string of whole blocks followed by more pads the rest. -/
theorem pad16_append {w r : List Byte} (hw : w.length % 16 = 0) :
    Ccm.pad16 (w ++ r) = w ++ Ccm.pad16 r := by
  simp only [Ccm.pad16, List.length_append, List.append_assoc]
  congr 3
  omega_arith

/-- A block pads to itself. -/
theorem pad16_block {r : List Byte} (h : r.length = 16) : Ccm.pad16 r = r := by
  simp [Ccm.pad16, h, Ccm.zeros]

/-- A string of 1 to 16 bytes pads to one block. -/
theorem pad16_short {r : List Byte} (h : r.length ≤ 16) :
    Ccm.pad16 r = r ++ Ccm.zeros (16 - r.length) ∨ r = [] := by
  rcases Nat.eq_zero_or_pos r.length with h0 | h0
  · exact .inr (List.eq_nil_of_length_eq_zero h0)
  · left
    simp only [Ccm.pad16]
    congr 2
    rcases Nat.lt_or_ge r.length 16 with h1 | h1
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega_arith)]
    · rw [show r.length = 16 by omega_arith]

theorem blocks_pad16_short {r : List Byte} (h0 : 0 < r.length) (h : r.length ≤ 16) :
    Cmac.blocks 16 (Ccm.pad16 r) = [r ++ Ccm.zeros (16 - r.length)] := by
  rcases pad16_short h with e | e
  · rw [e]; exact Proof.Cmac.Stream.blocks_single (by simp [length_zeros]; omega_arith)
  · subst e; simp at h0

/-- A string padded to whole blocks: its whole blocks, then its last bytes
padded, if any are left. -/
theorem blocks_pad16 (x : List Byte) :
    Cmac.blocks 16 (Ccm.pad16 x) = Cmac.blocks 16 (x.take (16 * (x.length / 16))) ++
      (if x.length % 16 = 0 then [] else
        [x.drop (16 * (x.length / 16)) ++ Ccm.zeros (16 - x.length % 16)]) := by
  have hw : (x.take (16 * (x.length / 16))).length % 16 = 0 := by
    rw [List.length_take]; omega_arith
  have ex : x = x.take (16 * (x.length / 16)) ++ x.drop (16 * (x.length / 16)) := (List.take_append_drop _ _).symm
  have hd : (x.drop (16 * (x.length / 16))).length = x.length % 16 := by rw [List.length_drop]; omega_arith
  conv => lhs; rw [ex]
  rw [pad16_append hw, Proof.Cmac.Stream.blocks_append hw]
  congr 1
  split
  · rename_i h
    rw [List.eq_nil_of_length_eq_zero (by omega_arith : (x.drop (16 * (x.length / 16))).length = 0)]; rfl
  · rename_i h
    rw [blocks_pad16_short (by omega_arith) (by omega_arith), hd]

/-! ## The associated data -/

/-- The length of the encoding of the length `a` (A.2.2). -/
def hdrLen (a : Nat) : Nat := if a < 2 ^ 16 - 2 ^ 8 then 2 else if a < 2 ^ 32 then 6 else 10

theorem length_encodeLen (a : Nat) : (Ccm.encodeLen a).length = hdrLen a := by
  unfold Ccm.encodeLen hdrLen
  split
  · simp [length_be]
  · split <;> simp [length_be]

theorem hdrLen_le (a : Nat) : hdrLen a ≤ 10 := by unfold hdrLen; split <;> [omega_arith; split <;> omega_arith]

/-- How many bytes of the associated data fit in its first block, after the
encoding of its length. -/
def headLen (a : Nat) : Nat := min a (16 - hdrLen a)

/-- The blocks of the formatted associated data `aad` (A.2.2): none if it is
empty; otherwise the encoding of its length followed by its first
`headLen` bytes, padded, then the rest of it, padded. -/
def adataBlocks (aad : List Byte) : List (List Byte) :=
  if aad.length = 0 then [] else
    [Ccm.pad16 (Ccm.encodeLen aad.length ++ aad.take (headLen aad.length))] ++
      Cmac.blocks 16 (Ccm.pad16 (aad.drop (headLen aad.length)))

theorem blocks_adata (aad : List Byte) :
    Cmac.blocks 16 (if aad.length = 0 then [] else Ccm.pad16 (Ccm.encodeLen aad.length ++ aad)) =
      adataBlocks aad := by
  unfold adataBlocks
  split
  · rfl
  · rename_i ha
    have hh := hdrLen_le aad.length
    have he := length_encodeLen aad.length
    rcases Nat.lt_or_ge (16 - hdrLen aad.length) aad.length with h | h
    · -- The first block is full.
      have hl : headLen aad.length = 16 - hdrLen aad.length := by unfold headLen; omega_arith
      have h16 : (Ccm.encodeLen aad.length ++ aad.take (headLen aad.length)).length = 16 := by
        rw [List.length_append, he, List.length_take]; omega_arith
      have ea : Ccm.encodeLen aad.length ++ aad =
          (Ccm.encodeLen aad.length ++ aad.take (headLen aad.length)) ++ aad.drop (headLen aad.length) := by
        rw [List.append_assoc, List.take_append_drop]
      rw [ea, pad16_append (by rw [h16]), Proof.Cmac.Stream.blocks_append (by rw [h16]),
        Proof.Cmac.Stream.blocks_single h16, pad16_block h16]
    · -- It all fits in the first block.
      have hl : headLen aad.length = aad.length := by unfold headLen; exact Nat.min_eq_left h
      rw [hl, List.take_of_length_le (Nat.le_refl _), List.drop_length, pad16_nil]
      rcases pad16_short (r := Ccm.encodeLen aad.length ++ aad) (by rw [List.length_append, he]; omega_arith) with e | e
      · rw [e, Proof.Cmac.Stream.blocks_single (by simp [List.length_append, he, length_zeros]; omega_arith)]; rfl
      · rw [List.append_eq_nil_iff] at e; exact absurd (List.length_eq_zero_iff.mpr e.2) ha

/-! ## The MAC -/

theorem xor_comm (x y : List Byte) : Cmac.xor x y = Cmac.xor y x := by
  simp only [Cmac.xor]
  exact List.zipWith_comm_of_comm (fun a b => BitVec.xor_comm a b) ..

theorem xor_zeros {x : List Byte} (h : x.length = 16) : Cmac.xor x (Cmac.zeros 16) = x := by
  apply List.ext_getElem (by simp [Proof.Cmac.length_xor, Proof.Cmac.length_zeros, h])
  intro i h₁ h₂
  simp only [Cmac.xor, Cmac.zeros, List.getElem_zipWith, List.getElem_replicate]
  exact BitVec.xor_zero ..

/-- A.2: the formatted blocks are `B₀`, those of the associated data and
those of the payload, padded. -/
theorem format_eq (t : Nat) {nonce : List Byte} (hn : nonce.length ≤ 15) (aad pt : List Byte) :
    Ccm.format t nonce aad pt =
      [Ccm.b0 t nonce aad.length pt.length] ++ adataBlocks aad ++ Cmac.blocks 16 (Ccm.pad16 pt) := by
  have h0 := length_b0 t hn aad.length pt.length
  have hA : (if aad.length = 0 then [] else Ccm.pad16 (Ccm.encodeLen aad.length ++ aad)).length % 16 = 0 := by
    split
    · rfl
    · exact length_pad16_mod _
  simp only [Ccm.format]
  rw [blocks_eq, List.append_assoc, Proof.Cmac.Stream.blocks_append (by rw [h0]),
    Proof.Cmac.Stream.blocks_single h0, Proof.Cmac.Stream.blocks_append hA, blocks_adata, List.append_assoc]

/-- §6.1 steps 1–4: the MAC is the first `t` bytes of the chaining of the
formatted blocks from a zero block. -/
theorem mac_eq (ciph : Ccm.Cipher) (t : Nat) {nonce : List Byte} (hn : nonce.length ≤ 15) (aad pt : List Byte) :
    Ccm.mac ciph t nonce aad pt = (Cmac.chain ciph (Cmac.zeros 16) (Ccm.format t nonce aad pt)).take t := by
  have h0 := length_b0 t hn aad.length pt.length
  simp only [Ccm.mac]
  rw [format_eq t hn, List.append_assoc, List.singleton_append]
  simp only [Cmac.chain, List.foldl_cons]
  rw [xor_comm, xor_zeros h0]
  have hf : (fun y bi => ciph (Ccm.xor bi y)) = (fun c m => ciph (Cmac.xor c m)) := by
    funext y b; rw [xor_eq, xor_comm]
  rw [hf]

end VG.Proof.AesCcm
