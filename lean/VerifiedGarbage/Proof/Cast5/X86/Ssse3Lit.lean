module

public import VerifiedGarbage.Impl.Cast5.X86.Ssse3
public import VerifiedGarbage.Proof.Cast5.SboxRows
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Cast5.X86.Ssse3
meta import VerifiedGarbage.Proof.Cast5.SboxRows
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# CAST5 with its S-box look-ups by `pshufb` on x86 (32-bit): the table and the code as literals

The table of the planes of S1 to S8 and the constants
(`Impl.Cast5.X86.Ssse3.table`), the look-ups' function and the functions
over it as literals, which the checks of the whole functions
(`taint_decide`, `lit_decide`) read rather than build again. Each S-box's
planes are a literal of their own (`planes0` to `planes7`), which the
table's is put together from: the kernel evaluates an S-box's 1024 entries'
bytes in one declaration, not the eight S-boxes' in one.
-/

@[expose] public section

namespace VG

/-! ## The S-boxes in one number -/

namespace Proof.Cast5.X86.Ssse3

open Spec.Cast5 (Word)

/-- Words packed in one number, the first lowest. -/
def packW : List Word → Nat
  | [] => 0
  | b :: l => b.toNat + 2 ^ 32 * packW l

theorem packW_shift (l : List Word) (c : Nat) : packW l >>> (32 * c) % 2 ^ 32 = (l.getD c 0).toNat := by
  induction l generalizing c with
  | nil => simp [packW]
  | cons b l ih =>
    have hb := b.isLt
    cases c with
    | zero =>
      simp only [packW, Nat.mul_zero, Nat.shiftRight_zero, List.getD_cons_zero]
      omega_using [hb]
    | succ c =>
      rw [List.getD_cons_succ, ← ih, packW, Nat.mul_add, Nat.mul_one, Nat.add_comm (32 * c) 32,
        Nat.shiftRight_add]
      congr 2
      rw [Nat.shiftRight_eq_div_pow]
      omega_using [hb]

/-- The eight S-boxes, one after the other, in one number. -/
def sboxP : Nat := packW sboxRows.flatten

materialize_value sboxP

theorem flatten_getD {α : Type} {m : Nat} (d : α) (L : List (List α)) (hL : ∀ l ∈ L, l.length = m) (k : Nat) {n : Nat}
    (hn : n < m) : L.flatten.getD (m * k + n) d = (L.getD k []).getD n d := by
  induction L generalizing k with
  | nil => rfl
  | cons l L ih =>
    have hl := hL l List.mem_cons_self
    cases k with
    | zero =>
      rw [List.flatten_cons, Nat.mul_zero, Nat.zero_add, List.getD_cons_zero, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega_using [hl, hn]), ← List.getD_eq_getElem?_getD]
    | succ k =>
      have h : l.length ≤ m * (k + 1) + n := by rw [hl, Nat.mul_succ]; omega_using []
      rw [List.flatten_cons, List.getD_cons_succ, ← ih (fun l hl => hL l (List.mem_cons_of_mem _ hl)),
        List.getD_eq_getElem?_getD, List.getElem?_append_right h, ← List.getD_eq_getElem?_getD, hl, Nat.mul_succ,
        show m * k + m + n - m = m * k + n by omega_using []]

theorem sboxRows_length : ∀ l ∈ sboxRows, l.length = 256 := by
  intro l hl
  simp only [sboxRows, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [← s1L.2, Vector.length_toList]
  · rw [← s2L.2, Vector.length_toList]
  · rw [← s3L.2, Vector.length_toList]
  · rw [← s4L.2, Vector.length_toList]
  · rw [← s5L.2, Vector.length_toList]
  · rw [← s6L.2, Vector.length_toList]
  · rw [← s7L.2, Vector.length_toList]
  · rw [← s8L.2, Vector.length_toList]

theorem getD_toList (v : Vector Word 256) (b : Byte) : v.toList.getD b.toNat 0 = v[b.toFin] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [Vector.length_toList]; exact b.isLt),
    Option.getD_some, Vector.getElem_toList]
  rfl

/-- The index of S-box `j` (`sboxOf`). -/
def idx (j : Nat) : Nat := cond (Nat.blt j 8) j 7

theorem sboxOf_eq (j : Nat) (b : Byte) : Impl.Cast5.X86.Ssse3.sboxOf j b = (sboxRows.getD (idx j) []).getD b.toNat 0 := by
  match j with
  | 0 => exact (getD_toList _ b).symm.trans (by rw [s1L.2]; rfl)
  | 1 => exact (getD_toList _ b).symm.trans (by rw [s2L.2]; rfl)
  | 2 => exact (getD_toList _ b).symm.trans (by rw [s3L.2]; rfl)
  | 3 => exact (getD_toList _ b).symm.trans (by rw [s4L.2]; rfl)
  | 4 => exact (getD_toList _ b).symm.trans (by rw [s5L.2]; rfl)
  | 5 => exact (getD_toList _ b).symm.trans (by rw [s6L.2]; rfl)
  | 6 => exact (getD_toList _ b).symm.trans (by rw [s7L.2]; rfl)
  | 7 => exact (getD_toList _ b).symm.trans (by rw [s8L.2]; rfl)
  | n + 8 =>
    have : idx (n + 8) = 7 := by
      have : Nat.blt (n + 8) 8 = false := by
        rw [Bool.eq_false_iff]; intro h; have := Nat.blt_eq.mp h; omega_using [this]
      rw [idx, this]; rfl
    rw [this]
    exact (getD_toList _ b).symm.trans (by rw [s8L.2]; rfl)

end Proof.Cast5.X86.Ssse3

/-- `planeByte`, read from the packed S-boxes, which `unfoldToLits` (in the
planes' literals below) rewrites `planeByte` to. -/
noncomputable abbrev Impl.Cast5.X86.Ssse3.planeByte.lit (j p x : Nat) : Byte :=
  BitVec.ofNat 8 (Nat.shiftRight (Nat.mod (Nat.shiftRight Proof.Cast5.X86.Ssse3.sboxP.lit
    (Nat.mul 32 (Nat.add (Nat.mul 256 (Proof.Cast5.X86.Ssse3.idx j)) (Nat.mod x 256)))) 4294967296) (Nat.mul 8 p))

open Proof.Cast5.X86.Ssse3 in
theorem Impl.Cast5.X86.Ssse3.planeByte.lit_eq :
    Impl.Cast5.X86.Ssse3.planeByte = Impl.Cast5.X86.Ssse3.planeByte.lit := by
  funext j p x
  have h := packW_shift Proof.Cast5.sboxRows.flatten (256 * idx j + x % 256)
  rw [flatten_getD 0 _ sboxRows_length _ (Nat.mod_lt x (by decide)),
    ← show (BitVec.ofNat 8 x).toNat = x % 256 from BitVec.toNat_ofNat .., ← sboxOf_eq] at h
  rw [planeByte, planeByte.lit, ← sboxP.lit_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, ← h, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rfl

materialize_value planes0 := Impl.Cast5.X86.Ssse3.planesOf 0
materialize_value planes1 := Impl.Cast5.X86.Ssse3.planesOf 1
materialize_value planes2 := Impl.Cast5.X86.Ssse3.planesOf 2
materialize_value planes3 := Impl.Cast5.X86.Ssse3.planesOf 3
materialize_value planes4 := Impl.Cast5.X86.Ssse3.planesOf 4
materialize_value planes5 := Impl.Cast5.X86.Ssse3.planesOf 5
materialize_value planes6 := Impl.Cast5.X86.Ssse3.planesOf 6
materialize_value planes7 := Impl.Cast5.X86.Ssse3.planesOf 7
materialize_value Impl.Cast5.X86.Ssse3.table
materialize_code Impl.Cast5.X86.Ssse3.lookup
materialize_code Impl.Cast5.X86.Ssse3.cbcEncryptChained
materialize_code Impl.Cast5.X86.Ssse3.ofb
materialize_code Impl.Cast5.X86.Ssse3.cfbEncrypt
materialize_code Impl.Cast5.X86.Ssse3.cfbEncryptFinal
materialize_code Impl.Cast5.X86.Ssse3.cfbDecryptFinal
materialize_code Impl.Cast5.X86.Ssse3.ofbFinal

end VG
