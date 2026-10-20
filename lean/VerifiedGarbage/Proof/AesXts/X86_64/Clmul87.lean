module

public import VerifiedGarbage.Proof.AesXts.Alpha16
public import VerifiedGarbage.TCB.X86_64.Sse
import Mathlib.Data.List.Induction

/-!
# XTS on x86-64: `clmul` by `0x87`

`clmul_87`: the carry-less product (`VG.X86_64.clmul`, PCLMULQDQ's) of a
quadword by `0x87` is `P` of it (`Proof/AesXts/Alpha16.lean`), which turns
`vpclmulqdq` of the top sixteen bits of a tweak into the reduction of sixteen
multiplications by `α`.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64

open VG VG.X86_64
open VG.Proof.AesXts (P P_xor P_shl P_zero)

theorem setWidth_succ (a : BitVec 64) {k : Nat} (hk : k < 64) :
    (a.setWidth (k + 1)).setWidth 128 =
      (a.setWidth k).setWidth 128 ^^^ (if a.getLsbD k then (1 : BitVec 128) <<< k else 0) := by
  ext i hi
  rcases Nat.lt_trichotomy i k with h | rfl | h
  · cases hb : a.getLsbD k <;> simp [BitVec.getElem_setWidth, BitVec.getElem_shiftLeft, h, show i < k + 1 by omega]
  · cases hb : a.getLsbD i <;> simp [BitVec.getElem_setWidth, BitVec.getElem_shiftLeft, hb]
  · cases hb : a.getLsbD k <;> simp [BitVec.getElem_setWidth, BitVec.getElem_shiftLeft, show ¬ i < k + 1 by omega,
      show ¬ i < k by omega, show ¬ i - k = 0 by omega]

/-- `clmul` of `a` by `0x87` is `P` of it. -/
theorem clmul_87 (a : BitVec 64) : clmul a 0x87 = P (a.setWidth 128) := by
  have h : ∀ k ≤ 64, (List.range k).foldl
      (fun acc j => if a.getLsbD j then acc ^^^ ((0x87 : BitVec 64).setWidth 128 <<< j) else acc) 0 =
      P ((a.setWidth k).setWidth 128) := by
    intro k hk
    induction k with
    | zero =>
      simp only [List.range_zero, List.foldl_nil]
      rw [show (a.setWidth 0).setWidth 128 = 0#128 by ext i; simp]
      rfl
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, ih (by omega), setWidth_succ a (by omega), P_xor]
      cases hb : a.getLsbD k
      · simp only [List.foldl_cons, List.foldl_nil, hb, Bool.false_eq_true, ↓reduceIte]
        rw [show P 0 = 0 from rfl]; simp
      · simp only [List.foldl_cons, List.foldl_nil, hb, ↓reduceIte, P_shl]
        rw [show BitVec.setWidth 128 (0x87 : BitVec 64) = P 1 from rfl]
  rw [clmul, h 64 (Nat.le_refl _), BitVec.setWidth_eq]

end VG.Proof.AesXts.X86_64
