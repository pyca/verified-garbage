module

import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.Mem
import VerifiedGarbage.Proof.Framework.GetElem

/-!
# A memory holding a table of constants

`constMem T W` holds the 64-bit words `W` at `T`, little-endian, and zeros
elsewhere (`constMem_held`): the memory of a witness that a contract with a
table of constants (`Abi.withConsts`) is satisfiable.
-/

@[expose] public section

namespace VG

/-- The words `W` at `T`, and zeros elsewhere. -/
def constMem (T : Addr) (W : List (BitVec 64)) : Mem := fun a =>
  if (a - T).toNat < 8 * W.length then
    (W.getD ((a - T).toNat / 8) 0).extractLsb' (8 * ((a - T).toNat % 8)) 8
  else 0

theorem constMem_held (T : Addr) (W : List (BitVec 64)) (hW : 8 * W.length ≤ 2 ^ 64) :
    ∀ i < W.length, (constMem T W).readW (T + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0 := by
  intro i hi
  show ((constMem T W).read (T + BitVec.ofNat 64 (8 * i)) 8).setWidth 64 = _
  rw [Mem.read_eq_of_bytes (n := 8) (v := W.getD i 0) fun j hj => ?_]
  · exact BitVec.setWidth_eq _
  · have e : (T + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - T).toNat = 8 * i + j := by
      rw [Offset.add_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hW, hi, hj])]
    simp only [constMem, e, show 8 * i + j < 8 * W.length by omega_using [hi, hj], ↓reduceIte,
        show (8 * i + j) / 8 = i by omega_using [hj], show (8 * i + j) % 8 = j by omega_using [hj]]

/-- Two tables: the words `W₂` at `T₂`, and `constMem T₁ W₁` elsewhere. -/
def constMem2 (T₁ : Addr) (W₁ : List (BitVec 64)) (T₂ : Addr) (W₂ : List (BitVec 64)) : Mem := fun a =>
  if (a - T₂).toNat < 8 * W₂.length then constMem T₂ W₂ a else constMem T₁ W₁ a

theorem constMem2_held₂ (T₁ : Addr) (W₁ : List (BitVec 64)) (T₂ : Addr) (W₂ : List (BitVec 64))
    (hW : T₂.toNat + 8 * W₂.length ≤ 2 ^ 64) :
    ∀ i < W₂.length, (constMem2 T₁ W₁ T₂ W₂).readW (T₂ + BitVec.ofNat 64 (8 * i)) 64 = W₂.getD i 0 := by
  intro i hi
  rw [← constMem_held T₂ W₂ (by omega_using [hW]) i hi]
  refine Mem.readW_congr fun j hj => ?_
  have e : (T₂ + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - T₂).toNat = 8 * i + j := by
    rw [Offset.add_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_using [hW, hi, hj])]
  simp only [constMem2, e, show 8 * i + j < 8 * W₂.length by omega_using [hi, hj], ↓reduceIte]

theorem constMem2_held₁ (T₁ : Addr) (W₁ : List (BitVec 64)) (T₂ : Addr) (W₂ : List (BitVec 64))
    (hsep : T₁.toNat + 8 * W₁.length ≤ T₂.toNat) (hW : T₂.toNat + 8 * W₂.length ≤ 2 ^ 64) :
    ∀ i < W₁.length, (constMem2 T₁ W₁ T₂ W₂).readW (T₁ + BitVec.ofNat 64 (8 * i)) 64 = W₁.getD i 0 := by
  intro i hi
  rw [← constMem_held T₁ W₁ (by omega_using [hsep, hW]) i hi]
  refine Mem.readW_congr fun j hj => ?_
  have hlt : (T₁ + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j).toNat = T₁.toNat + 8 * i + j := by
    rw [Offset.add_add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hsep, hW, hi, hj]),
      Nat.mod_eq_of_lt (by omega_using [hsep, hW, hi, hj])]
    omega_using []
  have hn : ¬ (T₁ + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - T₂).toNat < 8 * W₂.length := by
    rw [BitVec.toNat_sub, hlt]
    omega_using [hsep, hW, hi, hj, T₂.isLt]
  simp only [constMem2, hn, ↓reduceIte]

end VG
