import VerifiedGarbage.Proof.Framework.Mem

/-!
# A memory holding a table of constants

`constMem T W` holds the 64-bit words `W` at `T`, little-endian, and zeros
elsewhere (`constMem_held`): the memory of a witness that a contract with a
table of constants (`Abi.withConsts`) is satisfiable.
-/

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
      rw [Offset.add_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [constMem, e, show 8 * i + j < 8 * W.length by omega, ↓reduceIte,
        show (8 * i + j) / 8 = i by omega, show (8 * i + j) % 8 = j by omega]

end VG
