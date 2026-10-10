import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SM4's proofs: what every target uses

Facts about addresses and memory that the targets' proofs of the ECB
functions share: offsets (`off_sub_toNat`, …), copies of words
(`writeW_readW_apply`), and the data loop's invariant (`DInv`) and its result
(`blocksAt_of_dinv`). Nothing here depends on a target.
-/

namespace VG.Proof.Sm4

open VG VG.Spec.Sm4

/-! ## Addresses -/

theorem off_sub_toNat (B : Addr) {t e : Nat} (h : e ≤ t) (ht : t < 2 ^ 64) :
    (B + BitVec.ofNat 64 t - (B + BitVec.ofNat 64 e)).toNat = t - e := by
  rw [VG.Offset.add_sub_add _ h, BitVec.toNat_ofNat]; omega

theorem off_sub_not (B : Addr) {t e n : Nat} (h : t < e ∨ e + n ≤ t) (ht : t < 2 ^ 64) (hn : 0 < n)
    (he : e + n ≤ 2 ^ 64) : ¬ (B + BitVec.ofNat 64 t - (B + BitVec.ofNat 64 e)).toNat < n := by
  rw [VG.Offset.add_sub_add_left]; exact VG.Offset.not_lt_sub_ofNat h ht hn he

theorem not_contains_off (b : Addr) {t e n : Nat} (h : t < e ∨ e + n ≤ t) (ht : t < 2 ^ 64) (hn : 0 < n)
    (he : e + n ≤ 2 ^ 64) : ¬ (⟨b + BitVec.ofNat 64 e, n⟩ : Region).Contains (b + BitVec.ofNat 64 t) 1 := by
  simp only [Region.Contains]; intro hc; exact off_sub_not b h ht hn he (by omega)

/-- A byte of `A`'s area is not among the 8 at `B + e`. -/
theorem not_in_of_disjoint {A B : Addr} {n t e : Nat} (hsep : Region.Disjoint ⟨A, n⟩ ⟨B, n⟩) (ht : t < n)
    (he : e + 8 ≤ n) (hn : n < 2 ^ 64) : ¬ (A + BitVec.ofNat 64 t - (B + BitVec.ofNat 64 e)).toNat < 8 :=
  fun h => hsep (A + BitVec.ofNat 64 t) (VG.Offset.contains_base A (by omega) (by omega))
    (VG.Offset.sub_base B he _ (by simp only [Region.Contains]; omega))

theorem toNat_off (b : Addr) {d : Nat} (h : b.toNat + d < 2 ^ 64) : (b + BitVec.ofNat 64 d).toNat = b.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64), Nat.mod_eq_of_lt h]

theorem ofInt_nat (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

/-! ## Memory -/

/-- A byte of a little-endian word stored from a load. -/
theorem writeW_readW_apply (m m' : Mem) (a c x : Addr) :
    m.writeW a (m'.readW c 64) x =
      if (x - a).toNat < 8 then m' (c + BitVec.ofNat 64 (x - a).toNat) else m x := by
  simp only [Mem.writeW, Mem.write, Mem.readW, BitVec.setWidth_eq]
  split
  · rename_i h
    exact Mem.extractLsb'_read m' c (n := 8) h
  · rfl

/-- A byte of a little-endian 32-bit word stored from a load. -/
theorem writeW_readW32_apply (m m' : Mem) (a c x : Addr) :
    m.writeW a (m'.readW c 32) x =
      if (x - a).toNat < 4 then m' (c + BitVec.ofNat 64 (x - a).toNat) else m x := by
  simp only [Mem.writeW, Mem.write, Mem.readW, BitVec.setWidth_eq]
  split
  · rename_i h
    exact Mem.extractLsb'_read m' c (n := 4) h
  · rfl

/-- A byte of a word written. -/
theorem writeW32_byte (m : Mem) (a : Addr) (v : BitVec 32) {t j : Nat} (ht : t < 4) (hj : j < 8) :
    ((m.writeW a v) (a + BitVec.ofNat 64 t)).getLsbD j = v.getLsbD (8 * t + j) := by
  simp only [Mem.writeW, Mem.write, BitVec.setWidth_eq, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  simp only [show t < 32 / 8 by omega, ↓reduceIte, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]

/-- A byte outside a word written. -/
theorem writeW32_other (m : Mem) (a x : Addr) (v : BitVec 32) (h : ¬ (x - a).toNat < 4) :
    (m.writeW a v) x = m x := by
  simp only [Mem.writeW, Mem.write]
  exact ite_eq_right fun h' => h (by simpa using h')

/-- A word written inside `R`. -/
theorem frame_writeW {m : Mem} {a : Addr} {R : Region} (v : BitVec 64) (hs : Region.Sub ⟨a, 8⟩ R) :
    Frame [R] m (m.writeW a v) := fun x hx => by
  simp only [Mem.writeW, Mem.write]
  exact ite_eq_right fun h => hx R (List.mem_singleton_self _) (hs x (by simp only [Region.Contains]; omega))

/-! ## Blocks -/

/-- The first `k` blocks are `F`'s, the others still `m₀`'s. -/
def DInv (m₀ m : Mem) (D : Addr) (n k : Nat) (F : Nat → Block) : Prop :=
  ∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    if i < 16 * k then (F (i / 16)).getD (i % 16) 0 else m₀ (D + BitVec.ofNat 64 i)

theorem blocksAt_of_dinv {m₀ m : Mem} {D : Addr} {n : Nat} {F : Nat → Block}
    (h : DInv m₀ m D n n F) : blocksAt m D n = (List.range n).map F := by
  simp only [blocksAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  apply Vector.ext; intro t ht
  simp only [blockAt, Vector.getElem_ofFn]
  rw [VG.Offset.add_add, h _ (by omega), ite_eq_left (by omega), show (16 * j + t) / 16 = j by omega,
    show (16 * j + t) % 16 = t by omega]
  simp [Vector.getD, ht]

/-- The block function of each direction. -/
def blockFn (sch : Schedule) : Direction → Block → Block
  | .encrypt => encryptBlock sch
  | .decrypt => decryptBlock sch

theorem ecb_eq (sch : Schedule) (d : Direction) (l : List Block) : ecb sch d l = l.map (blockFn sch d) := by
  cases d <;> rfl

end VG.Proof.Sm4
