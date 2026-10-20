module

public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Mem

/-! Tightening memory frames using preserved whole words. -/

@[expose] public section
namespace VG.Proof.Bignum
open VG

theorem word_eq_byte {m m' : Mem} {B x : Addr} {d : Nat}
    (h : word m' B d = word m B d) (lo : d ≤ ofs B x) (hi : ofs B x < d + 8) :
    m' x = m x := by
  let j := ofs B x - d
  have hj : j < 8 := by omega
  have hx : off B d + BitVec.ofNat 64 j = x := by
    simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [show d + j = ofs B x by omega]
    simp only [ofs, BitVec.ofNat_toNat]
    bv_omega
  have he := congrArg (fun v : BitVec 64 => v.extractLsb' (8 * j) 8) h
  change (m'.read (off B d) 8).extractLsb' (8 * j) 8 =
    (m.read (off B d) 8).extractLsb' (8 * j) 8 at he
  rw [Mem.extractLsb'_read _ _ hj, Mem.extractLsb'_read _ _ hj, hx] at he
  exact he

theorem Frm.drop_word {m m' : Mem} {B : Addr} {d : Nat} {rs : List (Nat × Nat)}
    (h : Frm B ((d, 8) :: rs) m m') (hw : word m' B d = word m B d) :
    Frm B rs m m' := by
  intro x hx
  by_cases lo : d ≤ ofs B x
  · by_cases hi : ofs B x < d + 8
    · exact word_eq_byte hw lo hi
    · apply h x
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact Or.inr (Nat.le_of_not_gt hi)
      · exact hx r hr
  · apply h x
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact Or.inl (Nat.lt_of_not_ge lo)
    · exact hx r hr

end VG.Proof.Bignum
