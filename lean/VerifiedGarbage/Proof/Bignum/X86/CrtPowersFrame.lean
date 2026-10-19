module

public import VerifiedGarbage.Proof.Bignum.X86.CrtBothPowers

/-! # Both powers leave the imported components intact -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.Proof.Mont VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic VG.Impl.Bignum.X86.Crt

theorem powers_value {n i k : Nat} {base : Addr} {m m' : Mem}
    (O : Outs base (powersRanges n) m m') (hi : 9 ≤ i) (hi' : i < 16) (hk : k ≤ 2 * n)
    (fit : size n ≤ 2 ^ 64) : wordsVal m' base (slot n i) k = wordsVal m base (slot n i) k := by
  have before : contextBytes n ≤ slot n i := by
    unfold contextBytes slot
    have := Nat.mul_le_mul_right (stride n) hi
    omega
  have head := slot_header n i
  have bound := slot_bound (n := n) (i := i) (by omega)
  have p := slot_le (n := n) (i := i) (j := mpSlot) (by unfold mpSlot; omega)
  have q := slot_le (n := n) (i := i) (j := mqSlot) (by unfold mqSlot; omega)
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  apply O.val32
  · intro r hr
    simp only [powersRanges, arithmeticRanges, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> unfold stride at p q <;> omega
  · unfold stride at bound; omega

end VG.Proof.Bignum.X86.Crt
