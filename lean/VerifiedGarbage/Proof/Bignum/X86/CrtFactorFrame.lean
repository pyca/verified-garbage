module

public import VerifiedGarbage.Proof.Bignum.X86.CrtFactorPower

/-! # Saving a factor residue leaves every other preserved component intact -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.Proof.Mont VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic VG.Impl.Bignum.X86.Crt

theorem factor_value {n output i k : Nat} {base : Addr} {m m' : Mem}
    (O : Outs base (factorRanges n output) m m') (hi : 9 ≤ i) (hi' : i < 20)
    (ne : i ≠ output) (hk : k ≤ 2 * n) (fit : size n ≤ 2 ^ 64) :
    wordsVal m' base (slot n i) k = wordsVal m base (slot n i) k := by
  have before : contextBytes n ≤ slot n i := by
    unfold contextBytes slot
    have := Nat.mul_le_mul_right (stride n) hi
    omega
  have head := slot_header n i
  have bound := slot_bound (n := n) hi'
  have sep := slot_sep (n := n) ne
  have tb := slot_le (n := n) (i := i) (j := 20) hi'
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  apply O.val32
  · intro r hr
    simp only [factorRanges, arithmeticRanges, tableRange, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> unfold stride at sep tb <;> omega
  · unfold stride at bound; omega

end VG.Proof.Bignum.X86.Crt
