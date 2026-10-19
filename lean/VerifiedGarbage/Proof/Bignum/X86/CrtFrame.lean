module

public import VerifiedGarbage.Proof.Bignum.X86.CrtLayout
public import VerifiedGarbage.Proof.Bignum.X86.CheckedPrimePower
public import VerifiedGarbage.Proof.Bignum.X86.CrtCoefficient

/-! # Arithmetic preserves the saved CRT components and callee-saved header -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic

def arithmeticRanges (n : Nat) : List (Nat × Nat) := [(0, 8), (64, contextBytes n - 64)]

theorem arithmetic_value {n i k : Nat} {base : Addr} {m m' : Mem}
    (O : Outs base (arithmeticRanges n) m m') (hi : 9 ≤ i) (hi' : i < 20) (hk : k ≤ 2 * n)
    (fit : VG.Impl.Bignum.X86.Crt.size n ≤ 2 ^ 64) :
    wordsVal m' base (slot n i) k = wordsVal m base (slot n i) k := by
  have before : contextBytes n ≤ slot n i := by
    unfold contextBytes slot
    have := Nat.mul_le_mul_right (stride n) hi
    omega
  have bound := slot_bound (n := n) hi'
  have head := slot_header n i
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  apply O.val32
  · intro r hr
    simp only [arithmeticRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> omega
  · unfold stride at bound; omega

theorem arithmetic_header {n d : Nat} {base : Addr} {m m' : Mem}
    (O : Outs base (arithmeticRanges n) m m') (lo : 8 ≤ d) (hi : d + 4 ≤ 64) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 := by
  have V : val32 m' base d 1 = val32 m base d 1 := by
    apply O.val32
    · intro r hr
      simp only [arithmeticRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> omega
    · omega
  apply BitVec.eq_of_toNat_eq
  simpa only [val32, w32, Nat.mul_zero, Nat.add_zero] using V

theorem prime_arithmetic_frame {n : Nat} {base : Addr} {m m' : Mem}
    (O : Outs base (primeSetupRanges n ++ exponentRanges n (2 * n)) m m') :
    Outs base (arithmeticRanges n) m m' := by
  intro a ha
  have low := ha (0, 8) (by simp [arithmeticRanges])
  have high := ha (64, contextBytes n - 64) (by simp [arithmeticRanges])
  apply O a
  intro r hr
  simp only [primeSetupRanges, setupRanges, exponentRanges, productRanges,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [slot, stride, contextBytes] at * <;> omega

theorem coefficient_arithmetic_frame {n : Nat} {base : Addr} {m m' : Mem}
    (O : Outs base (coefficientRanges n) m m') : Outs base (arithmeticRanges n) m m' := by
  intro a ha
  have high := ha (64, contextBytes n - 64) (by simp [arithmeticRanges])
  apply O a
  intro r hr
  simp only [coefficientRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    simp only [slot, stride, contextBytes] at * <;> omega

end VG.Proof.Bignum.X86.Crt
