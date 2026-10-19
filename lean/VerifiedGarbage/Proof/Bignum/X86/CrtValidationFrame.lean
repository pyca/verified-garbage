module

public import VerifiedGarbage.Proof.Bignum.X86.CrtProductLayout
public import VerifiedGarbage.Proof.Bignum.X86.CrtSlotFrame

/-! # Validation changes only its full product and two mask words -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86.Crt

def validationRanges (n : Nat) : List (Nat × Nat) :=
  [(slot n productSlot, 4 * (2 * (2 * n) + 1)), (multiplierOffset, 4), (acceptanceOffset, 4)]

theorem validation_value {n i k : Nat} {base : Addr} {m m' : Mem}
    (O : Outs base (validationRanges n) m m') (hi : i < productSlot) (hk : k ≤ 2 * n)
    (fit : size n ≤ 2 ^ 64) : wordsVal m' base (slot n i) k = wordsVal m base (slot n i) k := by
  have sep := slot_le (n := n) hi
  have bound := slot_bound (n := n) (i := i) (by unfold productSlot at hi; omega)
  have head := slot_header n i
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  apply O.val32
  · intro r hr
    simp only [validationRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [multiplierOffset, acceptanceOffset] <;>
      unfold stride at sep <;> omega
  · unfold stride at bound; omega

end VG.Proof.Bignum.X86.Crt
