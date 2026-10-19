module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedSetup
public import VerifiedGarbage.Proof.Bignum.X86.PublicPower

/-! # Stored R², input, and exponent survive the inverse-and-one setup -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.Proof.Mont VG.Impl.Bignum.X86.PublicContext

theorem precomputedSetup_value {n i : Nat} {base : Addr} {m m' : Mem}
    (O : Outs base [(56, 4), (VG.Impl.Bignum.X86.PublicContext.slot n 4, 8 * n)] m m') (hi : i < 8) (hi4 : i ≠ 4)
    (bound : size n ≤ 2 ^ 64) : wordsVal m' base (VG.Impl.Bignum.X86.PublicContext.slot n i) n = wordsVal m base (VG.Impl.Bignum.X86.PublicContext.slot n i) n := by
  have b := slot_bound (n := n) hi
  have sep := slot_sep (n := n) hi4
  have hdr := slot_header n i
  simp only [stride] at b sep
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  apply O.val32
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> omega
  · omega

theorem precomputedSetup_ranges {n : Nat} {base : Addr} {m m' : Mem}
    (O : Outs base [(56, 4), (VG.Impl.Bignum.X86.PublicContext.slot n 4, 8 * n)] m m') : Outs base (setupRanges n) m m' := by
  refine O.mono ?_
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp [setupRanges]

end VG.Proof.Bignum.X86.PublicContext
