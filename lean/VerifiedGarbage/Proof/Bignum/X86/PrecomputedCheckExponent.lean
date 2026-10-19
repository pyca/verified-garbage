module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedCheckFrame
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout

/-! # Packed-key validation preserves the saved public exponent -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.Proof.Mont VG.Impl.Bignum.X86.PublicContext

theorem precomputedCheck_exponent {n : Nat} {base : Addr} {m m' : Mem}
    (O : Outs base (precomputedCheckRanges n) m m') : val32 m' base 128 2 = val32 m base 128 2 := by
  have d1 := slot_header n 1
  have d4 := slot_header n 4
  apply O.val32
  · intro r hr
    simp only [precomputedCheckRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> omega
  · decide

end VG.Proof.Bignum.X86.PublicContext
