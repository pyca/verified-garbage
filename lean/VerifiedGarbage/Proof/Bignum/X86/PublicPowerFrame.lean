module
public import VerifiedGarbage.Proof.Bignum.X86.PublicSetup

import VerifiedGarbage.Proof.Bignum.X86.PublicLayout

/-! # The public-power kernel preserves saved arguments and acceptance -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.Impl.Bignum.X86.PublicContext VG.Proof.Mont

theorem powerRanges_bound {n : Nat} {r : Nat × Nat}
    (hr : r ∈ setupRanges n ++ exponentRanges n) : r.1 + r.2 ≤ size n := by
  simp only [setupRanges, exponentRanges, productRanges, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [slot, stride, size, VG.Impl.Bignum.hdrBytes] <;> omega

theorem powerRanges_start {n : Nat} {r : Nat × Nat}
    (hr : r ∈ setupRanges n ++ exponentRanges n) : 16 ≤ r.1 := by
  simp only [setupRanges, exponentRanges, productRanges, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [slot, VG.Impl.Bignum.hdrBytes] <;> omega

theorem power_saved {n bytes : Nat} {base : Addr} {m m' : Mem}
    (h : Outs base (setupRanges n ++ exponentRanges n) m m') (bound : size n ≤ bytes) :
    Outside base 16 (bytes - 16) m m' := by
  intro a ha
  apply h a
  intro r hr
  have := powerRanges_bound hr
  have := powerRanges_start hr
  have sz := size_eq n
  omega

theorem power_outside {n bytes : Nat} {base : Addr} {m m' : Mem}
    (h : Outs base (setupRanges n ++ exponentRanges n) m m') (bound : size n ≤ bytes) :
    Outside base 0 bytes m m' := by
  intro a ha
  apply h a
  intro r hr
  have := powerRanges_bound hr
  omega

theorem power_header {n d : Nat} {base : Addr} {m m' : Mem}
    (h : Outs base (setupRanges n ++ exponentRanges n) m m')
    (hd : d + 4 ≤ 56 ∨ 140 ≤ d ∧ d + 4 ≤ 256) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 := by
  have V : val32 m' base d 1 = val32 m base d 1 := by
    apply h.val32
    · intro r hr
      simp only [setupRanges, exponentRanges, productRanges, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [slot, stride, VG.Impl.Bignum.hdrBytes] <;> omega
    · omega
  apply BitVec.eq_of_toNat_eq
  simpa only [val32, w32, Nat.mul_zero, Nat.add_zero] using V

end VG.Proof.Bignum.X86.PublicContext
