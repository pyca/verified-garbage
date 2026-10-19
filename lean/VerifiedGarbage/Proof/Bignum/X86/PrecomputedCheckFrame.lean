module
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Proof.Mont.Words32

import VerifiedGarbage.Proof.Bignum.X86.PublicLayout

/-! # Public precomputation validation leaves the packed key arrays untouched -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.Proof.Mont VG.Impl.Bignum.X86.PublicContext

def precomputedCheckRanges (n : Nat) : List (Nat × Nat) := [(VG.Impl.Bignum.X86.PublicContext.slot n 4, 8 * n), (VG.Impl.Bignum.X86.PublicContext.slot n 1, 8 * n), (148, 4)]

theorem precomputedCheck_value {n i : Nat} {base : Addr} {m m' : Mem}
    (O : Outs base (precomputedCheckRanges n) m m') (hi : i < 8) (hi1 : i ≠ 1) (hi4 : i ≠ 4)
    (bound : size n ≤ 2 ^ 64) : wordsVal m' base (VG.Impl.Bignum.X86.PublicContext.slot n i) n = wordsVal m base (VG.Impl.Bignum.X86.PublicContext.slot n i) n := by
  have b := slot_bound (n := n) hi
  have s1 := slot_sep (n := n) hi1
  have s4 := slot_sep (n := n) hi4
  have hdr := slot_header n i
  simp only [stride] at b s1 s4
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  apply O.val32
  · intro r hr
    simp only [precomputedCheckRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> omega
  · omega

theorem precomputedCheck_saved {n bytes : Nat} {base : Addr} {m m' : Mem}
    (O : Outs base (precomputedCheckRanges n) m m') (bound : size n ≤ bytes) :
    Outside base 16 (bytes - 16) m m' := by
  have b1 := slot_bound (n := n) (i := 1) (by decide)
  have b4 := slot_bound (n := n) (i := 4) (by decide)
  have hd1 := slot_header n 1
  have hd4 := slot_header n 4
  simp only [stride] at b1 b4
  intro a ha
  apply O a
  intro r hr
  simp only [precomputedCheckRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> omega

end VG.Proof.Bignum.X86.PublicContext
