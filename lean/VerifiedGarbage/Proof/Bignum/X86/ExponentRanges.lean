module

public import VerifiedGarbage.Proof.Bignum.X86.PublicMath

import VerifiedGarbage.Proof.Bignum.X86.PublicLayout

/-! # What the exponentiation in the compact workspace writes -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86.PublicContext

def productRanges (n : Nat) : List (Nat × Nat) :=
  [(136, 4), (slot n 5, 8 * n), (slot n 7, 8 * n), (slot n 1, 8 * n), (slot n 2, 16 * n + 4)]

def exponentRanges (n : Nat) : List (Nat × Nat) :=
  productRanges n ++ [(slot n 6, 8 * n), (128, 8)]

theorem exponent_one {n : Nat} {base : Addr} {s t : State}
    (O : Outs base (exponentRanges n) s.mem t.mem) (hn : size n ≤ 2 ^ 64) :
    wordsVal t.mem base (slot n 4) n = wordsVal s.mem base (slot n 4) n := by
  have h1 := slot_le (n := n) (i := 1) (j := 4) (by decide)
  have h2 := acc_end n
  have h5 := slot_le (n := n) (i := 4) (j := 5) (by decide)
  have h6 := slot_le (n := n) (i := 4) (j := 6) (by decide)
  have h7 := slot_le (n := n) (i := 4) (j := 7) (by decide)
  have hd := slot_header n 4
  have bd := slot_bound (n := n) (i := 4) (by decide)
  simp only [stride, acc_length] at *
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  apply O.val32
  · intro r hr
    simp only [exponentRanges, productRanges, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · omega

theorem exponent_op {n o : Nat} {base : Addr} {s t : State}
    (K : OpKeep (modulus n) base (slot n 2) (slot n o) s t) (ho : o = 6 ∨ o = 7) :
    Outs base (exponentRanges n) s.mem t.mem := by
  refine K.mem.mono ?_
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rcases ho with rfl | rfl <;> simp [exponentRanges, productRanges, modulus]
  · simp [exponentRanges, productRanges, modulus]
  · simp [exponentRanges, productRanges, modulus, accLen, words]
    omega

end VG.Proof.Bignum.X86.PublicContext
