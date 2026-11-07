module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Double

/-! # Facts for `R² mod M` at a run-time width

`edi` back to its value (`Keeps.drop_edi`), the selection of a conditional
subtraction (`select_mod'`), and a count down by one (`count1_zf`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86

/-- `Keeps` of registers and `edi`, which is back to its value. -/
theorem Keeps.drop_edi {rs : List Reg} {s t : State} (K : Keeps (rs ++ ([.edi] : List Reg)) s t)
    (he : t.gpr .edi = s.gpr .edi) : Keeps rs s t := by
  refine ⟨fun r hr => ?_, K.2.1, K.2.2⟩
  by_cases h : r = .edi
  · subst h; exact he
  · exact K.1 r (by simp [hr, h])

/-- The selection of the conditional subtraction, by the mask of a borrow below the top word. -/
theorem select_mod' {Tl D top X M : Nat} {c : Bool} (hX : M < X) (hD : D < X) (hV : Tl + X * top < 2 * M)
    (he : D + M = Tl + X * c.toNat) :
    (if decide (top < c.toNat) then Tl else D) = (Tl + X * top) % M := by
  rw [← select_mod hX hD hV he]
  by_cases h : top < c.toNat <;> simp [h]

/-- A count down by one: ZF when it reaches zero. -/
theorem count1_zf {x : BitVec 32} {N j : Nat} (hx : x.toNat = N - j) (hj : j < N) :
    (x - 1).toNat = N - (j + 1) ∧ (x - 1 == 0) = decide (j + 1 = N) := by
  have h1 : (x - 1).toNat = N - (j + 1) := by
    rw [BitVec.toNat_sub, hx, show (1 : BitVec 32).toNat = 1 from rfl]
    have := x.isLt
    omega
  refine ⟨h1, ?_⟩
  by_cases h : j + 1 = N
  · simp only [h, decide_true, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq; rw [h1]; simp; omega
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro hz
    have := congrArg BitVec.toNat hz
    rw [h1] at this
    simp at this
    omega

end VG.Proof.Bignum.X86.PublicRt
