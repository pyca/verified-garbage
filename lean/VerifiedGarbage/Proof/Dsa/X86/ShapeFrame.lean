module
public import VerifiedGarbage.Proof.Dsa.X86.ShapeCombine
public import VerifiedGarbage.Proof.Mont.Words32

import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Weierstrass.PointContract

/-! # Frames for width-mask scratch and public header slots -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86

theorem widthFrame_modulus {s t : State} {base : Addr} {n output count : Nat}
    (O : Outs base [(slot n 8, 8 * n), (output, count)] s.mem t.mem)
    (ho : output + count ≤ 64) (hb : contextBytes n ≤ 2 ^ 64) :
    wordsVal t.mem base (slot n 0) n = wordsVal s.mem base (slot n 0) n := by
  have b := slot_bound (n := n) (i := 0) (by decide)
  have sep := slot_le (n := n) (i := 0) (j := 8) (by decide)
  have h0 := slot_header n 0
  simp only [stride] at b sep
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  apply O.val32
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> omega
  · omega

theorem widthFrame_header {s t : State} {base : Addr} {n output d : Nat}
    (O : Outs base [(slot n 8, 8 * n), (output, 4)] s.mem t.mem)
    (hd : d + 4 ≤ 64) (hsep : d + 4 ≤ output ∨ output + 4 ≤ d) :
    shapeWord t base d = shapeWord s base d := by
  have h8 := slot_header n 8
  apply BitVec.eq_of_toNat_eq
  have H : val32 t.mem base d 1 = val32 s.mem base d 1 := by
    apply O.val32
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> omega
    · omega
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using H

theorem widthFrame_widen {s t : State} {base : Addr} {n output lo len : Nat}
    (O : Outs base [(slot n 8, 8 * n), (output, 4)] s.mem t.mem)
    (hl : lo ≤ output) (hh : output + 4 ≤ lo + len) :
    Outs base [(slot n 8, 8 * n), (lo, len)] s.mem t.mem := by
  intro x hx
  apply O x
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hx _ (by simp)
  · have H := hx (lo, len) (by simp)
    omega

end VG.Proof.Dsa.X86
