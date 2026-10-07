import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Selected
import VerifiedGarbage.Proof.Framework.AArch64.Lit

namespace VG.Proof.Weierstrass.AArch64.Forward.P256Bounds
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.P256.VerifyDouble
open VG.Proof.Weierstrass.AArch64.Forward

materialize_value leftRD := Fixed.original R D
materialize_value rightRD := Fixed.optimized R D
materialize_value leftDR := Fixed.original D R
materialize_value rightDR := Fixed.optimized D R
materialize_value leftED := Fixed.original E D
materialize_value rightED := Fixed.optimized E D

private theorem bound_of_all {is : List Instr}
    (h : is.all (fun i => decide (instrBound i≤992))=true) : ∀ i∈is,instrBound i≤992 := by
  intro i hi
  exact of_decide_eq_true ((List.all_eq_true.mp h) i hi)

private theorem clob_of_all {is : List Instr}
    (h : (is.flatMap instrClob).all (fun r => decide (r∈VG.Proof.Mont.AArch64.clob M.n))=true) :
    ∀ r∈is.flatMap instrClob,r∈VG.Proof.Mont.AArch64.clob M.n := by
  intro r hr
  exact of_decide_eq_true ((List.all_eq_true.mp h) r hr)

theorem rd_left : ∀ i∈Fixed.original R D,instrBound i≤992 := bound_of_all (by rw [leftRD.lit_eq]; decide +kernel)
theorem rd_right : ∀ i∈Fixed.optimized R D,instrBound i≤992 := bound_of_all (by rw [rightRD.lit_eq]; decide +kernel)
theorem rd_clob : ∀ r∈(Fixed.optimized R D).flatMap instrClob,r∈VG.Proof.Mont.AArch64.clob M.n :=
  clob_of_all (by rw [rightRD.lit_eq]; decide +kernel)

theorem dr_left : ∀ i∈Fixed.original D R,instrBound i≤992 := bound_of_all (by rw [leftDR.lit_eq]; decide +kernel)
theorem dr_right : ∀ i∈Fixed.optimized D R,instrBound i≤992 := bound_of_all (by rw [rightDR.lit_eq]; decide +kernel)
theorem dr_clob : ∀ r∈(Fixed.optimized D R).flatMap instrClob,r∈VG.Proof.Mont.AArch64.clob M.n :=
  clob_of_all (by rw [rightDR.lit_eq]; decide +kernel)

theorem ed_left : ∀ i∈Fixed.original E D,instrBound i≤992 := bound_of_all (by rw [leftED.lit_eq]; decide +kernel)
theorem ed_right : ∀ i∈Fixed.optimized E D,instrBound i≤992 := bound_of_all (by rw [rightED.lit_eq]; decide +kernel)
theorem ed_clob : ∀ r∈(Fixed.optimized E D).flatMap instrClob,r∈VG.Proof.Mont.AArch64.clob M.n :=
  clob_of_all (by rw [rightED.lit_eq]; decide +kernel)

end VG.Proof.Weierstrass.AArch64.Forward.P256Bounds
