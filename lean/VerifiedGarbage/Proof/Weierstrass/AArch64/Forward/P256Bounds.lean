import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Selected
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Kernel

namespace VG.Proof.Weierstrass.AArch64.Forward.P256Bounds
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.P256.VerifyDouble
open VG.Proof.Weierstrass.AArch64.Forward

materialize_value leftRD := Fixed.original R D
forward_state rightRD.lit := Fixed.optimized R D
theorem rightRD.lit_eq : Fixed.optimized R D=rightRD.lit := optimize_of_lit leftRD.lit_eq (by kernel_rfl)
materialize_value leftDR := Fixed.original D R
forward_state rightDR.lit := Fixed.optimized D R
theorem rightDR.lit_eq : Fixed.optimized D R=rightDR.lit := optimize_of_lit leftDR.lit_eq (by kernel_rfl)
materialize_value leftED := Fixed.original E D
forward_state rightED.lit := Fixed.optimized E D
theorem rightED.lit_eq : Fixed.optimized E D=rightED.lit := optimize_of_lit leftED.lit_eq (by kernel_rfl)

theorem rd_left : ∀ i∈Fixed.original R D,instrBound i≤992 := by
  rw [leftRD.lit_eq]; exact bound_of_listAllK (by decide +kernel)
private theorem rd_ok : listAllK (instrOkK 992 (RegSet.ofList (VG.Proof.Mont.AArch64.clob M.n)) [(0,992)])
    rightRD.lit=true := by decide +kernel
theorem rd_right : ∀ i∈Fixed.optimized R D,instrBound i≤992 := by
  rw [rightRD.lit_eq]; exact bound_of_instrOk rd_ok
theorem rd_clob : ∀ r∈(Fixed.optimized R D).flatMap instrClob,r∈VG.Proof.Mont.AArch64.clob M.n := by
  rw [rightRD.lit_eq]; exact clob_of_instrOk rd_ok

theorem dr_left : ∀ i∈Fixed.original D R,instrBound i≤992 := by
  rw [leftDR.lit_eq]; exact bound_of_listAllK (by decide +kernel)
private theorem dr_ok : listAllK (instrOkK 992 (RegSet.ofList (VG.Proof.Mont.AArch64.clob M.n)) [(0,992)])
    rightDR.lit=true := by decide +kernel
theorem dr_right : ∀ i∈Fixed.optimized D R,instrBound i≤992 := by
  rw [rightDR.lit_eq]; exact bound_of_instrOk dr_ok
theorem dr_clob : ∀ r∈(Fixed.optimized D R).flatMap instrClob,r∈VG.Proof.Mont.AArch64.clob M.n := by
  rw [rightDR.lit_eq]; exact clob_of_instrOk dr_ok

theorem ed_left : ∀ i∈Fixed.original E D,instrBound i≤992 := by
  rw [leftED.lit_eq]; exact bound_of_listAllK (by decide +kernel)
private theorem ed_ok : listAllK (instrOkK 992 (RegSet.ofList (VG.Proof.Mont.AArch64.clob M.n)) [(0,992)])
    rightED.lit=true := by decide +kernel
theorem ed_right : ∀ i∈Fixed.optimized E D,instrBound i≤992 := by
  rw [rightED.lit_eq]; exact bound_of_instrOk ed_ok
theorem ed_clob : ∀ r∈(Fixed.optimized E D).flatMap instrClob,r∈VG.Proof.Mont.AArch64.clob M.n := by
  rw [rightED.lit_eq]; exact clob_of_instrOk ed_ok

end VG.Proof.Weierstrass.AArch64.Forward.P256Bounds
