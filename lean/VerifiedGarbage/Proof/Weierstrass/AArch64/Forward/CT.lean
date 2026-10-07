import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Production
import VerifiedGarbage.Proof.Framework.AArch64.Taint

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64 VG.Impl.P256.VerifyDouble

 theorem rd_ct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
    (VG.Impl.P256.VerifyDouble.double M S R D) := by
  rw [VG.Impl.P256.VerifyDouble.double,ite_eq_left (show selected M S R D from ⟨rfl,rfl,Or.inl ⟨rfl,rfl⟩⟩)]
  change ConstantTime isa _ _ (.block P256RD.optimized)
  rw [P256RD.optimized_lit]
  exact VG.Taint.constantTime (A:=taint) (hc:=.block (List.replicate 5 (Taint.ofRegs [.x0]))) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by decide +kernel)

 theorem dr_ct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
    (VG.Impl.P256.VerifyDouble.double M S D R) := by
  rw [VG.Impl.P256.VerifyDouble.double,ite_eq_left (show selected M S D R from ⟨rfl,rfl,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩)]
  change ConstantTime isa _ _ (.block P256DR.optimized)
  rw [P256DR.optimized_lit]
  exact VG.Taint.constantTime (A:=taint) (hc:=.block (List.replicate 5 (Taint.ofRegs [.x0]))) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by decide +kernel)

 theorem ed_ct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
    (VG.Impl.P256.VerifyDouble.double M S E D) := by
  rw [VG.Impl.P256.VerifyDouble.double,ite_eq_left (show selected M S E D from ⟨rfl,rfl,Or.inr (Or.inr ⟨rfl,rfl⟩)⟩)]
  change ConstantTime isa _ _ (.block P256ED.optimized)
  rw [P256ED.optimized_lit]
  exact VG.Taint.constantTime (A:=taint) (hc:=.block (List.replicate 5 (Taint.ofRegs [.x0]))) (Taint.ofRegs [.x0])
    (fun _ _ _ _ h => h) (by decide +kernel)

end VG.Proof.Weierstrass.AArch64.Forward
