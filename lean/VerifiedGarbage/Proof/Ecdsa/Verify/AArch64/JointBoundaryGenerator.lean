import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointGeneratorFrame
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointPrefix

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass

/-- Both original table preconditions refer to the same public static table. -/
theorem jointBoundary_generators (hc : CfgOk p256) (hC : Law p256.C)
    (hT : CombOkW p256.C 7 37 p256.tbl p256.start)
    {s₀ t₀ s t : State} (ps : VPre p256 s₀) (pt : VPre p256 t₀)
    (hb : JointBoundary p256 s₀ t₀ s t) :
    JointGenerator P256Joint.cfg p256.C (s₀.gpr .x3) 8192 (G p256.C) (s₀.syms p256.tsym) s ∧
    JointGenerator P256Joint.cfg p256.C (s₀.gpr .x3) 8192 (G p256.C) (s₀.syms p256.tsym) t := by
  obtain ⟨pub,⟨gs,ms⟩,⟨gt,mt⟩,_⟩ := hb
  have bs : s₀.gpr .x3=t₀.gpr .x3 := pub.ptrs.2 .x3 (by decide)
  have ls := JointGenerator.of_pre hc hC hT ps.tbl rfl
  have rt := JointGenerator.of_pre hc hC hT pt.tbl rfl
  rw [←bs,←pub.table] at rt
  exact ⟨jointGenerator_unch ls ms.unch ms.rd ms.wr ms.syms (by simp),
    jointGenerator_unch rt mt.unch mt.rd mt.wr mt.syms (by simp)⟩

end VG.Proof.Ecdsa.Verify.AArch64
