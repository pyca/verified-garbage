module

public import VerifiedGarbage.Proof.P256.X86_64.Ifma.Window
public import VerifiedGarbage.Proof.P256.X86_64.JointLayout
public import VerifiedGarbage.Proof.P256.X86_64.JointInitLayout
public import VerifiedGarbage.Proof.P256.X86_64.JointPrep
public import VerifiedGarbage.Proof.P256.X86_64.JointLoop
public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64

/-!
# P-256 on x86-64 with AVX512_IFMA: the joint multiplication's layout

`publicJointIfma` is `publicJointAdx` with the generator's digits elsewhere:
its layouts are those of `publicJointAdx` where they do not name the digits,
and the vectors' part of the working space is apart from the rest (`VLay`).
-/

@[expose] public section

namespace VG.Proof.P256.X86_64.Ifma

open VG VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.P256.X86_64.Ifma VG.Impl.Weierstrass
open VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.P256.X86_64

theorem joint_ifma_layout : JointLayout publicJointIfma 8192 :=
  ⟨joint_adx_layout.lay, Or.inl rfl, by decide +kernel, by decide +kernel, Or.inr rfl⟩

theorem joint_ifma_lookup_layout : JointLookupLayout publicJointIfma 8192 :=
  ⟨joint_ifma_layout, rfl, rfl, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

theorem joint_ifma_add_layout : JointAddLayout publicJointIfma 8192 :=
  ⟨joint_ifma_lookup_layout, joint_adx_add_layout.addApart, joint_adx_add_layout.cache2Apart,
    joint_adx_add_layout.cache3Apart, joint_adx_add_layout.accumNodup, joint_adx_add_layout.copyApart,
    ⟨fun _ h => by cases h⟩⟩

theorem joint_ifma_init_layout : JointInitLayout publicJointIfma 8192 :=
  ⟨joint_ifma_layout, joint_adx_naf_layout, by decide, by decide, by decide, by decide, by decide,
    by decide +kernel, by decide, by decide, fun h => absurd h (by decide)⟩

theorem joint_ifma_prep_layout : JointPrepLayout publicJointIfma 8192
    (Impl.Ecdsa.X86_64.p256x.sl Impl.Ecdsa.Verify.X86_64.U)
    (Impl.Ecdsa.X86_64.p256x.sl Impl.Ecdsa.Verify.X86_64.V) := by
  constructor <;> decide

theorem joint_ifma_double_nodup : (doubleSlots publicJointIfma.K.S publicJointIfma.K.R).Nodup :=
  joint_adx_double_nodup

/-- The vectors' slots, MXCSR saved and the blocks' constants are apart from what the joint
multiplication keeps in the working space. -/
theorem joint_ifma_vlay : VLay publicJointIfma 8192 where
  big := by decide
  mx := by decide
  pool := by decide
  live := by decide +kernel
  liveB := by decide +kernel
  mo := by decide +kernel
  stable := by decide +kernel
  stableB := by decide +kernel
  n := rfl
  tbl := by decide
  cache := by decide
  rxy := by decide
  rxz := by decide
  ryz := by decide

end VG.Proof.P256.X86_64.Ifma
