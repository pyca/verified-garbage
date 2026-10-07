import VerifiedGarbage.Impl.P256.X86_64.Joint
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigit

/-! Concrete separation checks for the measured joint verifier's scratch allocation. -/
namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont VG.Proof.Weierstrass.X86_64

private theorem joint_lay : Lay publicJoint.K.M 8192 (·∈jointSlots publicJoint) := by
  refine ⟨by decide +kernel,?_,by decide +kernel,by decide +kernel⟩
  have h : ∀ x∈jointSlots publicJoint,∀ y∈jointSlots publicJoint,x≠y →
      x+8*publicJoint.K.M.n≤y ∨ y+8*publicJoint.K.M.n≤x := by decide +kernel
  exact fun x y hx hy => h x hx y hy

theorem joint_layout : JointLayout publicJoint 8192 :=
  ⟨joint_lay,rfl,by decide +kernel,by decide +kernel⟩

theorem joint_lookup_layout : JointLookupLayout publicJoint 8192 :=
  ⟨joint_layout,rfl,rfl,by decide,by decide,by decide,by decide,by decide,by decide,
    by decide,by decide,by decide,by decide⟩

theorem joint_add_layout : JointAddLayout publicJoint 8192 := by
  refine ⟨joint_lookup_layout,?_,by decide,by decide,by decide,by decide⟩
  constructor <;> decide +kernel

theorem joint_adx_layout : JointLayout publicJointAdx 8192 :=
  ⟨⟨joint_lay.le,joint_lay.apart,joint_lay.mo,joint_lay.tmp⟩,rfl,
    joint_layout.stableBounds,joint_layout.stableSep⟩

theorem joint_adx_lookup_layout : JointLookupLayout publicJointAdx 8192 :=
  ⟨joint_adx_layout,rfl,rfl,by decide,by decide,by decide,by decide,by decide,by decide,
    by decide,by decide,by decide,by decide⟩

theorem joint_adx_add_layout : JointAddLayout publicJointAdx 8192 :=
  ⟨joint_adx_lookup_layout,joint_add_layout.addApart,joint_add_layout.cache2Apart,
    joint_add_layout.cache3Apart,joint_add_layout.accumNodup,joint_add_layout.copyApart⟩

end VG.Proof.P256.X86_64
