import VerifiedGarbage.Impl.Ecdsa.Verify.P521.X86_64
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInitLayout
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointPrepFields

/-! Concrete separation checks for P-521's joint verifier's scratch allocation. -/
namespace VG.Proof.P521.X86_64
open VG VG.X86_64 VG.Impl.P521.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Weierstrass.X86_64

private theorem joint_lay : Lay publicJoint.K.M 8192 (·∈jointSlots publicJoint) := by
  refine ⟨by decide +kernel,?_,by decide +kernel,by decide +kernel⟩
  have h : ∀ x∈jointSlots publicJoint,∀ y∈jointSlots publicJoint,x≠y →
      x+8*publicJoint.K.M.n≤y ∨ y+8*publicJoint.K.M.n≤x := by decide +kernel
  exact fun x y hx hy => h x hx y hy

theorem joint_layout : JointLayout publicJoint 8192 :=
  ⟨joint_lay,Or.inr (Or.inr rfl),by decide +kernel,by decide +kernel⟩

theorem joint_lookup_layout : JointLookupLayout publicJoint 8192 :=
  ⟨joint_layout,rfl,rfl,by decide,by decide,by decide,by decide,by decide,by decide,
    by decide,by decide,by decide,by decide⟩

theorem joint_add_layout : JointAddLayout publicJoint 8192 := by
  refine ⟨joint_lookup_layout,?_,by decide,by decide,by decide,by decide⟩
  constructor <;> decide +kernel

theorem joint_adx_layout : JointLayout publicJointAdx 8192 :=
  ⟨⟨joint_lay.le,joint_lay.apart,joint_lay.mo,joint_lay.tmp⟩,Or.inr (Or.inr rfl),
    joint_layout.stableBounds,joint_layout.stableSep⟩

theorem joint_adx_lookup_layout : JointLookupLayout publicJointAdx 8192 :=
  ⟨joint_adx_layout,rfl,rfl,by decide,by decide,by decide,by decide,by decide,by decide,
    by decide,by decide,by decide,by decide⟩

theorem joint_adx_add_layout : JointAddLayout publicJointAdx 8192 :=
  ⟨joint_adx_lookup_layout,joint_add_layout.addApart,joint_add_layout.cache2Apart,
    joint_add_layout.cache3Apart,joint_add_layout.accumNodup,joint_add_layout.copyApart⟩

private theorem naf_lay : Lay publicJoint.K.M 8192 (·∈nafSlots publicJoint.K) := by
  have hs : ∀ x∈nafSlots publicJoint.K,x∈jointSlots publicJoint := fun _ hx =>
    List.mem_append_left _ (List.mem_append_left _ hx)
  exact ⟨fun x hx => joint_layout.lay.le x (hs x hx),
    fun x y hx hy => joint_layout.lay.apart x y (hs x hx) (hs y hy),
    fun x hx => joint_layout.lay.mo x (hs x hx),fun x hx => joint_layout.lay.tmp x (hs x hx)⟩

theorem joint_naf_layout : NafLay publicJoint.K 8192 :=
  ⟨Or.inr (Or.inr rfl),naf_lay,by decide +kernel,by decide +kernel,by decide +kernel,by decide,
    by decide +kernel,by decide,rfl,rfl,rfl,rfl⟩

theorem joint_init_layout : JointInitLayout publicJoint 8192 :=
  ⟨joint_layout,joint_naf_layout,by decide,by decide,by decide,by decide,by decide,by decide +kernel⟩

theorem joint_adx_naf_layout : NafLay publicJointAdx.K 8192 :=
  ⟨Or.inr (Or.inr rfl),⟨naf_lay.le,naf_lay.apart,naf_lay.mo,naf_lay.tmp⟩,
    joint_naf_layout.ro,joint_naf_layout.nodup,joint_naf_layout.tbl,joint_naf_layout.bits,
    joint_naf_layout.bits_w,joint_naf_layout.bits_tmp,rfl,rfl,rfl,rfl⟩

theorem joint_adx_init_layout : JointInitLayout publicJointAdx 8192 :=
  ⟨joint_adx_layout,joint_adx_naf_layout,by decide,by decide,by decide,by decide,by decide,
    joint_init_layout.bitsSep⟩

theorem joint_prep_layout : JointPrepLayout publicJoint 8192
    (p521.sl Impl.Ecdsa.Verify.X86_64.U)
    (p521.sl Impl.Ecdsa.Verify.X86_64.V) := by
  constructor <;> decide

theorem joint_adx_prep_layout : JointPrepLayout publicJointAdx 8192
    (p521x.sl Impl.Ecdsa.Verify.X86_64.U)
    (p521x.sl Impl.Ecdsa.Verify.X86_64.V) := by
  constructor <;> decide

end VG.Proof.P521.X86_64
