import VerifiedGarbage.Proof.P256.X86_64.JointLayout
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInitLayout

/-! The actual baseline and ADX table initialization layouts satisfy the nine-point bounds. -/
namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont VG.Proof.Weierstrass.X86_64

private theorem naf_lay : Lay publicJoint.K.M 8192 (·∈nafSlots publicJoint.K) := by
  have hs : ∀ x∈nafSlots publicJoint.K,x∈jointSlots publicJoint := fun _ hx =>
    List.mem_append_left _ (List.mem_append_left _ hx)
  exact ⟨fun x hx => joint_layout.lay.le x (hs x hx),
    fun x y hx hy => joint_layout.lay.apart x y (hs x hx) (hs y hy),
    fun x hx => joint_layout.lay.mo x (hs x hx),fun x hx => joint_layout.lay.tmp x (hs x hx)⟩

theorem joint_naf_layout : NafLay publicJoint.K 8192 :=
  ⟨rfl,naf_lay,by decide +kernel,by decide +kernel,by decide +kernel,by decide,
    by decide +kernel,by decide,rfl,rfl,rfl,rfl⟩

theorem joint_init_layout : JointInitLayout publicJoint 8192 :=
  ⟨joint_layout,joint_naf_layout,rfl,by decide,by decide,by decide,by decide,by decide +kernel⟩

theorem joint_adx_naf_layout : NafLay publicJointAdx.K 8192 :=
  ⟨rfl,⟨naf_lay.le,naf_lay.apart,naf_lay.mo,naf_lay.tmp⟩,
    joint_naf_layout.ro,joint_naf_layout.nodup,joint_naf_layout.tbl,joint_naf_layout.bits,
    joint_naf_layout.bits_w,joint_naf_layout.bits_tmp,rfl,rfl,rfl,rfl⟩

theorem joint_adx_init_layout : JointInitLayout publicJointAdx 8192 :=
  ⟨joint_adx_layout,joint_adx_naf_layout,rfl,by decide,by decide,by decide,by decide,
    joint_init_layout.bitsSep⟩

end VG.Proof.P256.X86_64
