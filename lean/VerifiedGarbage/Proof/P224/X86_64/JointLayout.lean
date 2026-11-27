module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInitLayout
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointPrepFields
public import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64
public import VerifiedGarbage.Impl.P224.X86_64.Joint
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Framework.Apart

/-! Concrete separation checks for P-224's joint verifier's scratch allocation. -/

@[expose] public section

namespace VG.Proof.P224.X86_64
open VG VG.X86_64 VG.Impl.P224.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont VG.Proof.Weierstrass.X86_64

private theorem joint_lay : Lay publicJointF.K.M 8192 (·∈jointSlots publicJointF) := by
  refine ⟨by decide +kernel,?_,by decide +kernel,by decide +kernel⟩
  have h : ∀ x∈jointSlots publicJointF,∀ y∈jointSlots publicJointF,x≠y →
      x+8*publicJointF.K.M.n≤y ∨ y+8*publicJointF.K.M.n≤x := apart_of (by decide +kernel)
  exact fun x y hx hy => h x hx y hy

theorem joint_layout : JointLayout publicJointF 8192 :=
  ⟨joint_lay,Or.inl rfl,by decide +kernel,by decide +kernel,Or.inl rfl⟩

theorem joint_lookup_layout : JointLookupLayout publicJointF 8192 :=
  ⟨joint_layout,rfl,rfl,by decide,by decide,by decide,by decide,by decide,by decide,
    by decide,by decide,by decide,by decide⟩

theorem joint_add_layout : JointAddLayout publicJointF 8192 := by
  refine ⟨joint_lookup_layout,?_,by decide,by decide,by decide,by decide,
    ⟨fun _ _ => ⟨by decide +kernel,by decide +kernel,by decide⟩, fun _ _ => rfl⟩⟩
  constructor <;> decide +kernel

private theorem naf_lay : Lay publicJointF.K.M 8192 (·∈nafSlots publicJointF.K) := by
  have hs : ∀ x∈nafSlots publicJointF.K,x∈jointSlots publicJointF := fun _ hx =>
    List.mem_append_left _ (List.mem_append_left _ hx)
  exact ⟨fun x hx => joint_layout.lay.le x (hs x hx),
    fun x y hx hy => joint_layout.lay.apart x y (hs x hx) (hs y hy),
    fun x hx => joint_layout.lay.mo x (hs x hx),fun x hx => joint_layout.lay.tmp x (hs x hx)⟩

theorem joint_naf_layout : NafLay publicJointF.K 8192 :=
  ⟨Or.inl rfl,naf_lay,by decide +kernel,by decide +kernel,by decide +kernel,by decide,
    by decide +kernel,by decide,rfl,rfl,rfl,rfl⟩

theorem joint_prep_layout : JointPrepLayout publicJointF 8192
    (p224v.sl Impl.Ecdsa.Verify.X86_64.U)
    (p224v.sl Impl.Ecdsa.Verify.X86_64.V) := by
  constructor <;> decide

end VG.Proof.P224.X86_64
