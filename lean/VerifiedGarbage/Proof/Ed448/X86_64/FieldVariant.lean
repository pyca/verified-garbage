module

public import VerifiedGarbage.Impl.Ed448.X86_64.FieldVariant
public import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Fn
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.X448.X86_64.Adx.Sqr
import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.AddSmall
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Lit
import VerifiedGarbage.Proof.X448.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Ed448.X86_64.FieldVariant
meta import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Fn
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.X448.X86_64.Adx.Sqr
meta import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
meta import VerifiedGarbage.Proof.Ed448.X86_64.Point64.AddSmall
meta import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Lit
meta import VerifiedGarbage.Proof.X448.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Spec.X448
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.X448
meta import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Ed448
meta import VerifiedGarbage.Spec.Ed448

/-! The field backends implement the same point programs and public contracts. -/

@[expose] public section

namespace VG

materialize_code Impl.Ed448.X86_64.Point64.doubleAdxFn
materialize_code Impl.Ed448.X86_64.Point64.addAdxFn

end VG

namespace VG.Proof.Ed448.X86_64.FieldVariant

open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64
open VG.Proof.Ed448 VG.Proof.Ed448.X86_64.Point64
open VG.Impl.Ed448.X86_64.Point64 (saves restores)

theorem field_ok (v : Impl.Ed448.X86_64.FieldVariant) : Proof.X448.X86_64.FieldOk v.field := by
  cases v
  · exact Proof.X448.X86_64.baseline_ok
  · exact Proof.X448.X86_64.adx_ok

theorem doubleFn_eq (v : Impl.Ed448.X86_64.FieldVariant) :
    v.doubleFn = Point64.doubleFnWith v.field := by cases v <;> rfl

theorem addFn_eq (v : Impl.Ed448.X86_64.FieldVariant) :
    v.addFn = Point64.addFnWith v.field := by cases v <;> rfl

theorem bodies_ok (v : Impl.Ed448.X86_64.FieldVariant) : Point64.PointOk v.bodies where
  dbl hs := by
    change WP isa v.doubleFn _ _
    rw [doubleFn_eq]
    exact WP.mono (fnWith_ok (field_ok v) doubleOps doubleOps_valid hs) (fun _ ⟨k, e, _⟩ => ⟨k, e⟩)
  add hs hd := by
    change WP isa v.addFn _ _
    rw [addFn_eq]
    exact WP.mono (addFnWith_ok (field_ok v) hs hd) (fun _ ⟨k, e, _⟩ => ⟨k, e⟩)

end VG.Proof.Ed448.X86_64.FieldVariant
