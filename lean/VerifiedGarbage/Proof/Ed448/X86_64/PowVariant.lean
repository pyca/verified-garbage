module

public import VerifiedGarbage.Proof.Ed448.X86_64.FieldVariant
meta import VerifiedGarbage.Proof.Ed448.X86_64.FieldVariant
import VerifiedGarbage.Proof.X448.X86_64.Pow223Verified
meta import VerifiedGarbage.Proof.X448.X86_64.Pow223Verified
import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
meta import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Ed448.X86_64.BaseField
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.AddSmall
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Verified
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.X448.X86_64.AddSub
import VerifiedGarbage.Proof.X448.X86_64.Pow223
meta import VerifiedGarbage.Proof.Ed448.Scalar
meta import VerifiedGarbage.Proof.Ed448.X86_64.BaseField
meta import VerifiedGarbage.Proof.Ed448.X86_64.Point64.AddSmall
meta import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Verified
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Inline
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Spill
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.X448.X86_64.AddSub
meta import VerifiedGarbage.Proof.X448.X86_64.Pow223

/-! The shared Curve448 exponentiation routine for each field backend. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.FieldVariant

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64

theorem powFn_eq (v : FieldVariant) : v.powFn = Impl.X448.X86_64.pow223FnWith v.field := by
  cases v <;> rfl

theorem pow_verified (v : FieldVariant) :
    Verified X86_64.target v.powFn (Spec.X448.Field64.pow223Contract X86_64.abi) := by
  rw [powFn_eq]
  refine pow223With_verified (field_ok v) (by cases v <;> lit_decide) ?_
  cases v
  · exact pow223_ct
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp]) (fun _ _ _ _ hp => by
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.2
      · exact hp.1) (by taint_decide)

end VG.Proof.Ed448.X86_64.FieldVariant
