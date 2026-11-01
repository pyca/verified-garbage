module

public import VerifiedGarbage.Proof.X448.Field64Contract
import VerifiedGarbage.Proof.X448.X86_64.Pow223Verified
import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
import VerifiedGarbage.Proof.Ed448.X86_64.FieldVariant
public import VerifiedGarbage.Impl.Ed448.X86_64.FieldVariant
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X448.X86_64.Lit
meta import VerifiedGarbage.Proof.X448.X86_64.Pow223Verified
meta import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
meta import VerifiedGarbage.Proof.Ed448.X86_64.FieldVariant
meta import VerifiedGarbage.Impl.Ed448.X86_64.FieldVariant
meta import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X448.X86_64.Lit

/-! The shared Curve448 exponentiation routine for each field backend. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.FieldVariant

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64

theorem powFn_eq (v : FieldVariant) : v.powFn = Impl.X448.X86_64.pow223FnWith v.field := by
  cases v <;> rfl

theorem pow_verified (v : FieldVariant) :
    Verified X86_64.target v.powFn (Proof.X448.Field64.pow223Contract X86_64.abi) := by
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
