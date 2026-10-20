module

public import VerifiedGarbage.Impl.Ed448.X86_64.FieldVariant
public import VerifiedGarbage.Proof.X448.X86_64.Adx.Verified
import VerifiedGarbage.Proof.X448.X86_64.Verified

/-!
# X448 on x86-64, with each Curve448 field backend

`vg_x448`'s code and its proof for each backend of the field
(`FieldVariant`), which `Generic/Curve448Field/X86_64/X448.lean` registers.
-/

@[expose] public section

namespace VG.Proof.X448.X86_64

/-- `vg_x448`'s code with the field backend `v`. -/
def code : Impl.Ed448.X86_64.FieldVariant → Prog X86_64.isa
  | .scalar => Impl.X448.X86_64.x448
  | .adx => Impl.X448.X86_64.x448Adx

theorem code_verified (v : Impl.Ed448.X86_64.FieldVariant) :
    Verified X86_64.target (code v) (Spec.X448.x448Contract X86_64.abi 8) := by
  cases v
  · exact x448_verified
  · exact x448Adx_verified

end VG.Proof.X448.X86_64
