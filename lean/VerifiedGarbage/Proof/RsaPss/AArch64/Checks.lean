module

public import VerifiedGarbage.Impl.RsaPss.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Impl.RsaPss.AArch64
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# RSASSA-PSS on AArch64: the taint checks of each hash function

The piece of `ctHashWith` whose instructions depend on the hash function
beyond its sizes (its length-field code) is checked by the taint analysis
once for each shape of hash function (`by taint_decide`, in
`Proof/RsaPss/AArch64/Shapes.lean`): `PssChecks P D`, for the parameters `P`
of its streaming code and its digest size `D`. The code of a hash function
`H` is that of `ckH H.P H.D`, by definition.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Impl.Pbkdf2.AArch64 (Params)

/-- A hash function with the parameters `P` and the digest size `D`, and no
functions to call. -/
def ckH (P : Params) (D : Nat) : Hash := ⟨P, D, 0, "", .block [], "", .block [], "", .block [], "", .block [], "", "", ""⟩

/-- The taint check of the hash function's code in `ctHashWith`: its length
field from `ℓ` (secret). -/
structure PssChecks (P : Params) (D : Nat) : Prop where
  lenField : ∃ hc, (taint.check (VG.AArch64.Taint.ofRegs [.x20]) (.block (lenField (ckH P D))) hc).isSome = true

end VG.Proof.RsaPss.AArch64
