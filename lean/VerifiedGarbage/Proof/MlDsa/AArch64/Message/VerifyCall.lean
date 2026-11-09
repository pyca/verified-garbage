module
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCall

/-!
# ML-DSA on AArch64, `verify_message_cached`: the verification function on `μ`

Untrusted: everything here is checked by Lean. The arguments of the cached
message verifier's call of the verification function on `μ`: `pk`, `μ` at
`X + 840`, `sig` and `scratch` (`verifyArgs`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa

/-- The arguments of the call of the verification function on `μ`. -/
abbrev verifyArgs : List (Reg × Arg) := [(.x0, .slot fKey), (.x1, .off oMU), (.x2, .slot fSig), (.x3, .slot fScr)]

end VG.Proof.MlDsa.AArch64.Message
