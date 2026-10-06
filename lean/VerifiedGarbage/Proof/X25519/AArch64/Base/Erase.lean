import VerifiedGarbage.Proof.Ed25519.AArch64.CombErase
import VerifiedGarbage.Impl.X25519.AArch64.Base

/-!
# X25519 of the base point on AArch64: the code without its immediates

Untrusted: everything here is checked by Lean. As for Ed25519's `scalarBase`
(`Proof/Ed25519/AArch64/CombErase.lean`): without the immediates of `movz` and
`movk`, the comb's 32 selections are table 0's (`engine_eraseImm`), so the
kernel builds and checks one selection, and no table's immediates, in the
constant-time analysis of `engine0` and the `keepsV` check of `x25519Base0`,
the code's only evaluations; the code has no literal.
-/

namespace VG.Proof.X25519.AArch64.Base

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.X25519.AArch64.Base
open VG.Proof.Ed25519.AArch64 (combMultiply0 combMultiply_eraseImm)

/-- `engine`, with every table's selection table 0's. -/
def engine0 : Prog isa :=
  .seq scalarBasePrepare (.seq (.block clampBits) (.seq combMultiply0 uEncode))

/-- `x25519Base`, with every table's selection table 0's. -/
def x25519Base0 : Prog isa :=
  .seq (.block (scalarSave ++ scalarBaseSetup)) (.seq engine0 scalarBaseFinish)

theorem engine_eraseImm : Code.eraseImm engine = Code.eraseImm engine0 := by
  simp only [engine, engine0, Code.eraseImm, combMultiply_eraseImm]

theorem x25519Base_eraseImm : Code.eraseImm x25519Base = Code.eraseImm x25519Base0 := by
  simp only [x25519Base, x25519Base0, Code.eraseImm, engine_eraseImm]

end VG.Proof.X25519.AArch64.Base
