module

public import VerifiedGarbage.Impl.Argon2.PPC64LE.Compress
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Argon2.PPC64LE.Compress
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-! # Argon2 compression on PPC64LE as a checked instruction literal -/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE

materialize_code compress := Impl.Argon2.PPC64LE.compress

end VG.Proof.Argon2.PPC64LE
