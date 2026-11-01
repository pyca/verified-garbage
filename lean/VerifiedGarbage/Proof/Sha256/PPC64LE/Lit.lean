module

public import VerifiedGarbage.Impl.Sha256.PPC64LE
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sha256.PPC64LE
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-! # SHA-256 on PPC64LE: code and constants as literals -/

@[expose] public section

namespace VG.Impl.Sha256.PPC64LE

materialize_value kWords
materialize_code computedChunk
materialize_code roundsLoop
materialize_code compressCore
materialize_code compress

end VG.Impl.Sha256.PPC64LE
