module

import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.PPC64LE
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
meta import VerifiedGarbage.Impl.CmacTripleDes.Stream.PPC64LE
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-! # Streaming TDEA-CMAC on PPC64LE, evaluated once -/

@[expose] public section

namespace VG

materialize_code Impl.CmacTripleDes.Stream.PPC64LE.streamInit
materialize_code Impl.CmacTripleDes.Stream.PPC64LE.absorb
materialize_code Impl.CmacTripleDes.Stream.PPC64LE.finish

end VG
