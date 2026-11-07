module

public import VerifiedGarbage.Impl.Cast5.PPC64LE.FbFinal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Cast5.PPC64LE.FbFinal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesLit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-! # CAST5's final CFB functions on PPC64LE, evaluated once -/

@[expose] public section

namespace VG

materialize_code Impl.Cast5.PPC64LE.cfbEncryptFinal
materialize_code Impl.Cast5.PPC64LE.cfbDecryptFinal

end VG
