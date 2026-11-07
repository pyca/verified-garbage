module

public import VerifiedGarbage.Impl.TripleDes.PPC64LE.FbFinal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesLit
import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.TripleDes.PPC64LE.FbFinal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.ModesLit
meta import VerifiedGarbage.Proof.TripleDes.PPC64LE.FunctionsLit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-! # Triple DES's final CFB functions on PPC64LE, evaluated once -/

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.PPC64LE.cfbEncryptFinal
materialize_code Impl.TripleDes.PPC64LE.cfbDecryptFinal

end VG
