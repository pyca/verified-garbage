module

public import VerifiedGarbage.Impl.Cast5.X86.FbFinal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Cast5.X86.FbFinal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-! # CAST5-CFB64's and CAST5-OFB's final functions' x86 (32-bit) code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG.Proof.Cast5.X86

materialize_flat_code cfbEncryptFinalCode := Impl.Cast5.X86.Modes.cfbEncryptFinal
materialize_flat_code cfbDecryptFinalCode := Impl.Cast5.X86.Modes.cfbDecryptFinal
materialize_flat_code ofbFinalCode := Impl.Cast5.X86.Modes.ofbFinal

end VG.Proof.Cast5.X86
