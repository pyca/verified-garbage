module

public import VerifiedGarbage.Impl.Blowfish.X86.FbFinal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Blowfish.X86.FbFinal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-! # Blowfish-CFB64's and Blowfish-OFB's final functions' x86 (32-bit) code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG.Proof.Blowfish.X86

materialize_flat_code cfbEncryptFinalCode := Impl.Blowfish.X86.cfbEncryptFinal
materialize_flat_code cfbDecryptFinalCode := Impl.Blowfish.X86.cfbDecryptFinal
materialize_flat_code ofbFinalCode := Impl.Blowfish.X86.ofbFinal

end VG.Proof.Blowfish.X86
