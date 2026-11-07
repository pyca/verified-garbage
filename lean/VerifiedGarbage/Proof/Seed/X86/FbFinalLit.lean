module

public import VerifiedGarbage.Impl.Seed.X86.FbFinal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Seed.X86.FbFinal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-! # SEED-CFB128's final functions' x86 (32-bit) code as literals, for kernel-evaluated checks -/

@[expose] public section

namespace VG.Proof.Seed.X86

materialize_code cfbEncryptFinalCode := Impl.Seed.X86.cfbEncryptFinal
materialize_code cfbDecryptFinalCode := Impl.Seed.X86.cfbDecryptFinal

end VG.Proof.Seed.X86
