module

public import VerifiedGarbage.Impl.Argon2.X86_64.Derive
import VerifiedGarbage.Proof.Argon2.X86_64.ClearBlockLit
import VerifiedGarbage.Proof.Argon2.X86_64.ReduceBlockLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Argon2.X86_64.AddressHeaderLit
import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressLit
import VerifiedGarbage.Proof.Argon2.X86_64.FillPointersLit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Argon2.X86_64.Derive
meta import VerifiedGarbage.Proof.Argon2.X86_64.ClearBlockLit
meta import VerifiedGarbage.Proof.Argon2.X86_64.ReduceBlockLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Argon2.X86_64.AddressHeaderLit
meta import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressLit
meta import VerifiedGarbage.Proof.Argon2.X86_64.FillPointersLit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! Merged from `Proof.Argon2.X86_64.ReferenceMapLit`. -/

@[expose] public section

section
/-! A checked literal for complete reference-index mapping. -/

namespace VG

materialize_code Impl.Argon2.X86_64.ReferenceMap.code

end VG
end

/-! Checked literals for the entry point's fixed instruction shapes. -/

namespace VG

materialize_code Impl.Argon2.X86_64.Derive.prepare
materialize_code Impl.Argon2.X86_64.FillSetup.code
materialize_code Impl.Argon2.X86_64.FinalReduction.code

end VG
