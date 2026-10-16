module

public import VerifiedGarbage.Impl.Argon2.X86_64.Derive
meta import VerifiedGarbage.Impl.Argon2.X86_64.Derive
import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressLit
meta import VerifiedGarbage.Proof.Argon2.X86_64.FillCompressLit
import VerifiedGarbage.Proof.Argon2.X86_64.FillPointersLit
meta import VerifiedGarbage.Proof.Argon2.X86_64.FillPointersLit
import VerifiedGarbage.Proof.Argon2.X86_64.AddressHeaderLit
meta import VerifiedGarbage.Proof.Argon2.X86_64.AddressHeaderLit
import VerifiedGarbage.Proof.Argon2.X86_64.ClearBlockLit
meta import VerifiedGarbage.Proof.Argon2.X86_64.ClearBlockLit
import VerifiedGarbage.Proof.Argon2.X86_64.ReduceBlockLit
meta import VerifiedGarbage.Proof.Argon2.X86_64.ReduceBlockLit
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Impl.Argon2.X86_64.ReferenceMap
meta import VerifiedGarbage.Impl.Argon2.X86_64.ReferenceMap
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

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
