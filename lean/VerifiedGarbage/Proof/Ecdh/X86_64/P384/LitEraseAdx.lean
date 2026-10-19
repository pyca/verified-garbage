module

public import VerifiedGarbage.Proof.Ecdh.X86_64.P384.LitAdx
meta import VerifiedGarbage.Proof.Ecdh.X86_64.P384.LitAdx
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.Inline
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-!
# ECDH over P-384 on x86-64 with BMI2 and ADX: the code without its displacements, as a literal

As `LitErase.lean`, for the code that multiplies modulo `p` with BMI2 and ADX.
-/

@[expose] public section

namespace VG.Proof.Ecdh.X86_64.P384

/-- The code without its displacements. -/
def exchangeErasedAdx : Prog VG.X86_64.isa := VG.X86_64.Code.erase Impl.Ecdh.X86_64.exchangeP384Adx

materialize_shared exchangeErasedAdx

end VG.Proof.Ecdh.X86_64.P384
