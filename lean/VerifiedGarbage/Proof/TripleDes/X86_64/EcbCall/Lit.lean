module

public import VerifiedGarbage.Impl.TripleDes.X86_64.EcbCall
meta import VerifiedGarbage.Impl.TripleDes.X86_64.EcbCall
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Lit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Lit
public import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Lit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedSse.Lit
import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.SboxLit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx2.SboxLit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

/-! # The ECB functions' code around the call of the core, as literals -/

@[expose] public section

namespace VG

materialize_code Impl.TripleDes.X86_64.EcbCall.sseEncrypt
materialize_code Impl.TripleDes.X86_64.EcbCall.sseDecrypt
materialize_code Impl.TripleDes.X86_64.EcbCall.avx2Encrypt
materialize_code Impl.TripleDes.X86_64.EcbCall.avx2Decrypt
materialize_code Impl.TripleDes.X86_64.EcbCall.avx512Encrypt
materialize_code Impl.TripleDes.X86_64.EcbCall.avx512Decrypt

end VG
