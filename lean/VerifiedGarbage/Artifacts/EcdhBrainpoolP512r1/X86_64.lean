module
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP512r1
import VerifiedGarbage.Proof.Ecdh.X86_64.BrainpoolP512r1.Lit
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
import VerifiedGarbage.Proof.Ecdh.X86_64.BrainpoolP512r1.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Bswap
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Mont.Words128
import VerifiedGarbage.Proof.Mont.X86_64.Blocks
import VerifiedGarbage.Proof.Mont.X86_64.CsubS
import VerifiedGarbage.Proof.Mont.X86_64.Friendly
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Proof.Mont.X86_64.Round
import VerifiedGarbage.Proof.Mont.X86_64.Sparse
import VerifiedGarbage.Proof.Mont.X86_64.SparseX
import VerifiedGarbage.Proof.Mont.X86_64.SqrPX
import VerifiedGarbage.Proof.Mont.X86_64.WideOps
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontCall
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8
import VerifiedGarbage.Proof.Weierstrass.X86_64.SpillUnch
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinLoop
import VerifiedGarbage.Proof.BrainpoolP512r1.X86_64.Law
import VerifiedGarbage.Proof.Framework.SpecApis


/-! # ECDH over brainpoolP512r1 (SP 800-56A) on x86-64 -/

namespace VG.Artifacts.EcdhBrainpoolP512r1.X86_64

open VG.Proof.BrainpoolP512r1.X86_64 (hasLaw)

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Ecdh.BrainpoolP512r1.exchangeApi.artifact X86_64.target
    { code := Impl.Ecdh.X86_64.Fn.exchangeBrainpoolP512r1
      verified := Proof.Ecdh.X86_64.BrainpoolP512r1.exchange_scrubbed hasLaw.law hasLaw.inv
      spSafe := Proof.Ecdh.X86_64.BrainpoolP512r1.exchange_spSafe }]

spec_apis artifacts

end VG.Artifacts.EcdhBrainpoolP512r1.X86_64
