module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
import VerifiedGarbage.Impl.Ecdh.P256.X86_64
public import VerifiedGarbage.Proof.Ecdh.X86_64.Verified
import VerifiedGarbage.Proof.Ecdh.X86_64.Lit
public import VerifiedGarbage.Proof.Ecdh.X86_64.VerifiedAdx
import VerifiedGarbage.Proof.Ecdh.X86_64.LitAdx
public import VerifiedGarbage.Proof.Ecdh.X86_64.VerifiedIfma
import VerifiedGarbage.Proof.Ecdh.X86_64.LitIfma
public import VerifiedGarbage.Impl.Ecdh.P256.X86_64.Ifma
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.EcKey.X86_64.Scrub.Out
public import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.P256
import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
public import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
public import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Pratt
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Framework.X86_64.Bswap
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.Inline
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Mont.Words128
public import VerifiedGarbage.Proof.Mont.X86_64.Blocks
public import VerifiedGarbage.Proof.Mont.X86_64.CsubS
public import VerifiedGarbage.Proof.Mont.X86_64.Friendly
public import VerifiedGarbage.Proof.Mont.X86_64.Ops
public import VerifiedGarbage.Proof.Mont.X86_64.Round
public import VerifiedGarbage.Proof.Mont.X86_64.Sparse
public import VerifiedGarbage.Proof.Mont.X86_64.SparseX
public import VerifiedGarbage.Proof.Mont.X86_64.SqrPX
public import VerifiedGarbage.Proof.Mont.X86_64.WideOps
public import VerifiedGarbage.Proof.P256.Order
public import VerifiedGarbage.Proof.P256.Prime
public import VerifiedGarbage.Proof.P256.X86_64.DoubleHalfForward
public import VerifiedGarbage.Proof.P256.X86_64.DoubleHalfPublic
public import VerifiedGarbage.Proof.P256.X86_64.DoubleHalfWP
public import VerifiedGarbage.Proof.P256.X86_64.HalfMemory
public import VerifiedGarbage.Proof.P256.X86_64.WinJac
public import VerifiedGarbage.Proof.Weierstrass.TCombWords
public import VerifiedGarbage.Proof.Weierstrass.WinJacMath
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacField
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacOps
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
public import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField
public import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardStores
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogJ
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JacAdd
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontCall
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8
public import VerifiedGarbage.Proof.Weierstrass.X86_64.SpillUnch
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJ
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJac
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacBuild
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacEntry
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacStep
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinLoop
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.P256.X86_64.Law

/-! # ECDH over P-256 (SP 800-56A) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.EcdhP256.X86_64

open VG.Proof.P256.X86_64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P256.exchangeApi.artifact X86_64.target (X86_64.Scrub.withScrubAll {
      suffix := "_ifma"
      code := Impl.Ecdh.X86_64.exchangeP256Ifma
      stack := 16
      verified := Proof.Ecdh.X86_64.ecdh_verified_ifma hasLaw.law hasLaw.inv hasLaw.prime hasLaw.killed }
    (Proof.EcKey.X86_64.Scrub.exchangeOut _ _)),
  Spec.Ecdh.P256.exchangeApi.artifact X86_64.target
    (Proof.Ecdh.X86_64.scrubReg hasLaw.law hasLaw.inv hasLaw.prime hasLaw.killed),
  Spec.Ecdh.P256.exchangeApi.artifact X86_64.target
    (Proof.Ecdh.X86_64.scrubRegAdx hasLaw.law hasLaw.inv hasLaw.prime hasLaw.killed)]

end VG.Artifacts.EcdhP256.X86_64
