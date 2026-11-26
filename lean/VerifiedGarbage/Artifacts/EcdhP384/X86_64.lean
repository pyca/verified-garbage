module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.P384
import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
import VerifiedGarbage.Impl.Ecdh.P384.X86_64
import VerifiedGarbage.Proof.Ecdh.X86_64.P384.Verified
import VerifiedGarbage.Proof.Ecdh.X86_64.P384.Lit
import VerifiedGarbage.Proof.Ecdh.X86_64.P384.VerifiedAdx
import VerifiedGarbage.Proof.Ecdh.X86_64.P384.LitAdx
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.VerifiedAdx
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdh.X86_64.P384.LitErase
import VerifiedGarbage.Proof.Ecdh.X86_64.P384.LitEraseAdx
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Verified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.P384.Point
import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacField
import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacOps
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Weierstrass.X86_64.DoubleIn
import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogJ
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacAdd
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
import VerifiedGarbage.Proof.Weierstrass.X86_64.SpillUnch
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJ
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJLoop
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJac
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacBuild
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacEntry
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacStep
import VerifiedGarbage.Proof.P384.X86_64.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over P-384 (SP 800-56A) on x86-64 -/

namespace VG.Artifacts.EcdhP384.X86_64

open VG.Proof.P384.X86_64 (hasLaw)

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Ecdh.P384.exchangeApi.artifact X86_64.target
    { code := Impl.Ecdh.X86_64.Fn.exchangeP384
      verified := Proof.Ecdh.X86_64.P384.exchange_scrubbed hasLaw.law hasLaw.inv hasLaw.prime
      spSafe := Proof.Ecdh.X86_64.P384.exchange_spSafe },
  Spec.Ecdh.P384.exchangeApi.artifact X86_64.target
    { suffix := "_adx"
      code := Impl.Ecdh.X86_64.Fn.exchangeP384Adx
      verified := Proof.Ecdh.X86_64.P384.exchangeAdx_scrubbed hasLaw.law hasLaw.inv hasLaw.prime
      spSafe := Proof.Ecdh.X86_64.P384.exchangeAdx_spSafe }]

spec_apis artifacts

end VG.Artifacts.EcdhP384.X86_64
