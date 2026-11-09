module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
import VerifiedGarbage.Impl.Ecdh.P521.X86_64
public import VerifiedGarbage.Proof.Ecdh.X86_64.P521.Verified
public import VerifiedGarbage.Proof.Ecdh.X86_64.P521.Lit
public import VerifiedGarbage.Proof.Ecdh.X86_64.P521.VerifiedAdx
public import VerifiedGarbage.Proof.Ecdh.X86_64.P521.LitAdx
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.VerifiedAdx
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.P521.X86_64.TaintSumsWin
public import VerifiedGarbage.Proof.P521.X86_64.TaintSumsWinAdx
public import VerifiedGarbage.Spec.Ecdh.P521
import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.X86_64.MulJ4
public import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
public import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.P521.Point
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogJ
public import VerifiedGarbage.Proof.Weierstrass.X86_64.SpillUnch
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJ
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJLoop
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.P521.X86_64.Law

/-! # ECDH over P-521 (SP 800-56A) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.EcdhP521.X86_64

open VG.Proof.P521.X86_64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P521.exchangeApi.artifact X86_64.target {
    code := Impl.Ecdh.X86_64.exchangeP521
    stack := 8
    verified := Proof.Ecdh.X86_64.P521.ecdh_verified hasLaw.law hasLaw.inv hasLaw.prime },
  Spec.Ecdh.P521.exchangeApi.artifact X86_64.target {
    suffix := "_adx"
    code := Impl.Ecdh.X86_64.exchangeP521Adx
    stack := 8
    verified := Proof.Ecdh.X86_64.P521.ecdh_verified_adx hasLaw.law hasLaw.inv hasLaw.prime }]

end VG.Artifacts.EcdhP521.X86_64
