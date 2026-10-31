module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
import VerifiedGarbage.Impl.Ecdh.P384.X86_64
import VerifiedGarbage.Proof.Ecdh.X86_64.P384.Verified
import VerifiedGarbage.Proof.Ecdh.X86_64.P384.Lit
import VerifiedGarbage.Proof.Ecdh.X86_64.P384.VerifiedAdx
import VerifiedGarbage.Proof.Ecdh.X86_64.P384.LitAdx
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.VerifiedAdx
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdh.X86_64.P384.LitErase
public import VerifiedGarbage.Proof.Ecdh.X86_64.P384.LitEraseAdx
public import VerifiedGarbage.Spec.Ecdh.P384
public import VerifiedGarbage.Proof.Ecdh.X86_64.P384.Verified
public import VerifiedGarbage.Proof.Ecdh.X86_64.P384.VerifiedAdx
import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
public import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.P384.Point
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacField
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacOps
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
public import VerifiedGarbage.Proof.Weierstrass.X86_64.DoubleIn
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogJ
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JacAdd
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
public import VerifiedGarbage.Proof.Weierstrass.X86_64.SpillUnch
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJ
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJLoop
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJac
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacA
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacBuild
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacEntry
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacStep
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

/-! # ECDH over P-384 (SP 800-56A) on x86-64 -/

@[expose] public section

namespace VG.Generic.P384.X86_64.EcdhP384

/-- The function of `Spec.Ecdh.P384.exchangeApi`, multiplying with BMI2 and ADX
(`adx`, `_adx`) or not: its `code`, proven (`hv`), with no instruction writing
`rsp` (`hsp`). -/
def exchange (adx : Bool) (code : Prog X86_64.isa)
    (hv : Verified X86_64.target code
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P384.inst X86_64.abi 8))
    (hsp : code.all (fun i => !X86_64.isa.writesSp i) = true := by sp_safe) : Artifact :=
  Spec.Ecdh.P384.exchangeApi.artifact X86_64.target {
    suffix := (if adx then "_adx" else "")
    code
    stack := 8
    verified := hv
    spSafe := hsp
    features := if adx then ["bmi2", "adx", "avx", "avx2"] else [] }

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P384.curve) : List Artifact := [
  exchange false Impl.Ecdh.X86_64.exchangeP384
    (Proof.Ecdh.X86_64.P384.ecdh_verified h.law h.inv h.prime),
  exchange true Impl.Ecdh.X86_64.exchangeP384Adx
    (Proof.Ecdh.X86_64.P384.ecdh_verified_adx h.law h.inv h.prime)]

end VG.Generic.P384.X86_64.EcdhP384
