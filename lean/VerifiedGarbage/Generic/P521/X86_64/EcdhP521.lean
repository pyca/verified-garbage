module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
import VerifiedGarbage.Impl.Ecdh.P521.X86_64
import VerifiedGarbage.Proof.Ecdh.X86_64.P521.Verified
public import VerifiedGarbage.Proof.Ecdh.X86_64.P521.Lit
import VerifiedGarbage.Proof.Ecdh.X86_64.P521.VerifiedAdx
public import VerifiedGarbage.Proof.Ecdh.X86_64.P521.LitAdx
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.VerifiedAdx
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.P521.X86_64.TaintSumsWin
public import VerifiedGarbage.Proof.P521.X86_64.TaintSumsWinAdx
public import VerifiedGarbage.Spec.Ecdh.P521
public import VerifiedGarbage.Proof.Ecdh.X86_64.P521.Verified
public import VerifiedGarbage.Proof.Ecdh.X86_64.P521.VerifiedAdx
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
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.X86_64.MulJ4
import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Verified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.P521.Point
import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogJ
import VerifiedGarbage.Proof.Weierstrass.X86_64.SpillUnch
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJ
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJLoop

/-! # ECDH over P-521 (SP 800-56A) on x86-64 -/

@[expose] public section

namespace VG.Generic.P521.X86_64.EcdhP521

/-- The function of `Spec.Ecdh.P521.exchangeApi`, multiplying modulo `p` with
BMI2 and ADX (`adx`, `_adx`) or not: its `code`, proven (`hv`), with no
instruction writing `rsp` (`hsp`). -/
def exchange (adx : Bool) (code : Prog X86_64.isa)
    (hv : Verified X86_64.target code
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst X86_64.abi 8))
    (hsp : code.all (fun i => !X86_64.isa.writesSp i) = true := by sp_safe) : Artifact :=
  Spec.Ecdh.P521.exchangeApi.artifact X86_64.target {
    suffix := (if adx then "_adx" else "")
    code
    stack := 8
    verified := hv
    spSafe := hsp
    features := if adx then ["bmi2", "adx"] else [] }

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInvOrd Spec.P521.curve) : List Artifact := [
  exchange false Impl.Ecdh.X86_64.exchangeP521
    (Proof.Ecdh.X86_64.P521.ecdh_verified h.law h.inv h.prime),
  exchange true Impl.Ecdh.X86_64.exchangeP521Adx
    (Proof.Ecdh.X86_64.P521.ecdh_verified_adx h.law h.inv h.prime)]

end VG.Generic.P521.X86_64.EcdhP521
