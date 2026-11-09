module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvInterface
public import VerifiedGarbage.Proof.P521.Comb7
import VerifiedGarbage.Impl.EcKey.P521.X86_64
import VerifiedGarbage.Proof.EcKey.X86_64.P521.Verified
public import VerifiedGarbage.Proof.EcKey.X86_64.P521.Lit
public import VerifiedGarbage.Proof.EcKey.X86_64.P521.VerifiedAdx
public import VerifiedGarbage.Proof.EcKey.X86_64.P521.LitAdx
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.VerifiedAdx
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
public import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Weierstrass.X86_64.FieldErase
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
public import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
public import VerifiedGarbage.Proof.EcKey.PublicKey
public import VerifiedGarbage.Proof.Ecdsa.Sign
public import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Main
public import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P521.Verified
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
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
public import VerifiedGarbage.Proof.P521.Point
public import VerifiedGarbage.Proof.Weierstrass.CombCheckFast
public import VerifiedGarbage.Proof.Weierstrass.TCombWords
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogJ
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontCall
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJ
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJDigit
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.P521.X86_64.Law

/-! # P-521 public keys (FIPS 186-5 §A.2) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.EcP521.X86_64

open VG.Proof.P521.X86_64 (hasLaw)

/-- The function of `Spec.EcKey.P521.publicKeyApi`, multiplying modulo `p` with
BMI2 and ADX and selecting the comb's entries with AVX2 (`adx`, `_adx`) or not: its `code`, proven (`hv`), with no
instruction writing `rsp` (`hsp`). -/
def publicKey (adx : Bool) (code : Prog X86_64.isa)
    (hv : Verified X86_64.target code
      (Spec.EcKey.P521.inst.publicKeyContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p521.combConsts) 8))
    (hsp : code.all (fun i => !X86_64.isa.writesSp i) = true := by sp_safe) : Artifact :=
  Spec.EcKey.P521.publicKeyApi.artifact X86_64.target {
    suffix := (if adx then "_adx" else "")
    code
    stack := 8
    verified := hv
    spSafe := hsp
    features := if adx then ["bmi2", "adx", "avx", "avx2"] else [] }

def artifacts : List Artifact := [
  publicKey false Impl.EcKey.X86_64.publicKeyP521
    (Proof.EcKey.X86_64.P521.pk_verified hasLaw.law (Proof.P521.combOk7 hasLaw.law) hasLaw.inv),
  publicKey true Impl.EcKey.X86_64.publicKeyP521Adx
    (Proof.EcKey.X86_64.P521.pk_verified_adx hasLaw.law (Proof.P521.combOk7 hasLaw.law) hasLaw.inv)]

end VG.Artifacts.EcP521.X86_64
