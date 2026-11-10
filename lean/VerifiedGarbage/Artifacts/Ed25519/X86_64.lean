module

public import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Sound
public import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Verified
public import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyMessage.Verified
public import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Expanded
public import VerifiedGarbage.Proof.Ed25519.X86_64.KeyPair
public import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyMessage.EqCodes
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyLit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.Sha512Compress.X86_64

/-! # Ed25519 (RFC 8032) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Ed25519.X86_64

/-- Verification with the SHA-512 implementation `c`, the field multiplications
`fld` and the windows `win`, those of `vg_ed25519_verify_equation` with the
suffix `fs`. -/
def verifyWith (c : Proof.Sha512.X86_64.Compress) (fld : Impl.Ed25519.X86_64.Arith)
    [Proof.Ed25519.X86_64.EdArith fld] (win : Prog X86_64.isa)
    (fs : String)
    (hq : Proof.Ed25519.X86_64.VerifyMessage.EqCode fld win) :
    Artifact :=
  Spec.Ed25519.verifyApi.artifact X86_64.target {
    suffix := c.suffix ++ fs
    code := Impl.Ed25519.X86_64.VerifyMessage.code fld win fs c.callee c.suffix
    stack := 184
    verified := Proof.Ed25519.X86_64.VerifyMessage.verified hq c
    spSafe := Proof.Ed25519.X86_64.VerifyMessage.spSafe hq c }

/-- Signing with the seed's cached SHA-512 digest and public key, with the SHA-512
implementation `c`, calling the base-point multiplication `bs` (`vg_ed25519_scalar_base` with
the suffix `fs`). -/
def signExpandedWith (c : Proof.Sha512.X86_64.Compress) (bs : Prog X86_64.isa)
    [Proof.Ed25519.X86_64.EdBase bs] (fs : String) : Artifact :=
  Spec.Ed25519.signExpandedApi.artifact X86_64.target {
    suffix := c.suffix ++ fs
    code := Impl.Ed25519.X86_64.SignCached.codeExpanded bs fs c.callee c.suffix
    stack := 264
    verified := Proof.Ed25519.X86_64.SignCached.verifiedE c
    spSafe := Proof.Ed25519.X86_64.SignCached.spSafeE c }

/-- Key-pair derivation with the SHA-512 implementation `c`'s one-shot digest, whose code
it calls as the internal `vg_sha512_digest<suffix>_core` (the exported digest also clears
what it leaves), calling `vg_ed25519_public_key_expanded` with the suffix `fs`, whose
base-point multiplication is `bs`. -/
def keyPairWith (c : Proof.Sha512.X86_64.Compress) (bs : Prog X86_64.isa)
    [Proof.Ed25519.X86_64.EdBase bs] (fs : String) : Artifact :=
  Spec.Ed25519.keyPairApi.artifact X86_64.target {
    suffix := c.suffix ++ fs
    code := Impl.Ed25519.X86_64.KeyPair.keyPair (Spec.Sha512.digest512Api.name ++ c.suffix ++ "_core")
      (Proof.Ed25519.X86_64.KeyPair.dgCode c) ("vg_ed25519_public_key_expanded" ++ fs)
      (Impl.Ed25519.X86_64.publicKeyExpanded bs fs)
    stack := 1632
    verified := Proof.Ed25519.X86_64.KeyPair.verified c bs fs
    spSafe := Proof.Ed25519.X86_64.KeyPair.spSafe c bs fs }

/-- Verification and signing with the SHA-512 implementation `c` and the field
multiplications `fld` (verification's doublings too), those of the Ed25519
functions with the suffix `fs`; signing calls the base-point multiplication
`bs`. -/
def withField (c : Proof.Sha512.X86_64.Compress) (fld : Impl.Ed25519.X86_64.Arith)
    [Proof.Ed25519.X86_64.EdArith fld] (fs : String)
    (bs : Prog X86_64.isa) [Proof.Ed25519.X86_64.EdBase bs]
    (hq : Proof.Ed25519.X86_64.VerifyMessage.EqCode fld (Impl.Ed25519.X86_64.windows fld)) :
    List Artifact :=
  [verifyWith c fld (Impl.Ed25519.X86_64.windows fld) fs hq,
    signExpandedWith c bs fs, keyPairWith c bs fs]

/-- Each operation with the SHA-512 implementation of `v`, if it has one, and
each field multiplication of the Ed25519 functions, best first: with
AVX512_IFMA (`_ifma`), verification with its windows, and signing with its
comb; BMI2's and ADX's (`_adx`, whose comb also selects its entries with
AVX2); and the baseline's. -/
def artifactsFor (c : Proof.Sha512.X86_64.Compress) : List Artifact :=
  [verifyWith c Impl.X25519.X86_64.adx
        Impl.Ed25519.X86_64.Ifma.windows "_ifma" Proof.Ed25519.X86_64.VerifyCode.ifma_eq,
        signExpandedWith c Impl.Ed25519.X86_64.scalarBase_ifma "_ifma",
        keyPairWith c Impl.Ed25519.X86_64.scalarBase_ifma "_ifma"] ++
      withField c Impl.X25519.X86_64.adx "_adx" Impl.Ed25519.X86_64.scalarBase_adx
        Proof.Ed25519.X86_64.VerifyCode.adx_eq ++
      withField c Impl.X25519.X86_64.baseline ""
        (Impl.Ed25519.X86_64.scalarBase_precomputed Impl.X25519.X86_64.baseline)
        Proof.Ed25519.X86_64.VerifyCode.baseline_eq

def artifacts : List Artifact :=
  VG.Proof.Variants.Sha512Compress.X86_64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Ed25519.X86_64
