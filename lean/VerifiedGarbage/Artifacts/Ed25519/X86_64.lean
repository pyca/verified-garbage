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
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
public import VerifiedGarbage.Proof.Ed25519.X86_64.Scrub
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.Sha512Compress.X86_64

/-! # Ed25519 (RFC 8032) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Ed25519.X86_64

/-- Verification with the SHA-512 implementation `c`, the field multiplications
`fld` and the windows `win`, those of `vg_ed25519_verify_equation` with the
suffix `fs`, whose own instructions are at the level `lv`. -/
def verifyWith (c : Proof.Sha512.X86_64.Compress) (fld : Impl.Ed25519.X86_64.Arith)
    [Proof.Ed25519.X86_64.EdArith fld] (win : Prog X86_64.isa)
    (fs : String)
    (hq : Proof.Ed25519.X86_64.VerifyMessage.EqCode fld win) (lv : Impl.Scrub.X86_64.VecLevel)
    (hs : Proof.Ed25519.X86_64.Scrub.VerifyStub lv fld win fs) :
    Artifact :=
  Spec.Ed25519.verifyApi.artifact X86_64.target
    { suffix := c.suffix ++ fs
      code := Impl.Ed25519.X86_64.VerifyMessage.Fn.verify (c.level.join lv) fld win fs c.callee c.suffix
      verified := Proof.Ed25519.X86_64.Scrub.verify_scrubbed c hq lv hs
      spSafe := Proof.Ed25519.X86_64.Scrub.verify_spSafe c hq _ }

/-- Signing with the seed's cached SHA-512 digest and public key, with the SHA-512
implementation `c`, calling the base-point multiplication `bs` (`vg_ed25519_scalar_base` with
the suffix `fs`), whose own instructions are at the level `lv`. -/
def signExpandedWith (c : Proof.Sha512.X86_64.Compress) (bs : Prog X86_64.isa)
    [Proof.Ed25519.X86_64.EdBase bs] (fs : String) (lv : Impl.Scrub.X86_64.VecLevel)
    (hs : Proof.Ed25519.X86_64.Scrub.SignStub lv bs fs) : Artifact :=
  Spec.Ed25519.signExpandedApi.artifact X86_64.target
    { suffix := c.suffix ++ fs
      code := Impl.Ed25519.X86_64.SignCached.Fn.signExpanded (c.level.join lv) bs fs c.callee c.suffix
      verified := Proof.Ed25519.X86_64.Scrub.signExpanded_scrubbed c lv hs
      spSafe := Proof.Ed25519.X86_64.Scrub.signExpanded_spSafe c _ }

/-- Key-pair derivation with the SHA-512 implementation `c`'s one-shot digest, whose code
it calls as the internal `vg_sha512_digest<suffix>_core` (the exported digest also clears
what it leaves), calling `vg_ed25519_public_key_expanded` with the suffix `fs`, whose
base-point multiplication is `bs`, whose own instructions are at the level `lv`. -/
def keyPairWith (c : Proof.Sha512.X86_64.Compress) (bs : Prog X86_64.isa)
    [Proof.Ed25519.X86_64.EdBase bs] (fs : String) (lv : Impl.Scrub.X86_64.VecLevel)
    (hs : Proof.Ed25519.X86_64.Scrub.KeyPairStub lv bs fs) : Artifact :=
  Spec.Ed25519.keyPairApi.artifact X86_64.target
    { suffix := c.suffix ++ fs
      code := Impl.Ed25519.X86_64.KeyPair.Fn.keyPair (c.level.join lv)
        (Spec.Sha512.digest512Api.name ++ c.suffix ++ "_core") (Proof.Ed25519.X86_64.KeyPair.dgCode c)
        ("vg_ed25519_public_key_expanded" ++ fs) (Impl.Ed25519.X86_64.publicKeyExpanded bs fs)
      verified := Proof.Ed25519.X86_64.Scrub.keyPair_scrubbed c lv hs
      spSafe := Proof.Ed25519.X86_64.Scrub.keyPair_spSafe c _ }

/-- Verification and signing with the SHA-512 implementation `c` and the field
multiplications `fld` (verification's doublings too), those of the Ed25519
functions with the suffix `fs`; signing calls the base-point multiplication
`bs`. -/
def withField (c : Proof.Sha512.X86_64.Compress) (fld : Impl.Ed25519.X86_64.Arith)
    [Proof.Ed25519.X86_64.EdArith fld] (fs : String)
    (bs : Prog X86_64.isa) [Proof.Ed25519.X86_64.EdBase bs]
    (hq : Proof.Ed25519.X86_64.VerifyMessage.EqCode fld (Impl.Ed25519.X86_64.windows fld))
    (lvV lvS : Impl.Scrub.X86_64.VecLevel)
    (hv : Proof.Ed25519.X86_64.Scrub.VerifyStub lvV fld (Impl.Ed25519.X86_64.windows fld) fs)
    (hs : Proof.Ed25519.X86_64.Scrub.SignStub lvS bs fs) (hk : Proof.Ed25519.X86_64.Scrub.KeyPairStub lvS bs fs) :
    List Artifact :=
  [verifyWith c fld (Impl.Ed25519.X86_64.windows fld) fs hq lvV hv,
    signExpandedWith c bs fs lvS hs, keyPairWith c bs fs lvS hk]

/-- Each operation with the SHA-512 implementation of `v`, if it has one, and
each field multiplication of the Ed25519 functions, best first: with
AVX512_IFMA (`_ifma`), verification with its windows, and signing with its
comb; BMI2's and ADX's (`_adx`, whose comb also selects its entries with
AVX2); and the baseline's. -/
def artifactsFor (c : Proof.Sha512.X86_64.Compress) : List Artifact :=
  [verifyWith c Impl.X25519.X86_64.adx
        Impl.Ed25519.X86_64.Ifma.windows "_ifma" Proof.Ed25519.X86_64.VerifyCode.ifma_eq .avx
        Proof.Ed25519.X86_64.Scrub.verify_stub_ifma,
        signExpandedWith c Impl.Ed25519.X86_64.scalarBase_ifma "_ifma" .avx Proof.Ed25519.X86_64.Scrub.sign_stub_ifma,
        keyPairWith c Impl.Ed25519.X86_64.scalarBase_ifma "_ifma" .avx Proof.Ed25519.X86_64.Scrub.keyPair_stub_ifma] ++
      withField c Impl.X25519.X86_64.adx "_adx" Impl.Ed25519.X86_64.scalarBase_adx
        Proof.Ed25519.X86_64.VerifyCode.adx_eq .sse .avx Proof.Ed25519.X86_64.Scrub.verify_stub_adx
        Proof.Ed25519.X86_64.Scrub.sign_stub_adx Proof.Ed25519.X86_64.Scrub.keyPair_stub_adx ++
      withField c Impl.X25519.X86_64.baseline ""
        (Impl.Ed25519.X86_64.scalarBase_precomputed Impl.X25519.X86_64.baseline)
        Proof.Ed25519.X86_64.VerifyCode.baseline_eq .sse .sse Proof.Ed25519.X86_64.Scrub.verify_stub_baseline
        Proof.Ed25519.X86_64.Scrub.sign_stub_baseline Proof.Ed25519.X86_64.Scrub.keyPair_stub_baseline

def artifacts : List Artifact :=
  VG.Proof.Variants.Sha512Compress.X86_64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Ed25519.X86_64
