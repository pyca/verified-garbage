module

public import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Sound
public import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Verified
public import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyMessage.Verified
public import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Expanded
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

/-!
# Ed25519 (RFC 8032) on x86-64, over SHA-512

Signing with the cached SHA-512 digest of the seed and public key, and verification, are
emitted for every SHA-512 compression backend carried by `MdHash.sha512`, and for
each field multiplication of the Ed25519 functions they call (the baseline's,
and BMI2's and ADX's, `_adx`), and with AVX512_IFMA (`_ifma`): verification for
its windows, signing for its comb (`vg_ed25519_scalar_base_ifma`). Each operation includes
its streaming hash calls and carries the backend's suffix and CPU features, then the field's.
Key derivation, which hashes no more than the seed, takes its digest
(`Artifacts/Ed25519PublicKeyExpanded/X86_64.lean`).
Other hash families emit no Ed25519 artifacts.
-/

@[expose] public section

namespace VG.Generic.MdHash.X86_64.Ed25519

/-- Verification with the SHA-512 implementation `c`, the field multiplications
`fld` and the windows `win`, those of `vg_ed25519_verify_equation` with the
suffix `fs`, which need the CPU features `ff`. -/
def verifyWith (c : Proof.Sha512.X86_64.Compress) (fld : Impl.Ed25519.X86_64.Arith)
    [Proof.Ed25519.X86_64.EdArith fld] (win : Prog X86_64.isa)
    (fs : String) (ff : List String)
    (hq : Proof.Ed25519.X86_64.VerifyMessage.EqCode fld win) :
    Artifact :=
  Spec.Ed25519.verifyApi.artifact X86_64.target {
    suffix := c.suffix ++ fs
    consts := Impl.Ed25519.X86_64.baseOddConsts
    code := Impl.Ed25519.X86_64.VerifyMessage.code fld win fs c.callee c.suffix
    stack := 184
    verified := Proof.Ed25519.X86_64.VerifyMessage.verified hq c
    spSafe := Proof.Ed25519.X86_64.VerifyMessage.spSafe hq c
    features := c.features ++ ff.filter (!c.features.contains ·) }

/-- Signing with the seed's cached SHA-512 digest and public key, with the SHA-512
implementation `c`, calling the base-point multiplication `bs` (`vg_ed25519_scalar_base` with
the suffix `fs`), which needs the CPU features `ff`. -/
def signExpandedWith (c : Proof.Sha512.X86_64.Compress) (bs : Prog X86_64.isa)
    [Proof.Ed25519.X86_64.EdBase bs] (fs : String) (ff : List String) : Artifact :=
  Spec.Ed25519.signExpandedApi.artifact X86_64.target {
    suffix := c.suffix ++ fs
    consts := Impl.Ed25519.X86_64.combConsts
    code := Impl.Ed25519.X86_64.SignCached.codeExpanded bs fs c.callee c.suffix
    stack := 264
    verified := Proof.Ed25519.X86_64.SignCached.verifiedE c
    spSafe := Proof.Ed25519.X86_64.SignCached.spSafeE c
    features := c.features ++ ff.filter (!c.features.contains ·) }

/-- Verification and signing with the SHA-512 implementation `c` and the field
multiplications `fld` (verification's doublings too), those of the Ed25519
functions with the suffix `fs`, which need the CPU features `ff`; signing
calls the base-point multiplication `bs`, which needs `bf`. -/
def withField (c : Proof.Sha512.X86_64.Compress) (fld : Impl.Ed25519.X86_64.Arith)
    [Proof.Ed25519.X86_64.EdArith fld] (fs : String) (ff : List String)
    (bs : Prog X86_64.isa) [Proof.Ed25519.X86_64.EdBase bs] (bf : List String)
    (hq : Proof.Ed25519.X86_64.VerifyMessage.EqCode fld (Impl.Ed25519.X86_64.windows fld)) :
    List Artifact :=
  [verifyWith c fld (Impl.Ed25519.X86_64.windows fld) fs ff hq,
    signExpandedWith c bs fs bf]

/-- Each operation with the SHA-512 implementation of `v`, if it has one, and
each field multiplication of the Ed25519 functions: the baseline's, and
BMI2's and ADX's (`_adx`, whose comb also selects its entries with AVX2); and with AVX512_IFMA
(`_ifma`), verification with its windows, and signing with its comb. -/
def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact :=
  match v.sha512 with
  | none => []
  | some c => withField c Impl.X25519.X86_64.baseline "" []
        (Impl.Ed25519.X86_64.scalarBase_precomputed Impl.X25519.X86_64.baseline) []
        Proof.Ed25519.X86_64.VerifyCode.baseline_eq ++
      withField c Impl.X25519.X86_64.adx "_adx" ["bmi2", "adx"] Impl.Ed25519.X86_64.scalarBase_adx
        ["avx", "avx2", "bmi2", "adx"]
        Proof.Ed25519.X86_64.VerifyCode.adx_eq ++
      [verifyWith c Impl.X25519.X86_64.adx
        Impl.Ed25519.X86_64.Ifma.windows "_ifma"
        ["avx", "avx2", "bmi2", "adx", "avx512ifma", "avx512vl"]
        Proof.Ed25519.X86_64.VerifyCode.ifma_eq,
        signExpandedWith c Impl.Ed25519.X86_64.scalarBase_ifma "_ifma"
          ["avx", "avx2", "bmi2", "adx", "avx512f", "avx512ifma", "avx512vl"]]

end VG.Generic.MdHash.X86_64.Ed25519
