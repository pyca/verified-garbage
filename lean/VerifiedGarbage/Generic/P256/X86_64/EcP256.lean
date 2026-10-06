import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.P256.Comb7
import VerifiedGarbage.Impl.EcKey.P256.X86_64
import VerifiedGarbage.Proof.EcKey.X86_64.Verified
import VerifiedGarbage.Proof.EcKey.X86_64.Lit
import VerifiedGarbage.Proof.EcKey.X86_64.VerifiedAdx
import VerifiedGarbage.Proof.EcKey.X86_64.LitAdx

/-!
# P-256 public keys (FIPS 186-5 §A.2) on x86-64

A generic file (see `TCB/Emit.lean`) over P-256's group law and
inversions `h`, the variant `Variants/P256/X86_64/Law.lean`, for each
multiplication: the baseline's, and BMI2's and ADX's, with the comb's
selection by AVX2 (`_adx`).
-/

namespace VG.Generic.P256.X86_64.EcP256

/-- The function of `Spec.EcKey.P256.publicKeyApi`, multiplying with BMI2 and ADX
(`adx`, `_adx`) or not: its `code`, proven (`hv`), with no instruction writing
`rsp` (`hsp`). -/
def publicKey (adx : Bool) (code : Prog X86_64.isa)
    (hv : Verified X86_64.target code
      (Spec.EcKey.P256.inst.publicKeyContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p256.combConsts)))
    (hsp : code.all (fun i => !X86_64.isa.writesSp i) = true) : Artifact :=
  { Spec.EcKey.P256.publicKeyApi with
    name := Spec.EcKey.P256.publicKeyApi.name ++ (if adx then "_adx" else "")
    target := X86_64.target
    doc := Spec.EcKey.P256.publicKeyApi.doc (notes := ["The function is `vg_ecdsa_p256_sign" ++ (if adx then "_adx" else "") ++ "`'s \
      code up to the inversion of `Z`, with `d` as both the key and the secret number: it saves \
      its caller's callee-saved registers in `scratch`; field elements are four 64-bit words in \
      Montgomery form, " ++ Proof.Ecdsa.X86_64.mulNote adx ++ "; `[d]G` is the signature's comb over the 7-bit windows of `d`, from \
      the static `VG_P256_COMB`; and `Z⁻¹` is by the signature's divsteps. The result (or zeros) is selected by a mask of `d ∈ [1, n-1]` and `Z ≠ 0`, \
      so the time depends only on the pointers."])
    consts := Impl.Ecdsa.X86_64.p256.combConsts
    code
    contract := Spec.EcKey.P256.inst.publicKeyContract
      (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p256.combConsts)
    verified := hv
    spSafe := hsp
    features := if adx then ["bmi2", "adx", "avx", "avx2"] else [] }

def artifacts (h : Proof.Weierstrass.X86_64.HasLawInv Spec.P256.curve) : List Artifact := [
  publicKey false Impl.EcKey.X86_64.publicKeyP256
    (Proof.EcKey.X86_64.pk_verified h.law (Proof.P256.combOk7 h.law) h.inv) (Code.all_of_allInstrs (by lit_decide)),
  publicKey true Impl.EcKey.X86_64.publicKeyP256Adx
    (Proof.EcKey.X86_64.pk_verified_adx h.law (Proof.P256.combOk7 h.law) h.inv) (Code.all_of_allInstrs (by lit_decide))]

end VG.Generic.P256.X86_64.EcP256
