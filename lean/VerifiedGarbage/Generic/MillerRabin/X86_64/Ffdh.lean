module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.DerivePublic.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchVerified
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Emit FFDH domain operations for every shared arithmetic backend -/

@[expose] public section

namespace VG.Generic.MillerRabin.X86_64.Ffdh

def artifacts (v : Proof.MillerRabin.X86_64.RoundImpl) : List Artifact := [
  Spec.Ffdh.checkPublicApi.artifact X86_64.target {
    suffix := v.suffix
    stack := 8
    notes := ["The verified range and optional subgroup checks use fixed four-bit windows \
        with the selected Montgomery backend. Domain bytes and the public key are public \
        under the shared contract."]
    code := Proof.Ffdh.X86_64.CheckPublic.publicCode v
    verified := Proof.Ffdh.X86_64.CheckPublic.publicCode_verified v
    spSafe := Proof.Ffdh.X86_64.CheckPublic.publicCode_sp v
    features := v.features },
  Spec.Ffdh.exchangeApi.artifact X86_64.target {
    suffix := v.suffix
    stack := 8
    notes := ["The selected Montgomery backend and fixed four-bit windows process every \
        supplied scalar byte. The result is masked to zero for a degenerate shared value."]
    code := Proof.Ffdh.X86_64.Exchange.exchangeCode v
    verified := Proof.Ffdh.X86_64.Exchange.exchangeCode_verified v
    spSafe := Proof.Ffdh.X86_64.Exchange.exchangeCode_sp v
    features := v.features },
  Spec.Ffdh.checkPrivateApi.artifact X86_64.target {
    suffix := v.suffix
    stack := 8
    notes := ["The scalar bound and the public-value equality are checked in verified code. \
        Powers of a checked generator remain in its q subgroup, so the generated power \
        needs only its range check. Fixed four-bit windows use the selected Montgomery backend."]
    code := Proof.Ffdh.X86_64.CheckPrivate.privateCode v
    verified := Proof.Ffdh.X86_64.CheckPrivate.privateCode_verified v
    spSafe := Proof.Ffdh.X86_64.CheckPrivate.privateCode_sp v
    features := v.features },
  Spec.Ffdh.derivePublicApi.artifact X86_64.target {
    suffix := v.suffix
    stack := 8
    notes := ["The output is zeroed first; the scalar's range, as `vg_ffdh_check_private` checks \
        it, is the one branch on x. Powers of a checked generator remain in its q subgroup, so \
        the power needs only its range check, which masks the output, as in \
        `vg_ffdh_generate_key`. Fixed four-bit windows over all `x_len` scalar bytes use the \
        selected Montgomery backend."]
    code := Proof.Ffdh.X86_64.DerivePublic.deriveCode v
    verified := Proof.Ffdh.X86_64.DerivePublic.deriveCode_verified v
    spSafe := Proof.Ffdh.X86_64.DerivePublic.deriveCode_sp v
    features := v.features },
  Spec.Ffdh.generateKeyApi.artifact X86_64.target {
    suffix := v.suffix
    stack := 8
    notes := ["Scalar masking, scalar-range rejection, generator exponentiation, and \
        degenerate-public-value rejection run in verified code. Fixed four-bit windows \
        use the public bound's significant byte width and the selected Montgomery backend."]
    code := Proof.Ffdh.X86_64.GenerateKey.generateCode v
    verified := Proof.Ffdh.X86_64.GenerateKey.generateCode_verified v
    spSafe := Proof.Ffdh.X86_64.GenerateKey.generateCode_sp v
    features := v.features },
  Spec.Ffdh.checkDomainApi.artifact X86_64.target {
    suffix := v.suffix
    stack := 8
    notes := ["The modulus, generator, optional subgroup range, divisibility, and subgroup \
        relation are checked in verified code. Divisibility uses RSA's arbitrary-width \
        Montgomery reduction; fixed four-bit exponentiation uses the selected backend."]
    code := Proof.Ffdh.X86_64.CheckDomain.domainCode v
    verified := Proof.Ffdh.X86_64.CheckDomain.domainCode_verified v
    spSafe := Proof.Ffdh.X86_64.CheckDomain.domainCode_sp v
    features := v.features },
  Spec.Ffdh.parameterSearchApi.artifact X86_64.target {
    suffix := v.suffix
    stack := 160
    notes := ["The whole candidate search runs in verified code: the attempt limit, the \
        octets each rejected candidate consumed, and the length of the next entropy \
        request. Both primes use the shared Miller–Rabin round with the selected \
        Montgomery backend, with 64 or 128 independent witnesses for each. The random \
        tape and the controller's four public words are public under the contract."]
    code := Proof.Ffdh.X86_64.Generation.searchCode v
    verified := Proof.Ffdh.X86_64.Generation.search_verified v
    spSafe := Proof.Ffdh.X86_64.Generation.searchCode_sp v
    features := v.features },
  Spec.Ffdh.keySearchApi.artifact X86_64.target {
    suffix := v.suffix
    stack := 56
    notes := ["The whole key search runs in verified code: both rejection budgets, the \
        octets each attempt consumes, and the next entropy request. Each attempt calls \
        `vg_ffdh_generate_key` with the same backend, in a 40-byte frame. Timing depends \
        on the domain, the controller's public words and the attempts' statuses."]
    code := Proof.Ffdh.X86_64.KeyGeneration.keyCode v
    verified := Proof.Ffdh.X86_64.KeyGeneration.key_verified v
    spSafe := Proof.Ffdh.X86_64.KeyGeneration.keyCode_sp v
    features := v.features }]

end VG.Generic.MillerRabin.X86_64.Ffdh
