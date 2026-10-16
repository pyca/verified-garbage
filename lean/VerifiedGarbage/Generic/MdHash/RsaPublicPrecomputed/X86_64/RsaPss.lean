module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaPss.X86_64.PrecomputedCT
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# RSASSA-PSS verification using cached public-key values

Every hash compression variant combines with every precomputed RSA public
operation variant. The digest, signature and recovered encoding stay secret.
-/

@[expose] public section

namespace VG.Generic.MdHash.RsaPublicPrecomputed.X86_64.RsaPss

open VG.Proof.RsaPss.X86_64 (verifyStack safeI_eq allInstrs_and)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) (c : Proof.Rsa.X86_64.PublicImpl) : List Artifact := [
  (Spec.RsaPss.verifyPrecomputedApi v.mgf.G v.mgf.G).artifact X86_64.target {
    suffix := Emit.qualifiedName "" [(v.mgf.G.rust, v.suffix), ("rsa", c.suffix)]
    notes := ["This implementation calls `" ++ c.name ++ "` with the cached public-key values, \
        then checks EMSA-PSS using the same padding and hashing code as the original verifier."]
    code := Impl.RsaPss.X86_64.Precomputed.code v.H c.name c.code
    stack := verifyStack
    verified := Proof.RsaPss.X86_64.Pc.verified c v.ok v.K v.mgf v.pss
    spSafe := by
      have h := Proof.RsaPss.X86_64.Pc.code_safe v.ok v.K c
      rw [safeI_eq, allInstrs_and, Bool.and_eq_true] at h
      exact Code.all_of_allInstrs h.1
    features := v.features ++ c.features.filter (!v.features.contains ·) }]

end VG.Generic.MdHash.RsaPublicPrecomputed.X86_64.RsaPss
