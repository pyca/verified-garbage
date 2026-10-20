module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Verified
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashVariants
public import VerifiedGarbage.Proof.Dsa.X86.Generation.EntrySafety
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Instance
public import VerifiedGarbage.Proof.Sha1.X86.Variants.Interface
public import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
public import VerifiedGarbage.TCB.Emit
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Registration

/-! # DSA parameter generation for every pair of x86 SHA backends -/
@[expose] public section
namespace VG.Generic.Sha1.Sha256.X86.Dsa
open VG.Proof.Dsa.X86.Generation

def artifacts (v1 : Proof.Sha1.X86.Variants.Backend) (v256 : Proof.Sha256.X86.Variants.Backend) : List Artifact :=
  let hashes := generationHashes v1.stream v256.stream
  let check := Proof.Dsa.X86.KeyRandom.checkFn
  [Spec.Dsa.generateParametersApi.artifact X86.target {
    suffix := Emit.qualifiedName "" [("sha1", v1.suffix), ("sha256", v256.suffix)]
    stack := 292
    notes := ["Verified bounded seed, prime, and generator searches for 1024/160, 2048/256, and 3072/256. \
      A shared candidate division supplies the modulus and generator exponent. Reciprocal trial division \
      and reused Montgomery setup reduce primality-test work. All three search tapes are public under the contract."]
    code := Impl.Dsa.X86.Generation.code hashes.sha1 hashes.sha256 check.name check.code
    verified := verified hashes check
    spSafe := entry_safe hashes check
    features := v1.features ++ v256.features.filter (!v1.features.contains ·) }]
end VG.Generic.Sha1.Sha256.X86.Dsa
