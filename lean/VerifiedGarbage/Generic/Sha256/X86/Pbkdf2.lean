import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha256
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Frame
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Frame

/-!
# PBKDF2-HMAC-SHA-256 (RFC 8018) on x86, for every x86 SHA-256 backend: the iteration and the whole derivation

The iteration is the one for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/X86.lean`): each step is two calls of the backend's
verified compression function, on a block laid out once, word by word, in
`scratch` (`U`, its padding and length), starting from the key's inner and
outer hash values.

The whole derivation, `pbkdf2`, is the one for every streaming hash function
(`Impl/Pbkdf2/Whole/X86.lean`), calling the backend's streaming functions,
HMAC's `init` and `finalize` and the iteration above, made with the backend.
`stack` is that of the shared contracts: 48 bytes for the iteration, and 76
for `pbkdf2`, which pushes up to 24 bytes of arguments for the functions it
calls, and their return address, and gives them 48. `pbkdf2` runs that code
in a frame holding its working space (`Proof.Pbkdf2.Whole.X86.pbkFramed`);
scrypt's code calls the code itself, with its own working space, as
`vg_pbkdf2_hmac_sha256_scratch`.
-/

namespace VG.Generic.Sha256.X86.Pbkdf2

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  { Spec.Hmac.sha256I.iterateApi with
    name := Spec.Hmac.sha256I.iterateApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Hmac.sha256I.iterateApi.doc
    code := v.M.iterate
    contract := Spec.Hmac.sha256I.iterateContract X86.abi 48
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.iterateContract; rfl⟩
    stack := 48
    verified := v.iterate
    spSafe := v.iterSp
    features := v.features },
  { Spec.Hmac.sha256I.pbkdf2Api with
    name := Spec.Hmac.sha256I.pbkdf2Api.name ++ v.suffix
    target := X86.target
    doc := Spec.Hmac.sha256I.pbkdf2Api.doc
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Whole.X86.pbkFrame Spec.Hmac.sha256I) 7 v.F.pbkdf2
    contract := Spec.Hmac.sha256I.pbkdf2Contract X86.abi (76 + Proof.Pbkdf2.Whole.X86.pbkFrame Spec.Hmac.sha256I)
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.pbkdf2Contract Spec.Pbkdf2.pbkdf2Contract; rfl⟩
    stack := 76 + Proof.Pbkdf2.Whole.X86.pbkFrame Spec.Hmac.sha256I
    verified := Proof.Pbkdf2.Whole.X86.pbkFramed (Proof.Pbkdf2.Whole.X86.sha256_verified v) (by decide)
      (Proof.Pbkdf2.Whole.X86.noEsp_of_all v.pbkdf2Sp) (Proof.Pbkdf2.Whole.X86.sha256_stack v)
      Proof.Pbkdf2.Whole.X86.sha256_pbkFrameSat
    spSafe := Proof.Pbkdf2.Md.X86.withStackScratch_spSafe (by decide) v.pbkdf2Sp
    features := v.features },
  -- Scrypt's code calls `pbkdf2` with its own working space.
  { Spec.Hmac.sha256I.pbkdf2ScratchApi with
    name := Spec.Hmac.sha256I.pbkdf2ScratchApi.name ++ v.suffix
    target := X86.target
    doc := Spec.Hmac.sha256I.pbkdf2ScratchApi.doc
    code := v.F.pbkdf2
    contract := Spec.Hmac.sha256I.pbkdf2ScratchContract X86.abi 76
    ofSig := ⟨_, _, _, by unfold Spec.Hmac.Instance.pbkdf2ScratchContract; rfl⟩
    stack := 76
    verified := Proof.Pbkdf2.Whole.X86.sha256_verified v
    spSafe := v.pbkdf2Sp
    features := v.features }]

end VG.Generic.Sha256.X86.Pbkdf2
