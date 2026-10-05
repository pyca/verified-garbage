import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCt

/-!
# RSASSA-PSS verification on x86-64

A generic file (see `TCB/Emit.lean`): `vg_rsa_pss_<H>_mgf1_<H>_verify`, for
the hash function of each `MdHash` variant `v` (`Variants/MdHash/X86_64/`)
with MGF1 over the same hash function, calling `v`'s compression function
and `vg_rsa_public_checked`, is emitted once for each variant, named with its
suffix (e.g. `vg_rsa_pss_sha256_mgf1_sha256_verify_shani`), and needs its CPU
features.

Its stack is its frame and the return address of its calls, which use none.
-/

namespace VG.Generic.MdHash.X86_64.RsaPss

open VG.Proof.RsaPss.X86_64 (verifyStack verify_verified verify_spSafe safeI)

theorem pubSafe : Impl.Rsa.X86_64.Checked.publicChecked.allInstrs safeI = true := by
  decide +kernel

theorem pubDepth : Impl.Rsa.X86_64.Checked.publicChecked.x86_64Depth = 0 := by decide +kernel

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact := [
  { Spec.RsaPss.verifyApi v.mgf.G v.mgf.G with
    name := (Spec.RsaPss.verifyApi v.mgf.G v.mgf.G).name ++ v.suffix
    target := X86_64.target
    doc := (Spec.RsaPss.verifyApi v.mgf.G v.mgf.G).doc (notes := ["This implementation computes RSAVP1 with \
      `" ++ Spec.Rsa.publicCheckedApi.name ++ "` into its working space, then checks the encoding \
      without a branch on it: `DB`, `maskedDB ⊕ MGF1(H)`, is scanned for its first nonzero byte, the \
      salt is shifted into place by ten passes whatever its length, and `M'` is hashed over the \
      blocks the longest salt needs, the digest of the actual length selected by a mask. Only the \
      lengths, `salt_len`, `any_salt_len` and `n` decide a branch or an address."])
    code := Impl.RsaPss.X86_64.verify v.H Spec.Rsa.publicCheckedApi.name Impl.Rsa.X86_64.Checked.publicChecked
    contract := Spec.RsaPss.verifyContract v.mgf.G v.mgf.G X86_64.abi verifyStack
    stack := verifyStack
    verified := verify_verified (hct := Proof.Rsa.X86_64.publicChecked_constantTime) (hH := v.ok) (K := v.K)
      (lk := v.mgf) (hc := v.pss) Proof.Rsa.X86_64.publicChecked_correct pubSafe pubDepth
    spSafe := verify_spSafe v.ok v.K pubSafe
    features := v.features }]

end VG.Generic.MdHash.X86_64.RsaPss
