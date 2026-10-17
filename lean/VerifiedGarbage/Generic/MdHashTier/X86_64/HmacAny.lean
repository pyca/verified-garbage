module

public import VerifiedGarbage.Proof.Hmac.Any.X86_64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# HMAC and streaming `update` with the hash function as an argument on x86-64

A generic file (see `TCB/Emit.lean`): `vg_hmac_init_scratch`,
`vg_hash_update_scratch` and `vg_hmac_finalize_scratch` call the function of
the hash function `hash` names in the tier `v`
(`Variants/MdHashTier/X86_64/`), so each is emitted once for every tier,
named with its suffix (e.g. `vg_hmac_init_scratch_shani_avx2`), and needs
its CPU features.

The stack is the return address of the call and what the called function
uses: 16 bytes for HMAC's `init` and `finalize`, 8 for `update`.
-/

@[expose] public section

namespace VG.Generic.MdHashTier.X86_64.HmacAny

open VG.Proof.Hmac.Any.X86_64 (hsOf vsOf init_spec upd_spec fin_spec init_sp upd_sp fin_sp)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.Tier) : List Artifact := [
  Spec.Hmac.Any.initApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["This implementation calls the `vg_hmac_<hash>_init_scratch` of the hash function \
      `hash` names, through a comparison of `hash` with each number, with the arguments as it \
      was given them."]
    code := Impl.Hmac.Any.X86_64.init (hsOf (vsOf v))
    stack := 24
    verified := init_spec v
    spSafe := init_sp _
    features := v.features },
  Spec.Hmac.Any.updateApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["This implementation calls the streaming `update` of the hash function `hash` names \
      (`vg_sha1_update_scratch`, `vg_sha256_update_scratch` or `vg_sha512_update_scratch`), \
      through a comparison of `hash` with each number, with the arguments as it was given them."]
    code := Impl.Hmac.Any.X86_64.update (hsOf (vsOf v))
    stack := 16
    verified := upd_spec v
    spSafe := upd_sp _
    features := v.features },
  Spec.Hmac.Any.finalizeApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["This implementation calls the `vg_hmac_<hash>_finalize_scratch` of the hash \
      function `hash` names, through a comparison of `hash` with each number, with the arguments \
      as it was given them."]
    code := Impl.Hmac.Any.X86_64.finalize (hsOf (vsOf v))
    stack := 24
    verified := fin_spec v
    spSafe := fin_sp _
    features := v.features }]

end VG.Generic.MdHashTier.X86_64.HmacAny
