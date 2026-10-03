import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Verified
import VerifiedGarbage.Proof.Ed448.X86_64.BaseVerified

/-!
# Ed448 signing with a cached public key on x86-64

The signature and documentation come from the reviewed Ed448 API. The proof
of `vg_ed448_scalar_base` is passed to the caller's here, so that only this
file imports it.
-/

namespace VG.Artifacts.Ed448SignCached.X86_64

def artifacts : List Artifact := [
  { Spec.Ed448.signCachedApi with
    target := X86_64.target
    doc := Spec.Ed448.signCachedApi.doc (notes := ["Uses baseline integer instructions. \
      Hashes the private key, `dom4(0, C) || prefix || M` and `dom4(0, C) || R || A || M` with \
      `vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze` (SHAKE256, with the Keccak \
      state and the sponge functions' working space in `scratch`) into a stack frame; prunes \
      the scalar `s` there; reduces the nonce `r` and the challenge `k` with \
      `vg_ed448_scalar_reduce`; writes `R = [r]B` with `vg_ed448_scalar_base` and \
      `S = (r + k s) mod L` with `vg_ed448_scalar_mul_add` into `out`; and clears `s` and `r` \
      from the frame. The hashes, and the scalar operations' working values, are left in \
      `scratch`."])
    code := Impl.Ed448.X86_64.SignCached.signCached
    contract := Spec.Ed448.signCachedContract X86_64.abi 464
    stack := 464
    verified := Proof.Ed448.X86_64.SignCached.signCached_verified Proof.Ed448.X86_64.scalarBase_ok
      Proof.Ed448.X86_64.scalarBase_ct
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed448SignCached.X86_64
