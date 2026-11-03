module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Verified
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Hashes

/-!
# RSAES-OAEP encryption on PPC64LE: the instances

Untrusted: everything here is checked by Lean. A hash function's streaming
functions with what the proofs need of them (`Link`: `HashOK`, `HashCT`, and
the hash function of `Spec.Mgf1` they compute, among those the label may be
hashed with); `link_verified`: encryption for two of them, which the
registration files bind.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE

/-- `vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed` for the linked hash
functions. -/
theorem link_verified {H G : Hash} (lh : Link H) (lg : Link G) :
    Verified PPC64LE.target (Impl.RsaOaep.PPC64LE.encrypt H G)
      (Spec.RsaOaep.encryptPrecomputedContract lh.G lg.G abi 304) :=
  enc_verified lh.ok lh.ct lg.ok lg.ct lh.hash lh.len lg.hash lg.len lg.valid (enc_sat lg.G lh.mem)

end VG.Proof.RsaOaep.PPC64LE
