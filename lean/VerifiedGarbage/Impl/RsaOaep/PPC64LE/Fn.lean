module

public import VerifiedGarbage.Impl.RsaOaep.PPC64LE.Decrypt
public import VerifiedGarbage.Impl.Scrub.PPC64LE

/-!
# RSAES-OAEP on PPC64LE: the functions as emitted

`vg_rsa_oaep_decrypt_precomputed` and `vg_rsa_oaep_encrypt_precomputed`,
calling the hash functions `f` through their tables, each followed by its
cleanup (`Impl.Scrub.PPC64LE.scrub`): the result's 32 bits, the bytes of
stack its frames and those of the functions it calls use, which the cleanup
zeroes, and every volatile register (`Clear.all`), since the functions its
tables hold may write any, which the cleanup clears, so that it returns
without secret residue (`Proof/RsaOaep/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.RsaOaep.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrub)

/-- `vg_rsa_oaep_decrypt_precomputed`, calling the hash functions `f`, as emitted. -/
def decryptP (f : Fns) : Prog isa :=
  scrub 32 3792 Impl.Scrub.PPC64LE.Clear.all (Impl.RsaOaep.PPC64LE.Dec.decryptP f)

/-- `vg_rsa_oaep_encrypt_precomputed`, calling the hash functions `f`, as emitted. -/
def encrypt (f : Fns) : Prog isa :=
  scrub 32 304 Impl.Scrub.PPC64LE.Clear.all (Impl.RsaOaep.PPC64LE.encrypt f)

end VG.Impl.RsaOaep.PPC64LE.Fn
