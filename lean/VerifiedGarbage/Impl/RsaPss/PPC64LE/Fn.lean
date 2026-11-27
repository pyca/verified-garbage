module

public import VerifiedGarbage.Impl.RsaPss.PPC64LE.Sign
public import VerifiedGarbage.Impl.Scrub.PPC64LE

/-!
# RSASSA-PSS on PPC64LE: the functions as emitted

`vg_rsa_pss_verify_precomputed` and `vg_rsa_pss_sign_precomputed`, calling
the message's hash functions `f` and MGF1's `g` through their tables, each
followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the result's 32 bits,
the bytes of stack its frames and those of the functions it calls use, which
the cleanup zeroes, and every volatile register (`Clear.all`), since the
functions its tables hold may write any, which the cleanup clears, so that
it returns without secret residue (`Proof/RsaPss/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.RsaPss.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)
open VG.Impl.RsaOaep.PPC64LE (Fns)

/-- `vg_rsa_pss_verify_precomputed`, calling the hash functions `f` and `g`, as emitted. -/
def verifyPrecomputed (f : MdFns) (g : Fns) : Prog isa :=
  scrubAll 32 304 Impl.Scrub.PPC64LE.Clear.all (Impl.RsaPss.PPC64LE.verifyPrecomputed f g)

/-- `vg_rsa_pss_sign_precomputed`, calling the hash functions `f` and `g`, as emitted. -/
def signP (f : MdFns) (g : Fns) : Prog isa :=
  scrubAll 32 3792 Impl.Scrub.PPC64LE.Clear.all (Impl.RsaPss.PPC64LE.Sign.signP f g)

end VG.Impl.RsaPss.PPC64LE.Fn
