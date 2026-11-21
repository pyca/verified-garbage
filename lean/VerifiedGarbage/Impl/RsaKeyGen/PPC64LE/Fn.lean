module

public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.KeyInit
public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Candidate
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Generate
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Key
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Search
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Trial

/-!
# RsaKeyGen on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/RsaKeyGen/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `vg_rsa_generate_init`, as emitted. -/
def keyInit : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (Impl.RsaKeyGen.PPC64LE.KeyInit.init)

/-- `vg_rsa_generate_search<suffix>`, as emitted, with the Miller–Rabin round
`round` (`vg_miller_rabin_round<suffix>`): the controller, calling the prime
search `vg_rsa_prime_search<suffix>` (which calls the candidate test
`vg_rsa_keygen_candidate<suffix>`) and the key `vg_rsa_keygen_key`, then the
clearing of the 1088 bytes of stack its frames use. -/
def keySearch (suffix : String) (round : Prog isa) : Prog isa :=
  scrubAll 32 1088 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (Impl.RsaKeyGen.PPC64LE.Generate.code
      (.call ("vg_rsa_prime_search" ++ suffix)
        (Impl.RsaKeyGen.PPC64LE.Search.code (.call ("vg_rsa_keygen_candidate" ++ suffix)
          (Impl.RsaKeyGen.PPC64LE.Candidate.code
            (Impl.RsaKeyGen.PPC64LE.Trial.trial Impl.RsaKeyGen.PPC64LE.Candidate.hTrial)
            ("vg_miller_rabin_round" ++ suffix) round))))
      (.call "vg_rsa_keygen_key" Impl.RsaKeyGen.PPC64LE.Key.code))

end VG.Impl.RsaKeyGen.PPC64LE.Fn
