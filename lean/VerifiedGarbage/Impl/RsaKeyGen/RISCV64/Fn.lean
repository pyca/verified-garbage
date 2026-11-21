module

public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Generate
public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Search
public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Candidate
public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Trial
public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Key
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# RSA's key search on RISC-V, as emitted

`vg_rsa_generate` with the functions it calls, given the code of a
Miller–Rabin round's implementation (`round`, named with `suffix`), and its
cleanup (`Impl.Scrub.RISCV64.scrubAll`): the caller-saved registers cleared but
the 32 bits of its result, and the 656 bytes of stack it uses zeroed, so that
it returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.RISCV64.Fn

open VG VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrubAll)

/-- `vg_rsa_keygen_candidate`, calling the shared round
`vg_miller_rabin_round<suffix>`. -/
def candidate (suffix : String) (round : Prog isa) : Prog isa :=
  Candidate.code (Trial.trial Candidate.hTrial) ("vg_miller_rabin_round" ++ suffix) round

/-- `vg_rsa_prime_search`, calling `vg_rsa_keygen_candidate`. -/
def primeSearch (suffix : String) (round : Prog isa) : Prog isa :=
  Search.code (.call ("vg_rsa_keygen_candidate" ++ suffix) (candidate suffix round))

/-- The controller, calling `vg_rsa_prime_search` and `vg_rsa_keygen_key`. -/
def body (suffix : String) (round : Prog isa) : Prog isa :=
  Generate.code (.call ("vg_rsa_prime_search" ++ suffix) (primeSearch suffix round))
    (.call "vg_rsa_keygen_key" Key.code)

/-- `vg_rsa_generate` as emitted: the controller, then its cleanup. -/
def keySearch (suffix : String) (round : Prog isa) : Prog isa := scrubAll 32 656 (body suffix round)

end VG.Impl.RsaKeyGen.RISCV64.Fn
