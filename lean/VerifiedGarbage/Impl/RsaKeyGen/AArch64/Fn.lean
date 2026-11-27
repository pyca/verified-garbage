module

public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Generate
public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Search
public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Key
public import VerifiedGarbage.Impl.MillerRabin.AArch64.Caller
public import VerifiedGarbage.Impl.MillerRabin.AArch64.Round
public import VerifiedGarbage.Impl.Scrub.AArch64.Writes

/-!
# RSA's key search on AArch64, as emitted

`vg_rsa_key_search` with the functions it calls, given the Montgomery
multiplications of a Miller–Rabin round's implementation, and its cleanup
(`Impl.Scrub.AArch64.scrubOf`), so that it returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.AArch64.Fn

open VG VG.AArch64 VG.Impl.Scrub.AArch64

/-- `vg_rsa_keygen_candidate`: its own arithmetic with the multiplication
`mm`, calling the shared round `vg_miller_rabin_round`, whose
multiplication is `rmm`. -/
def candidate (suffix : String) (mm rmm : Nat → Nat → Nat → Prog isa) : Prog isa :=
  Candidate.codeWith mm
    [Impl.MillerRabin.AArch64.Caller.call ("vg_miller_rabin_round" ++ suffix) (Impl.MillerRabin.AArch64.round rmm)]

/-- `vg_rsa_prime_search`, calling `vg_rsa_keygen_candidate`. -/
def primeSearch (suffix : String) (mm rmm : Nat → Nat → Nat → Prog isa) : Prog isa :=
  Search.code (.call ("vg_rsa_keygen_candidate" ++ suffix) (candidate suffix mm rmm))

/-- `vg_rsa_key_search` as emitted: the controller, which calls
`vg_rsa_prime_search` and `vg_rsa_keygen_key`, then its cleanup over the 416
bytes of stack it uses. -/
def keySearch (suffix : String) (mm rmm : Nat → Nat → Nat → Prog isa) : Prog isa :=
  scrubOf 416 32 (Generate.code (.call ("vg_rsa_prime_search" ++ suffix) (primeSearch suffix mm rmm))
    (.call "vg_rsa_keygen_key" Key.code))

end VG.Impl.RsaKeyGen.AArch64.Fn
