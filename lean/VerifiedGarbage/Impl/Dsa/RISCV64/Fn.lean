module

public import VerifiedGarbage.Impl.Dsa.RISCV64.Derive
public import VerifiedGarbage.Impl.Dsa.RISCV64.PrevalidatedSign
public import VerifiedGarbage.Impl.Dsa.RISCV64.Generate
public import VerifiedGarbage.Impl.Dsa.RISCV64.Prevalidated
public import VerifiedGarbage.Impl.Dsa.RISCV64.ParameterSearch
public import VerifiedGarbage.Impl.Dsa.RISCV64.ProbablePrime
public import VerifiedGarbage.Impl.Dsa.RISCV64.Params
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# DSA on RISC-V, as emitted

Each function is its code, then its cleanup (`Impl.Scrub.RISCV64.scrub`):
the caller-saved registers cleared but the 32 bits of its result, and the
stack its frames use (192 bytes for signing and key generation, none for
the others), so that it returns without secret residue.

The parameter search, `vg_dsa_parameter_search`, is given the code of a
Miller–Rabin round's implementation (`round`, named with `suffix`), which its
probable-prime tests call; its cleanup zeroes the 512 bytes of stack it uses.
-/

@[expose] public section

namespace VG.Impl.Dsa.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrub)

/-- `vg_dsa_derive_key`. -/
def deriveKey : Prog isa := scrub 32 0 Derive.derive

/-- `vg_dsa_validate_private_key`. -/
def validatePrivateKey : Prog isa := scrub 32 0 PrevalidatedSign.validate

/-- `vg_dsa_sign_random_prevalidated`. -/
def randomSignPrevalidated : Prog isa := scrub 32 192 PrevalidatedSign.randomSign

/-- `vg_dsa_generate_key`. -/
def generateKey : Prog isa := scrub 32 192 Generate.code

/-- `vg_dsa_validate_public_key`. -/
def validatePublicKey : Prog isa := scrub 32 0 Prevalidated.validate

/-- `vg_dsa_verify_prevalidated`. -/
def verifyPrevalidated : Prog isa := scrub 32 0 Prevalidated.verify

/-- `vg_dsa_parameter_search_init`. -/
def parameterInit : Prog isa := scrub 32 0 ParameterSearch.init

/-- The parameter search's width `(pLen, qLen)`, hashing with `G`, testing
with the probable-prime functions over the round `round` (named with
`suffix`), and checking the domain with `vg_dsa_check_parameters`. -/
def geo (pLen qLen : Nat) (G : ParameterSearch.Hash) (suffix : String) (round : Prog isa) :
    ParameterSearch.Geo where
  pLen := pLen
  qLen := qLen
  G := G
  qName := s!"vg_dsa_probable_prime_{8 * qLen}" ++ suffix
  qCode := ProbablePrime.code (8 * qLen) ("vg_miller_rabin_round" ++ suffix) round
  pName := s!"vg_dsa_probable_prime_{8 * pLen}" ++ suffix
  pCode := ProbablePrime.code (8 * pLen) ("vg_miller_rabin_round" ++ suffix) round
  checkName := "vg_dsa_check_parameters"
  checkCode := Params.checkParameters

/-- The parameter search over its three widths, with the round `round`. -/
def parameterSearchBody (suffix : String) (round : Prog isa) : Prog isa :=
  ParameterSearch.code (geo 128 20 ParameterSearch.sha1 suffix round)
    (geo 256 32 ParameterSearch.sha256 suffix round) (geo 384 32 ParameterSearch.sha256 suffix round)

/-- `vg_dsa_parameter_search` as emitted: the search, then its cleanup. -/
def parameterSearch (suffix : String) (round : Prog isa) : Prog isa :=
  scrub 32 512 (parameterSearchBody suffix round)

end VG.Impl.Dsa.RISCV64.Fn
