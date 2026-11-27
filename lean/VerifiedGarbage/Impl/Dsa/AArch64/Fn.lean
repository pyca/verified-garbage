module

public import VerifiedGarbage.Impl.Dsa.AArch64.GenerateKey
public import VerifiedGarbage.Impl.Dsa.AArch64.Generate
public import VerifiedGarbage.Impl.Dsa.AArch64.PrevalidatedSign
public import VerifiedGarbage.Impl.Dsa.AArch64.Prevalidated
public import VerifiedGarbage.Impl.Scrub.AArch64.Scrub
public import VerifiedGarbage.Impl.Scrub.AArch64.Writes
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Entry
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PublicRound
public import VerifiedGarbage.Impl.Dsa.AArch64.Generator
public import VerifiedGarbage.Impl.Dsa.AArch64.ProbablePrime
public import VerifiedGarbage.Impl.MillerRabin.AArch64.Caller

/-!
# DSA's functions over an arithmetic backend on AArch64, as emitted

Each function is its code with the Montgomery multiplication `mul`, then its
cleanup (`Impl.Scrub.AArch64.scrubAll`): the registers `clear` are cleared,
but the 32 bits of its result, and the stack it uses, the backend's `stack`
bytes and, for the two functions that draw random numbers, their frame of
256, is zeroed, so that it returns without secret residue.

`vg_dsa_parameter_search` is its code with two hash functions and the
arithmetic of a Miller–Rabin round's implementation, then its cleanup
(`Impl.Scrub.AArch64.scrubOf`), which clears the registers the code may
write, which differ with its hash functions.
-/

@[expose] public section

namespace VG.Impl.Dsa.AArch64.Fn

open VG.AArch64
open VG.Impl.Scrub.AArch64 (Clear scrubAll)

/-- The registers the functions clear: those their code may write, with any
backend, of the registers the calling convention does not preserve. -/
def clear : Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
   [.v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v31],
   []⟩

/-- `vg_dsa_random_sign_prevalidated`, calling its signer as the internal
function `signer`. -/
def randomSignPrevalidated (signer : String) (mul : Nat → Nat → Nat → Prog isa) (stack : Nat) : Prog isa :=
  scrubAll (stack + 256) 32 clear (RandomSign.code signer (PrevalidatedSign.sign mul))

/-- `vg_dsa_validate_private_key`. -/
def validatePrivateKey (mul : Nat → Nat → Nat → Prog isa) (stack : Nat) : Prog isa :=
  scrubAll stack 32 clear (PrevalidatedSign.validate mul)

/-- `vg_dsa_validate_public_key`. -/
def validatePublicKey (mul : Nat → Nat → Nat → Prog isa) (stack : Nat) : Prog isa :=
  scrubAll stack 32 clear (Prevalidated.validate mul)

/-- `vg_dsa_verify_prevalidated`. -/
def verifyPrevalidated (mul : Nat → Nat → Nat → Prog isa) (stack : Nat) : Prog isa :=
  scrubAll stack 32 clear (Prevalidated.verify mul)

/-- `vg_dsa_generate_key`, calling the check of the parameters and the
derivation as the internal functions `check` and `derive`. -/
def generateKey (check derive : String) (mul : Nat → Nat → Nat → Prog isa) (stack : Nat) : Prog isa :=
  scrubAll (stack + 256) 32 clear
    (GenerateKey.code check derive (Generate.checkParameters mul) (Generate.deriveChecked mul))

/-- `vg_dsa_derive_key`. -/
def deriveKey (mul : Nat → Nat → Nat → Prog isa) (stack : Nat) : Prog isa :=
  scrubAll stack 32 clear (Generate.deriveKey mul)

/-- `vg_dsa_generator_<bits>`, the generator stage for a p of `pLen` bytes
with the multiplication `mm`, as `vg_dsa_parameter_search` calls it. -/
def generator (suffix : String) (mm : Nat → Nat → Nat → Prog isa) (pLen : Nat) : Prog isa :=
  .call (s!"vg_dsa_generator_{8 * (Generator.layout pLen).pLen}" ++ suffix) (Generator.code mm pLen)

/-- `vg_dsa_probable_prime_<bits>`, the test with the multiplication `mm`,
calling the round for public candidates, whose multiplication is `rmm`, as
`vg_dsa_parameter_search` calls it. -/
def probablePrime (suffix : String) (mm rmm : Nat → Nat → Nat → Prog isa) (bits : Nat) : Prog isa :=
  .call (s!"vg_dsa_probable_prime_{(ProbablePrime.layout bits).bits}" ++ suffix)
    (ProbablePrime.code bits mm
      [Impl.MillerRabin.AArch64.Caller.call ("vg_dsa_miller_rabin_round" ++ suffix) (Generation.publicRound rmm)])

/-- `vg_dsa_parameter_search` as emitted: the search with the SHA-1 `G1`, the
SHA-256 `G256` and the functions above, then its cleanup over the 768 bytes
of stack it uses. -/
def parameterSearch (G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash) (suffix : String)
    (mm rmm : Nat → Nat → Nat → Prog isa) : Prog isa :=
  Impl.Scrub.AArch64.scrubOf 768 32
    (Generation.code G1 G256 (generator suffix mm) (probablePrime suffix mm rmm))

end VG.Impl.Dsa.AArch64.Fn
