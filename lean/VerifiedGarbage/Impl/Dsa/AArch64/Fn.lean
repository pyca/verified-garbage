module

public import VerifiedGarbage.Impl.Dsa.AArch64.GenerateKey
public import VerifiedGarbage.Impl.Dsa.AArch64.Generate
public import VerifiedGarbage.Impl.Dsa.AArch64.PrevalidatedSign
public import VerifiedGarbage.Impl.Dsa.AArch64.Prevalidated
public import VerifiedGarbage.Impl.Residue.AArch64.Scrub

/-!
# DSA's functions over an arithmetic backend on AArch64, as emitted

Each function is its code with the Montgomery multiplication `mul`, then its
cleanup (`Impl.Residue.AArch64.scrubAll`): the registers `clear` are cleared,
but the 32 bits of its result, and the stack it uses, the backend's `stack`
bytes and, for the two functions that draw random numbers, their frame of
256, is zeroed, so that it returns without secret residue.
-/

@[expose] public section

namespace VG.Impl.Dsa.AArch64.Fn

open VG.AArch64
open VG.Impl.Residue.AArch64 (Clear scrubAll)

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

end VG.Impl.Dsa.AArch64.Fn
