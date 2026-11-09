module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generate

/-!
# Separate reusable private-key validation from DSA signing on AArch64

`validate` is `vg_dsa_validate_private_key` (Spec/Dsa/PrevalidatedSign.lean):
the domain check's register entry (`Generate.checkFields`), with the nonce
field pointing at x, so that the signer's key checks (`Checks.signingKey`
and `Checks.privateKey`, whose nonce range check is then x's) are every
check signing makes of the key. `sign` is one signing attempt of
`vg_dsa_sign_random_prevalidated`: the signer's program with those two
checks, and their two exponentiations, replaced by rebuilding q−2 and the
nonce's range check; the precondition that the exact key bytes validate
makes the omitted checks' mask true.
-/

@[expose] public section

namespace VG.Impl.Dsa.AArch64.PrevalidatedSign

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64.SignVerify

/-- `vg_dsa_validate_private_key(key, key_len, p_len, q_len, scratch,
scratch_len)`: all arguments in registers, as the domain check's. The
nonce field points at x. -/
def validateEntry : List Instr :=
  ([mov .x11 .x4] : List Instr) ++ Generate.checkFields ++ keyPointers ++
  [.ldr .x .x3 .x11 Field.x.offset, initial .x3 .nonce]

def validate (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block validateEntry, Checks.domainShape,
  .ite (.zero .x .x3) (.block [movi .x0 0])
    (seqs [workspaces, Checks.signingKey mul, Checks.privateKey mul, .block result])]

/-- Rebuild q−2 in this call's workspace and check the nonce's range;
validation is a precondition on the immutable key bytes, never a flag
recovered from scratch. -/
def compute (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  Checks.modulusMinus qWorkspace 2 (Core.scalar qMinusTwo),
  Checks.range qWorkspace Core.nonce,
  Core.sign mul, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true]

def sign (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block signEntry, Checks.domainShape,
  .ite (.zero .x .x3) signFailure (seqs [
    workspaces, compute mul,
    writeScalar r false, writeScalar s true, .block result])]

end VG.Impl.Dsa.AArch64.PrevalidatedSign
