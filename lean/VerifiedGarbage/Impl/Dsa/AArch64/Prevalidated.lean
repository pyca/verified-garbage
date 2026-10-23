module

public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify

/-! # Separate reusable public-key validation from DSA signature verification -/

@[expose] public section

namespace VG.Impl.Dsa.AArch64.Prevalidated
open VG VG.AArch64 VG.Impl.Dsa.Layout
open VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public

/-- Six register arguments: key, key length, p length, q length, scratch,
scratch length. No signature or digest is accessed by the validation program. -/
def validateEntry : List Instr :=
  ([mov .x11 .x4, movi .x6 0, movi .x7 0] : List Instr) ++
    SignVerify.verifyFields ++ SignVerify.keyPointers

def validate (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block validateEntry, Checks.domainShape,
  .ite (.zero .x .x3) (.block [movi .x0 0])
    (seqs [SignVerify.workspaces, Checks.publicKey mul, .block SignVerify.result])]

/-- Rebuild q−2 in this call's workspace; validation is a precondition on the
immutable key bytes, never a flag recovered from scratch. -/
def compute (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  Checks.modulusMinus qWorkspace 2 (Core.scalar qMinusTwo),
  Checks.range qWorkspace Core.signatureR, Checks.range qWorkspace Core.signatureS,
  Core.verify mul, Checks.equal (Core.scalar u) Core.signatureR]

def verify (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block SignVerify.verifyEntry, Checks.domainShape,
  .ite (.zero .x .x3) (.block [movi .x0 0])
    (seqs [SignVerify.workspaces, compute mul, .block SignVerify.result])]

end VG.Impl.Dsa.AArch64.Prevalidated
