module

public import VerifiedGarbage.Impl.Dsa.AArch64.Core

/-! # Initialization of the parent and linked DSA Montgomery workspaces -/

@[expose] public section

namespace VG.Impl.Dsa.AArch64.SignVerify
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.Layout

def parent : List Instr :=
  ([movi .x12 outerWords, sth .x12 sW, movi .x3 0, sth .x3 sMinv] : List Instr) ++ setBases

def child (offset : Nat) (modulus : Operand) : Prog isa := seqs [
  .block (Core.operand arg argLen modulus ++
    ([mov .x1 .x0, ldh .x12 argLen, .addImm .x .x12 .x12 7, .lsr .x .x12 .x12 3] : List Instr) ++
    Core.enter offset ++ ([sth .x12 sW, sth .x1 Crt.sLink] : List Instr) ++ setBases),
  Arithmetic.load aN arg argLen,
  .block (([ldh .x3 (sArr aN), ld .x3 .x3] : List Instr) ++ minv ++
    ([sth .x15 sMinv, Crt.leave] : List Instr))]

def workspaces : Prog isa := seqs [
  .block parent,
  child pWorkspace ⟨.input .p, .pLen⟩,
  child qWorkspace ⟨.input .q, .qLen⟩]

end VG.Impl.Dsa.AArch64.SignVerify
