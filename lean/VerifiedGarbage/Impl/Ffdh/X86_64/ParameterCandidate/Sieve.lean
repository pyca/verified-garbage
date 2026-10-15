module

public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Candidate

/-! # FFDH parameter candidates on x86-64: the specified small-prime sieve -/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.RsaKeyGen
open VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate

/-- Load one packed word of RSA's small-prime table. -/
def sieveLoad : List Instr := extBase aTab .rbx ++
  [.mov .rax (.mem (ix .rbx .r13)), .store (hdr kT1) .rax]

/-- Four consecutive odd primes. The same reductions and loop are used by RSA. -/
def sieveWord : List (Prog isa) := [.block sieveLoad] ++
  trialEntry 0 ++ trialEntry 1 ++ trialEntry 2 ++ trialEntry 3 ++
  [.block [.alu .add .r13 (.imm 1), .mov .rax (.mem (hdr kT0)), .alu .cmp .r13 (.reg .rax)]]

/-- The first 53 odd primes: 13 whole packed words, then the next entry.
The separate candidate oddness check supplies the prime 2. ZF is set iff
none divides the candidate in aN. -/
def sieve : Prog isa := seqs (
  [.block (extBase aTab .rbx ++ tabWrite),
   .block [.mov32 .rax (.imm 13), .store (hdr kT0) .rax, .mov32 .rax (.imm 0),
     .store (hdr kT2) .rax, .mov32 .r13 (.imm 0)],
   .loop (seqs sieveWord) .ne, .block sieveLoad] ++
  trialEntry 0 ++ [.block [.mov .rax (.mem (hdr kT2)), .alu .test .rax (.reg .rax)]])

/-- Check oddness before using the odd-prime sieve. ZF means acceptance. -/
def oddTest : List Instr := [.mov .rax (.mem (hdr (sArr aN))), .mov .rax (.mem (at0 .rax)),
  .alu .and .rax (.imm 1), .alu .cmp .rax (.imm 1)]

def primeCheck : Prog isa := .seq (.block oddTest) (.ite .e sieve (.block []))

end VG.Impl.Ffdh.X86_64.ParameterCandidate
