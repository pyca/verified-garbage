module

public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Candidate

/-! # FFDH parameter candidates on x86-64: RSA's trial division -/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.RsaKeyGen
open VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate

/-- Load one packed word of RSA's small-prime table. -/
def sieveLoad : List Instr := extBase aTab .rbx ++
  [.mov .rax (.mem (ix .rbx .r13)), .store (hdr kT1) .rax]

/-- The next word, and the loop's exit test: ZF iff the words are done or one
of the primes so far divides the candidate (`kT2` all ones), without a
branch: `(count − r13) & ~kT2`. The candidate is public (it is the tape's),
so the sieve may stop at its first divisor. -/
def sieveNext : List Instr :=
  [.alu .add .r13 (.imm 1), .mov .rax (.mem (hdr kT0)), .alu .sub .rax (.reg .r13),
    .mov .rcx (.mem (hdr kT2)), .alu .xor .rcx (.imm (BitVec.ofInt 32 (-1))), .alu .and .rax (.reg .rcx)]

/-- Four consecutive odd primes, with RSA's reductions. -/
def sieveWord : List (Prog isa) := [.block sieveLoad] ++
  trialEntry 0 ++ trialEntry 1 ++ trialEntry 2 ++ trialEntry 3 ++ [.block sieveNext]

/-- The count in RAX into `kT0`, the flag cleared, from the table's first word. -/
def sieveStart : List Instr :=
  [.store (hdr kT0) .rax, .mov32 .rax (.imm 0), .store (hdr kT2) .rax, .mov32 .r13 (.imm 0)]

/-- RSA's trial division by the first 512 entries of its table, 1024 above
1024 bits (`Spec.RsaKeyGen.obviouslyComposite`), as RSA's `trial`, but with
the count chosen by the requested width in RDX (p's, for q as well), and
stopping after the first word of the table with a divisor. The separate
candidate oddness check supplies the prime 2. ZF is set iff none divides the
candidate in aN (`sieve`). -/
def sievePrefix : Prog isa := seqs
  [.block (extBase aTab .rbx ++ tabWrite ++ [.mov32 .rax (.imm 128), .alu .cmp .rdx (.imm 1025)]),
   .ite .b (.block []) (.block [.mov32 .rax (.imm 256)]),
   .block sieveStart]

def sieveTail : List Instr := [.mov .rax (.mem (hdr kT2)), .alu .test .rax (.reg .rax)]

def sieve : Prog isa := .seq sievePrefix (.seq (.loop (seqs sieveWord) .ne) (.block sieveTail))

/-- The table, and a count of `n` of its words. -/
def sievePrefixN (n : Nat) : Prog isa :=
  .block (extBase aTab .rbx ++ tabWrite ++ [.mov32 .rax (.imm (BitVec.ofNat 32 n))] ++ sieveStart)

/-- The words of the table `sieveFirst` divides by: its first 64 primes. -/
def firstWords : Nat := 16

/-- The sieve by the table's first `firstWords` words only, stopping at the
first divisor: a cheap test of p before q's whole sieve. ZF is set iff none
divides the candidate in aN. -/
def sieveFirst : Prog isa := .seq (sievePrefixN firstWords) (.seq (.loop (seqs sieveWord) .ne) (.block sieveTail))

/-- Check oddness before using the odd-prime sieve. ZF means acceptance. -/
def oddTest : List Instr := [.mov .rax (.mem (hdr (sArr aN))), .mov .rax (.mem (at0 .rax)),
  .alu .and .rax (.imm 1), .alu .cmp .rax (.imm 1)]

end VG.Impl.Ffdh.X86_64.ParameterCandidate
