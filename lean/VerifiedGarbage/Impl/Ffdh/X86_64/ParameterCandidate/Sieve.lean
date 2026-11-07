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

/-- Field `j` of the table word in `rax` into `rcx`, multiplied into `rbx`. -/
def productField (j : Nat) : List Instr :=
  [.mov .rcx (.reg .rax), .shift .shr .rcx (16 * j), .alu .and .rcx (.imm 0xFFFF), .imul .rbx .rcx]

/-- `M`, the product of the four primes of the table word in `kT1`, into
`rbx` (below `2^52`), and `−M⁻¹ mod 2^64` into `r15`; then the candidate's
base into `r8`, `w` into `r12` and `acc := 0` into `rbp`. -/
def productHead : List Instr :=
  [.mov .rax (.mem (hdr kT1)), .mov .rbx (.reg .rax), .alu .and .rbx (.imm 0xFFFF)] ++
    productField 1 ++ productField 2 ++ productField 3 ++ minv ++
    [.mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aN))), .mov32 .rbp (.imm 0)]

/-- `acc := (acc + x) 2^(−64) mod M` (below `M + 2`) for the candidate's word
`x` (`r14`), `acc` in `rbp`, `M` in `rbx` and `−M⁻¹ mod 2^64` in `r15`:
Montgomery reduction of `acc + x < M 2^64`, its carry kept in `rcx`. -/
def redc64 : List Instr :=
  [.mov .rsi (.mem (ix .r8 .r14)), .alu .add .rsi (.reg .rbp), .alu .sbb .rcx (.reg .rcx),
    .mov .rax (.reg .rsi), .imul .rax .r15, .mul .rbx, .alu .add .rax (.reg .rsi),
    .alu .adc .rdx (.imm 0), .alu .sub .rdx (.reg .rcx), .mov .rbp (.reg .rdx)]

/-- The candidate reduced modulo the table word's product `M`, once for its
four primes: `acc 2^(64 w) ≡ c (mod M)` into `r8`. -/
def productReduce : List (Prog isa) :=
  [.block productHead, wordLoop 0 redc64, .block [.mov .r8 (.reg .rbp)]]

/-- For entry `j` of the table word in `kT1`, as RSA's `trialEntry` but on
the reduced candidate `acc` in `r8` rather than the candidate: `s` into
`rbx`, `−s⁻¹` into `r15`, `acc` reduced over its two halves, and the mask
of `s ∣ c` or'ed into `kT2`. -/
def accEntry (j : Nat) : List Instr :=
  ([.mov .rbx (.mem (hdr kT1))] : List Instr) ++ (if j = 0 then [] else [.shift .shr .rbx (16 * j)]) ++
    ([.alu .and .rbx (.imm 0xFFFF)] : List Instr) ++ minv ++
    [.mov32 .rbp (.imm 0), .mov32 .rax (.reg .r8)] ++ redc32 ++ [.mov .rax (.reg .r8), .shift .shr .rax 32] ++
    redc32 ++
    [.mov .rax (.reg .rbp), .alu .cmp .rax (.imm 1), .alu .sbb .rdx (.reg .rdx), .alu .xor .rax (.reg .rbx),
      .alu .cmp .rax (.imm 1), .alu .sbb .rcx (.reg .rcx), .alu .or .rdx (.reg .rcx), .alu .or .rdx (.mem (hdr kT2)),
      .store (hdr kT2) .rdx]

/-- Four consecutive odd primes: the candidate reduced once modulo their
product, then each prime's test on that. -/
def sieveWord : List (Prog isa) := [.block sieveLoad] ++ productReduce ++
  [.block (accEntry 0), .block (accEntry 1), .block (accEntry 2), .block (accEntry 3), .block sieveNext]

/-- The count in RAX into `kT0`, the flag cleared, from the table's first word. -/
def sieveStart : List Instr :=
  [.store (hdr kT0) .rax, .mov32 .rax (.imm 0), .store (hdr kT2) .rax, .mov32 .r13 (.imm 0)]

/-- Trial division by the first 512 entries of RSA's table, 1024 above
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
