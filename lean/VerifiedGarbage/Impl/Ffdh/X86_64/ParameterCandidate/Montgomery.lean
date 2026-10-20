module
public import VerifiedGarbage.Impl.MillerRabin.X86_64.Core


/-! # FFDH parameter candidates on x86-64: Montgomery precomputation -/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.ParameterCandidate

open VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public

/-- RSA's negative-inverse setup, without its whole-word candidate assumption. -/
def prepareHead : List Instr :=
  [.mov .r10 (.mem (hdr (sArr aN))), .mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (at0 .r10))] ++ minv ++
  [.store (hdr sMinv) .r15, .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)]

/-- Compute the inverse, the number one, and R² for either candidate. The
selected R² implementation accepts a partially occupied highest word. -/
def prepareR2 (r2 : Prog isa) : Prog isa := seqs [
  .block prepareHead, setWord aOne .rcx, .block [.mov .r10 (.mem (hdr (sArr aN)))], r2]

/-- Preserve the Montgomery encoding of one in the shared round's extra array. -/
def copyR1 : Prog isa := .seq
  (.block ([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aY)))] ++ extBase aR1 .rbx)) copyWords

/-- Subtract the Montgomery encoding of one from the modulus. -/
def negateR1 : Prog isa := .seq
  (.block ([.mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aN)))] ++ extBase aR1 .r10 ++
    extBase aRm1 .rsi ++ [.mov32 .rbp (.imm 0)]))
  (wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .r8 .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)),
    .store (ix .rsi .r14) .rax, cfToRbp])

/-- The number 1 and −1 in Montgomery form, using the shared multiply. -/
def prepareConstants (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (mul aY aR2 aOne) (.seq copyR1 negateR1)

/-- Prepare all the modulus-dependent values required by the shared round. -/
def prepareModulus (mul : Nat → Nat → Nat → Prog isa) (r2 : Prog isa) : Prog isa :=
  .seq (prepareR2 r2) (.seq (prepareConstants mul) (seqs expSetup))

end VG.Impl.Ffdh.X86_64.ParameterCandidate
