module

public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Candidate

/-! # FFDH parameter candidates on x86-64: small public remainders -/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate

/-- Reduce the candidate in aN modulo a small public divisor, using RSA's
bit-at-a-time reduction. The result is in rsi, and memory is untouched. -/
def residue (divisor : Nat) : Prog isa := .seq
  (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 divisor)), .mov .r12 (.mem (hdr sW)),
    .mov .r8 (.mem (hdr (sArr aN))), .mov32 .rsi (.imm 0), .mov32 .r14 (.imm 0)])
  (.loop (.seq modWord (.block [.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)])) .ne)

/-- The PKCS #3 congruence check for generator 2. ZF means acceptance. -/
def generator2 : Prog isa := .seq (residue 24) (.block [.alu .cmp .rsi (.imm 11)])

/-- The PKCS #3 congruence check for generator 5. A remainder modulo 10
is at most 9, so clearing bit 2 maps exactly 3 and 7 to 3. -/
def generator5 : Prog isa := .seq (residue 10)
  (.block [.alu .and .rsi (.imm 11), .alu .cmp .rsi (.imm 3)])

/-- Select the congruence check for the public generator in rdx (2 or 5). -/
def generatorCheck : Prog isa := .seq (.block [.alu .cmp .rdx (.imm 2)])
  (.ite .e generator2 generator5)

end VG.Impl.Ffdh.X86_64.ParameterCandidate
