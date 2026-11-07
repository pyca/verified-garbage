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

/-- One value of `member`: RAX := RCX (1) if RSI is `v`. -/
def memberStep (v : Nat) : List Instr :=
  [.alu .cmp .rsi (.imm (BitVec.ofNat 32 v)), .cmov .e .rax (.reg .rcx)]

/-- ZF iff the remainder in RSI is one of `vals`, without a branch. -/
def member (vals : List Nat) : List Instr :=
  [.mov32 .rax (.imm 0), .mov32 .rcx (.imm 1)] ++ vals.flatMap memberStep ++ [.alu .cmp .rax (.imm 1)]

/-- The remainders modulo 840 of a candidate p that has generator 2's
PKCS #3 congruence (p ≡ 11 mod 24) and that neither 5 nor 7 rules out for
p or q = (p − 1)/2 (p mod 5 and p mod 7 at least 2). -/
def allowed2 : List Nat :=
  [59, 83, 107, 179, 227, 299, 347, 419, 443, 467, 563, 587, 683, 779, 803]

/-- The remainders modulo 420 of a candidate p that has generator 5's
congruence (p ≡ 3 or 7 mod 10) and that 2, 3 and 7 do not rule out for p
or q = (p − 1)/2 (p ≡ 3 mod 4, p ≡ 2 mod 3, p mod 7 at least 2). -/
def allowed5 : List Nat := [23, 47, 83, 107, 143, 167, 227, 263, 347, 383]

/-- Generator 2's congruence, with the small primes that q's and p's trial
division would reject anyway: they are rejected here, before the sieve.
ZF means acceptance. -/
def generator2 : Prog isa := .seq (residue 840) (.block (member allowed2))

/-- Generator 5's congruence, with the small primes that q's and p's trial
division would reject anyway. ZF means acceptance. -/
def generator5 : Prog isa := .seq (residue 420) (.block (member allowed5))

/-- Select the congruence check for the public generator in rdx (2 or 5). -/
def generatorCheck : Prog isa := .seq (.block [.alu .cmp .rdx (.imm 2)])
  (.ite .e generator2 generator5)

end VG.Impl.Ffdh.X86_64.ParameterCandidate
