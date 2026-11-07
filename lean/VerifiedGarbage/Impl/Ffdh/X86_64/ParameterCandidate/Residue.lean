module

public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Candidate

/-! # FFDH parameter candidates on x86-64: small public remainders -/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate

/-- One word of `fold`: word `w − 1 − r14` of aN into RSI, modulo
2^64 − 1: an addition whose carry is added back (`adc rsi, 0`), which
cannot carry again. -/
def foldWord : List Instr :=
  [.mov .rax (.reg .r12), .alu .sub .rax (.imm 1), .alu .sub .rax (.reg .r14),
    .alu .add .rsi (.mem (ix .r8 .rax)), .alu .adc .rsi (.imm 0)]

/-- RSI := a word congruent to the candidate in aN modulo 2^64 − 1, the sum
of its words with end-around carries (2^64 ≡ 1). R8 keeps aN's base. -/
def fold : Prog isa := .seq
  (.block [.mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aN))), .mov32 .rsi (.imm 0),
    .mov32 .r14 (.imm 0)])
  (.loop (.seq (.block foldWord) (.block [.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)])) .ne)

/-- RSI := RSI mod 255 (255 divides 2^64 − 1), bit by bit as RSA's `modWord`. -/
def reduce255 : Prog isa := .seq
  (.block [.mov .rdx (.reg .rsi), .mov32 .rsi (.imm 0), .mov32 .rbx (.imm 255), .mov32 .r13 (.imm 64)])
  (.loop (.block (modBit ++ [.alu .sub .r13 (.imm 1)])) .ne)

/-- One value of `member`: RAX := RCX (1) if RSI is `v`. -/
def memberStep (v : Nat) : List Instr :=
  [.alu .cmp .rsi (.imm (BitVec.ofNat 32 v)), .cmov .e .rax (.reg .rcx)]

/-- RAX := 1 if the remainder in RSI is one of `vals`, else 0, without a branch. -/
def memberFlag (vals : List Nat) : List Instr :=
  [.mov32 .rax (.imm 0), .mov32 .rcx (.imm 1)] ++ vals.flatMap memberStep

/-- ZF iff RAX is 1 and aN's low word, masked by `mask`, is 3. -/
def lowCheck (mask : Nat) : List Instr :=
  [.mov .rdx (.mem (at0 .r8)), .alu .and .rdx (.imm (BitVec.ofNat 32 mask)), .mov32 .rcx (.imm 0),
    .alu .cmp .rdx (.imm 3), .cmov .ne .rax (.reg .rcx), .alu .cmp .rax (.imm 1)]

/-- The remainders modulo 255 = 3 · 5 · 17 of a candidate p ≡ 3 mod 8 that
has generator 2's PKCS #3 congruence (p ≡ 11 mod 24: p ≡ 2 mod 3) and that
neither 5 nor 17 rules out for p or q = (p − 1)/2 (p mod 5 and p mod 17 at
least 2). -/
def allowed2 : List Nat :=
  [2, 8, 14, 23, 29, 32, 38, 44, 47, 53, 59, 62, 74, 77, 83, 89, 92, 98, 104, 107, 113, 122, 128,
    134, 143, 149, 152, 158, 164, 167, 173, 179, 182, 194, 197, 203, 209, 212, 218, 224, 227, 233,
    242, 248, 254]

/-- The remainders modulo 255 of a candidate p ≡ 3 mod 4 (q odd) that has
generator 5's congruence (p ≡ 3 or 7 mod 10: p mod 5 is 2 or 3) and that
neither 3 nor 17 rules out for p or q (p ≡ 2 mod 3, p mod 17 at least 2). -/
def allowed5 : List Nat :=
  [2, 8, 23, 32, 38, 47, 53, 62, 77, 83, 92, 98, 107, 113, 122, 128, 143, 152, 158, 167, 173, 182,
    197, 203, 212, 218, 227, 233, 242, 248]

/-- Generator 2's congruence, with the small primes that q's and p's trial
division would reject anyway: they are rejected here, before the sieve.
One pass over the candidate's words (`fold`), then one word. ZF means
acceptance. -/
def generator2 : Prog isa := .seq fold (.seq reduce255 (.block (memberFlag allowed2 ++ lowCheck (2 ^ 3 - 1))))

/-- Generator 5's congruence, with the small primes that q's and p's trial
division would reject anyway. ZF means acceptance. -/
def generator5 : Prog isa := .seq fold (.seq reduce255 (.block (memberFlag allowed5 ++ lowCheck (2 ^ 2 - 1))))

/-- Select the congruence check for the public generator in rdx (2 or 5). -/
def generatorCheck : Prog isa := .seq (.block [.alu .cmp .rdx (.imm 2)])
  (.ite .e generator2 generator5)

end VG.Impl.Ffdh.X86_64.ParameterCandidate
