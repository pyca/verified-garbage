module

public import VerifiedGarbage.Impl.Bignum.X86_64

/-! # A five-bit inverse seed for trial division

For odd `m`, `(3*m) xor 2` is an inverse modulo 32. Four Newton steps
then suffice for a 64-bit inverse, instead of five steps from `m`.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.X86_64.Candidate

open VG.X86_64 VG.Impl.Bignum.X86_64

/-- `-m⁻¹ mod 2⁶⁴` in `r15`, with the odd `m` in `rbx`. -/
def trialInverse : List Instr :=
  ([.mov .rcx (.reg .rbx), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rbx),
    .alu .xor .rcx (.imm 2)] : List Instr) ++ newton ++ newton ++ newton ++ newton ++
  ([.mov32 .r15 (.imm 0), .alu .sub .r15 (.reg .rcx)] : List Instr)

end VG.Impl.RsaKeyGen.X86_64.Candidate
