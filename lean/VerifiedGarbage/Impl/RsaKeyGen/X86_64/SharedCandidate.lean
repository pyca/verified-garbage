module

public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Candidate

/-! # RSA candidate policies parameterized by a prepared Miller–Rabin round -/

@[expose] public section

namespace VG.Impl.RsaKeyGen.X86_64.Candidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64

def mrRoundWith (mul : Nat → Nat → Nat → Prog isa) (body : Prog isa) : List (Prog isa) :=
  mrWitness ++ [mul aXm aX aR2] ++ [body] ++ ([
  .block [.mov32 .rcx (.imm 3), .mov .rax (.mem (hdr kFlag)), .alu .test .rax (.reg .rax)],
  .ite .e (.block [])
    (.block [.mov .rax (.mem (hdr kI)), .alu .add .rax (.imm 1), .store (hdr kI) .rax,
      .mov .rdx (.mem (hdr kU)), .alu .and .rdx (.imm 1), .alu .add .rdx (.mem (hdr kUni)), .store (hdr kUni) .rdx,
      -- `rcx := 4` if `i ≤ 16` or `uniform < checks`, else 1.
      .alu .cmp .rax (.imm 17), .alu .sbb .rcx (.reg .rcx), .alu .cmp .rdx (.mem (hdr kChecks)),
      .alu .sbb .rax (.reg .rax), .alu .or .rcx (.reg .rax), .alu .and .rcx (.imm 3), .alu .add .rcx (.imm 1)]),
  .block [.store (hdr kStat) .rcx]] : List (Prog isa))


def millerRabinWith (mul : Nat → Nat → Nat → Prog isa) (body : Prog isa) : List (Prog isa) := [
  .block [.mov32 .rax (.imm 1), .store (hdr kI) .rax, .mov32 .rax (.imm 0), .store (hdr kUni) .rax],
  .loop (seqs [
    .block [.mov .rcx (.mem (hdr kRandLen)), .mov .rax (.mem (hdr kUsed)), .alu .sub .rcx (.reg .rax),
      .mov .rax (.mem (hdr kLen)), .alu .cmp .rcx (.reg .rax)],
    .ite .b (.block [.mov32 .rax (.imm 0), .store (hdr kStat) .rax]) (seqs (mrRoundWith mul body)),
    .block [.mov .rax (.mem (hdr kStat)), .alu .cmp .rax (.imm 4)]]) .e]


def kMainWith (mul : Nat → Nat → Nat → Prog isa) (body : Prog isa) : Prog isa :=
  seqs (loadC ++ closeCheck ++ ([.ite .ne (finUsed 2) (seqs (trial ++
    ([.ite .ne (finUsed 3) (seqs (gcdCheck ++
      ([.ite .ne (finUsed 3) (seqs (montSetup mul ++ expSetup ++ millerRabinWith mul body ++
        [mrResult]))] : List (Prog isa))))] : List (Prog isa))))] : List (Prog isa)))


def codeWith (mul : Nat → Nat → Nat → Prog isa) (body : Prog isa) : Prog isa :=
  seqs [.block kEntry, zeroOut,
    .block [.mov .rax (.mem (hdr kRandLen)), .mov .rcx (.mem (hdr kLen)), .alu .cmp .rax (.reg .rcx)],
    .ite .b finNone (kMainWith mul body)]

end VG.Impl.RsaKeyGen.X86_64.Candidate
