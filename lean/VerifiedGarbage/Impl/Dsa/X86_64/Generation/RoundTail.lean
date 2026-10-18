module

public import VerifiedGarbage.Impl.MillerRabin.X86_64.Layout

/-! # The shared RSA blinded-round completion policy, with caller-supplied checks -/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate

def roundTail : Prog isa := seqs [
  .block [.mov32 .rcx (.imm 3), .mov .rax (.mem (hdr kFlag)), .alu .test .rax (.reg .rax)],
  .ite .e (.block [])
    (.block [.mov .rax (.mem (hdr kI)), .alu .add .rax (.imm 1), .store (hdr kI) .rax,
      .mov .rdx (.mem (hdr kU)), .alu .and .rdx (.imm 1), .alu .add .rdx (.mem (hdr kUni)), .store (hdr kUni) .rdx,
      -- `rcx := 4` if `i ≤ 16` or `uniform < checks`, else 1.
      .alu .cmp .rax (.imm 17), .alu .sbb .rcx (.reg .rcx), .alu .cmp .rdx (.mem (hdr kChecks)),
      .alu .sbb .rax (.reg .rax), .alu .or .rcx (.reg .rax), .alu .and .rcx (.imm 3), .alu .add .rcx (.imm 1)]),
  .block [.store (hdr kStat) .rcx]]

end VG.Impl.Dsa.X86_64.Generation
