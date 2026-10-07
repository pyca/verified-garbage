import VerifiedGarbage.Impl.Bignum.X86_64

/-! Compare eight limbs per loop iteration, carrying the borrow in CF between
limbs. Lengths not divisible by eight retain the single-limb loop. -/
namespace VG.Impl.Rsa.X86_64.Compare8
open VG VG.X86_64 VG.Impl.Bignum.X86_64

def one (i : Nat) : List Instr :=
  [.mov .rax (.mem (ix .rbx .r14 (8*i))), .alu .sbb .rax (.mem (ix .r10 .r14 (8*i)))]

def words (i n : Nat) : List Instr :=
  match n with
  | 0 => []
  | n+1 => one i ++ words (i+1) n

def block8 : List Instr := [cfFromRbp] ++ words 0 8 ++
  [cfToRbp,.alu .add .r14 (.imm 8),.alu .cmp .r14 (.reg .r12)]

def loop8 : Prog isa := .seq (.block [.mov32 .r14 (.imm 0)]) (.loop (.block block8) .ne)

def code : Prog isa :=
  .seq (.block [.mov .rax (.reg .r12),.alu .and .rax (.imm 7),.alu .cmp .rax (.imm 0)])
    (.ite .e loop8
      (wordLoop 0 [cfFromRbp,.mov .rax (.mem (ix .rbx .r14)),.alu .sbb .rax (.mem (ix .r10 .r14)),cfToRbp]))
end VG.Impl.Rsa.X86_64.Compare8
