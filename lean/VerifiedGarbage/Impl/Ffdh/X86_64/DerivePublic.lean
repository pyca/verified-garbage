module

public import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey

/-!
# FFDH on x86-64: an imported scalar's public value

`vg_ffdh_derive_public`: y zeroed, then x checked as a scalar as
`vg_ffdh_check_private` checks it (2 returned otherwise, the one branch on x);
then `y = g^x mod p` over x's `x_len` bytes, its range as the acceptance
mask (a power of the checked generator is in its subgroup), y written
through key generation's public output (zeros unless accepted), and
`3 − 2 flag` returned, without a branch.
-/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.Domain.DerivePublic

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open Crt (ws stk leave loadArr)

/-- `(y, y_len, domain, domain_len, p_len, x, x_len, scratch, scratch_len)`. -/
def entry : List Instr :=
  [.mov .rax (.mem (stk 2)), .mov .r10 (.mem (stk 1))] ++ save .rax ++
  [.store (ws .rax sDom) .rdx, .store (ws .rax sDomLen) .rcx, .store (ws .rax sK) .r8,
    .store (ws .rax sY) .rdi, .store (ws .rax sX) .r9, .store (ws .rax sXl) .r10,
    .mov .rdi (.reg .rax)]

/-- The range flag in `rax` to status 1 or 3. -/
def status : List Instr :=
  [.shift .shl .rax 1, .mov32 .rdx (.imm 3), .alu .sub .rdx (.reg .rax), .mov .rax (.reg .rdx)]

variable (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa)) (r2 : Prog isa)

/-- The checked generator's power over every byte of x, written as key
generation writes it. -/
def tail : List (Prog isa) :=
  [r2] ++ pow mul ex sG sK sX sXl ++ GenerateKey.publicOutput ++ [.block status]

def main : Prog isa :=
  seqs (([.block head] : List (Prog isa)) ++ pSetup ++ loadArr aXm sX sXl ++ CheckPrivate.scalarRange ++
    [.block [.alu .test .rax (.reg .rax)], .ite .e (retInner 2) (seqs (tail mul ex r2))])

/-- Zeros in y first: the scalar's rejection then leaves them. -/
def body : Prog isa :=
  .seq (.block entry) (.seq (Keys.zeroOut sY sK) (.seq (.block domHead) (.ite .ne (ret 0) (main mul ex r2))))

def code : Prog isa := .seq (body mul ex r2) (.block exit)

end VG.Impl.Ffdh.X86_64.Domain.DerivePublic
