module

public import VerifiedGarbage.Impl.Ffdh.X86_64.Domain

/-! # FFDH private-key validation on x86-64 -/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.Domain.CheckPrivate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open Crt (ws stk leave loadArr)

/-- `(domain, domain_len, p_len, y, y_len, x, x_len, scratch, scratch_len)`. -/
def entry : List Instr :=
  [.mov .rax (.mem (stk 2)), .mov .r10 (.mem (stk 1))] ++ save .rax ++
  [.store (ws .rax sDom) .rdi, .store (ws .rax sDomLen) .rsi, .store (ws .rax sK) .rdx,
    .store (ws .rax sY) .rcx, .store (ws .rax sX) .r9, .store (ws .rax sXl) .r10,
    .mov .rdi (.reg .rax)]

/-- The scalar is nonzero and below q, or p-1 when q is absent. All words
are compared, including for rejected scalars. Leaves the inner workspace active. -/
def scalarRange : List (Prog isa) :=
  isNonzero aXm ++ [.block [.store (hdr sF) .rax], .block (leave :: qTest),
    .ite .e (seqs (([.block [enter]] : List (Prog isa)) ++ ltP aXm))
      (seqs (([.block [enter]] : List (Prog isa)) ++ loadArr aY sQ sK ++ ltArr aXm aY)),
    .block andF]

variable (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa)) (r2 : Prog isa)

/-- A power of the checked generator is already in the optional q subgroup.
Check its range and equality to the imported public value without branching. -/
def tail : List (Prog isa) :=
  [r2] ++ pow mul ex sG sK sX sXl ++ range aY ++ loadArr aXm sY sK ++ eqArr aY aXm ++
    [.block [.alu .and .rax (.mem (hdr sF)), leave]]

def main : Prog isa :=
  seqs (([.block head] : List (Prog isa)) ++ pSetup ++ loadArr aXm sX sXl ++ scalarRange ++
    [.block [.alu .test .rax (.reg .rax)], .ite .e (retInner 2) (seqs (tail mul ex r2))])

def body : Prog isa := .seq (.block (entry ++ domHead)) (.ite .ne (ret 0) (main mul ex r2))

def code : Prog isa := .seq (body mul ex r2) (.block exit)

end VG.Impl.Ffdh.X86_64.Domain.CheckPrivate
