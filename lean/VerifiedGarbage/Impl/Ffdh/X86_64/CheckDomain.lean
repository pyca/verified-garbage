module

public import VerifiedGarbage.Impl.Ffdh.X86_64.Domain

/-! # FFDH domain validation on x86-64 -/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.Domain.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open Crt (ws leave loadArr zeroArr)

/-- `(domain, domain_len, p_len, scratch, scratch_len)`. -/
def entry : List Instr := save .rcx ++
  [.store (ws .rcx sDom) .rdi, .store (ws .rcx sDomLen) .rsi, .store (ws .rcx sK) .rdx,
    .mov .rdi (.reg .rcx)]

/-- Since p is odd, subtract one from its low word without a borrow. -/
def pMinus1 : List (Prog isa) := [zeroArr aX,
  .block [.mov .rsi (.mem (hdr sDom)), .mov .rcx (.mem (hdr sK)), .mov .rbx (.mem (hdr (sArr aX)))],
  loadBE, .block [.mov .rax (.mem (at0 .rbx)), .alu .sub .rax (.imm 1), .store (at0 .rbx) .rax]]

/-- q is odd and lies strictly between 2 and p-1. -/
def qRange : List (Prog isa) :=
  loadArr aXm sQ sK ++ range aXm ++ isOdd aXm ++
  [.block andF, .block [.alu .test .rax (.reg .rax)]]

variable (mul : Nat → Nat → Nat → Prog isa) (ex : Nat → Nat → List (Prog isa)) (r2 : Prog isa)

/-- After q divides p-1, reinitialize the p workspace and check g^q = 1. -/
def subgroup : List (Prog isa) := [.block [leave]] ++ pSetup ++ [r2] ++
  pow mul ex sG sK sEp sEl ++ isOne aY ++ [.block [leave]]

/-- Reduce p-1 modulo the public q, using RSA's arbitrary-width Montgomery
reduction. Its result is zero exactly when q divides p-1. -/
def divides : List (Prog isa) :=
  [.block [leave]] ++ scan sQ ++ pMinus1 ++ wsSetup sEl ++ [.block [enter]] ++ modSetup sEp sEl ++
  Crt.redc mul aX ++ isZero Crt.aXc ++ [.block [.alu .test .rax (.reg .rax)],
    .ite .e (retInner 0) (seqs (subgroup mul ex r2))]

def withQ : List (Prog isa) := [.block [enter]] ++ qRange ++
  [.ite .e (retInner 0) (seqs (divides mul ex r2))]

/-- Check the generator's range, then the optional subgroup order and relation. -/
def main : Prog isa :=
  seqs ([.block head] ++ pSetup ++ loadArr aXm sG sK ++ rangeTest aXm ++
    [.ite .e (retInner 0) (.seq (.block (leave :: qTest))
      (.ite .e (ret 1) (seqs (withQ mul ex r2))))])

def body : Prog isa := .seq (.block (entry ++ domHead)) (.ite .ne (ret 0) (main mul ex r2))

def code : Prog isa := .seq (body mul ex r2) (.block exit)

end VG.Impl.Ffdh.X86_64.Domain.CheckDomain
