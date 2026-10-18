module

public import VerifiedGarbage.Impl.Bignum.X86_64

/-! # Bounded native p-candidate search controller

A separate three-word control block holds the attempt counter, seed offset,
and status. The candidate body returns 0 for exhausted witnesses, 1 for an
accepted candidate, or 3 to continue. Status 2 means all 4L attempts failed.
The body restores rdi to this block; arithmetic and hashing use other frames.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64

def pSearchInit : List Instr :=
  [.mov32 .rax (.imm 0), .store (hdr 0) .rax,
   .mov32 .rax (.imm 1), .store (hdr 1) .rax]

def pSearchAdvanceHead (limit stride : Nat) : List Instr :=
  [.mov .rax (.mem (hdr 0)), .alu .add .rax (.imm 1), .store (hdr 0) .rax,
   .mov .rcx (.mem (hdr 1)), .alu .add .rcx (.imm (BitVec.ofNat 32 stride)), .store (hdr 1) .rcx,
   .alu .cmp .rax (.imm (BitVec.ofNat 32 limit))]

def pSearchStatus (status : Nat) : List Instr :=
  [.mov32 .rax (.imm (BitVec.ofNat 32 status)), .store (hdr 2) .rax]

def pSearchAdvance (limit stride : Nat) : Prog isa :=
  .seq (.block (pSearchAdvanceHead limit stride))
    (.ite .b (.block (pSearchStatus 3)) (.block (pSearchStatus 2)))

def pSearchStatusCmp : List Instr :=
  [.mov .rax (.mem (hdr 2)), .alu .cmp .rax (.imm 3)]

def pSearchIteration (body : Prog isa) (limit stride : Nat) : Prog isa := seqs [
  body, .block pSearchStatusCmp,
  .ite .e (pSearchAdvance limit stride) (.block []), .block pSearchStatusCmp]

def pSearch (body : Prog isa) (limit stride : Nat) : Prog isa :=
  .seq (.block pSearchInit) (.loop (pSearchIteration body limit stride) .e)

end VG.Impl.Dsa.X86_64.Generation
