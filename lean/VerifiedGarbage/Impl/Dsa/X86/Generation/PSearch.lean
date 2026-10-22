module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.PAttempt

/-! A bounded modulus search retains the shared witness cursor across candidate retries. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)

def pIndex : Nat := Dsa.Generation.Layout.packed + 532

def pSearchInit : List Instr := setHeader pIndex 0 ++ setHeader candidateOffset 1

def pSearchStatusCmp : List Instr :=
  [.mov .eax (.mem (sc primeStatus)), .alu .cmp .eax (.imm 3)]

def pSearchAdvanceHead (limit stride : Nat) : List Instr :=
  [.mov .eax (.mem (sc pIndex)), .alu .add .eax (.imm 1), .store (sc pIndex) .eax,
   .mov .ecx (.mem (sc candidateOffset)), .alu .add .ecx (.imm (BitVec.ofNat 32 stride)),
   .store (sc candidateOffset) .ecx, .alu .cmp .eax (.imm (BitVec.ofNat 32 limit))]

def pSearchAdvance (limit stride : Nat) : Prog isa :=
  .seq (.block (pSearchAdvanceHead limit stride))
    (.ite .b (.block (setHeader primeStatus 3)) (.block (setHeader primeStatus 2)))

def pSearchIteration (body : Prog isa) (limit stride : Nat) : Prog isa :=
  .seq body (.seq (.block pSearchStatusCmp)
    (.seq (.ite .e (pSearchAdvance limit stride) (.block [])) (.block pSearchStatusCmp)))

def primeSearch (H : Hash) (name : String) (code : Prog isa) (seedLen n : Nat) : Prog isa :=
  let stride := (64 * n - 1) / (8 * H.D) + 1
  .seq (.block pSearchInit)
    (.loop (pSearchIteration (pAttempt H name code seedLen n) (256 * n) stride) .e)

end VG.Impl.Dsa.X86.Generation
