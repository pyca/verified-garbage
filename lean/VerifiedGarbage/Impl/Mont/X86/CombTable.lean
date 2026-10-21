module

public import VerifiedGarbage.Impl.Mont.X86.Window
public import VerifiedGarbage.Impl.Mont.X86.ContextSquares
public import VerifiedGarbage.Spec.Rsa.FixedBaseComb

/-! Shared five-tooth comb table operations over the x86 Montgomery workspace. -/

@[expose] public section
namespace VG.Impl.Mont.X86.Comb
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

def seq (xs : List (Prog isa)) : Prog isa := xs.foldr .seq (.block [])
def imm (n : Nat) : Src := .imm (BitVec.ofNat 32 n)

/-- Copy one word per iteration between the two public pointers. -/
def copyLoop (src dst : MemOp) : Prog isa :=
  .loop (.block [.mov .eax (.mem src), .store dst .eax,
    .alu .add .ecx (imm 4), .alu .add .ebp (imm 4), .alu .sub .ebx (imm 1)]) .ne

/-- Public entry pointer and shared copy-loop counters. -/
def copySetup (n tab : Nat) (index : Src) : Prog isa :=
  .block [.mov .eax index, .mov .edx (imm (8*n)), .mul .edx,
    .alu .add .eax (.reg .edi), .alu .add .eax (imm tab),
    .mov .ecx (.reg .eax), .mov .ebp (.reg .edi), .mov .ebx (imm (2*n))]

/-- Direct table selection is used only for public exponents. -/
def publicSelect (n tab dst : Nat) : Prog isa :=
  .seq (copySetup n tab (.mem (sc windowOffset))) (copyLoop (at_ .ecx 0) (at_ .ebp dst))

/-- Accumulate one fixed-address table word under its equality mask. -/
def maskedWord (table mask : MemOp) : List Instr :=
  [.mov .eax (.mem table), .alu .and .eax (.mem mask), .alu .or .ebx (.reg .eax)]

/-- One output word of the fixed-address scan, followed by its loop counter. -/
def scanStep (n tab dst entries : Nat) (mask : Nat → MemOp) : List Instr :=
  [.mov .ebx (imm 0)] ++ (List.range entries).flatMap (fun j =>
    maskedWord (at_ .ebp (entry n tab j)) (mask j)) ++ [
    .store (at_ .ebp dst) .ebx, .alu .add .ebp (imm 4),
    .mov .eax (.reg .edi), .alu .add .eax (imm (8*n)), .alu .cmp .ebp (.reg .eax)]

def scan (n tab dst entries : Nat) (mask : Nat → MemOp) : Prog isa :=
  .seq (.block [.mov .ebp (.reg .edi)])
    (.loop (.block (scanStep n tab dst entries mask)) .ne)

/-- Fixed-address masked table scan, accumulating each output word in a
register. Masks are computed once per window, without secret indexing. -/
def wordSelectBody (n tab dst : Nat) (entries : Nat) (mask : Nat → MemOp) : Prog isa :=
  .seq (.block ((List.range entries).flatMap fun j => windowMask j ++ [.store (mask j) .ecx]))
    (scan n tab dst entries mask)

/-- The first Montgomery temporary holds all 32 masks. It is unused during
selection and overwritten by the following multiply; n ≥ 16 provides 128 bytes. -/
def wordSelect (n tab dst : Nat) : Prog isa :=
  wordSelectBody n tab dst 32 (fun j => sc (slot n 1+4*j))

def copyToComb (n tab src : Nat) : Prog isa :=
  .seq (copySetup n tab (.reg .esi)) (copyLoop (at_ .ebp src) (at_ .ecx 0))

def buildStart (n context : Nat) : Prog isa :=
  let tab := context + 16*n
  seq [copyWords n (slot n 0) context, copyWords n (slot n 4) (context+8*n),
    encodeBase n, copyWords n (slot n 6) tab, copyWords n (slot n 5) (entry n tab 1)]

def columnAdvance : Prog isa :=
  .block [.mov .esi (.mem (sc 28)), .alu .add .esi (.reg .esi), .store (sc 28) .esi]

def columnStep (n d tab : Nat) : Prog isa :=
  seq [repeatSquares n 5 d, columnAdvance,
    copyToComb n tab (slot n 5), .block [.alu .cmp .esi (imm 16)]]

def buildColumns (n e context : Nat) : Prog isa :=
  .seq (.block [.mov .eax (imm 1), .store (sc 28) .eax])
    (.loop (columnStep n (VG.Spec.Rsa.FixedBaseComb.rows (32*e)) (context+16*n)) .ne)

def subsetIndices : Prog isa :=
  .block [.mov .eax (imm 0), .alu .sub .eax (.reg .esi), .alu .and .eax (.reg .esi),
    .store (sc 28) .eax, .mov .edx (.reg .esi), .alu .sub .edx (.reg .eax), .store (sc windowOffset) .edx]

def subsetLow : Prog isa :=
  .block [.mov .eax (.mem (sc 28)), .store (sc windowOffset) .eax]

def subsetStep (n tab : Nat) : Prog isa :=
  seq [subsetIndices, publicSelect n tab (slot n 6), subsetLow,
    publicSelect n tab (slot n 5),
    Dynamic.mul (contextMod n) 0 (slot n 2) (slot n 7) (slot n 6) (slot n 5),
    copyToComb n tab (slot n 7), .block [.alu .add .esi (imm 1), .alu .cmp .esi (imm 32)]]

def buildSubsets (n context : Nat) : Prog isa :=
  .seq (.block [.mov .esi (imm 1)]) (.loop (subsetStep n (context+16*n)) .ne)

def combBuild (n e context : Nat) : Prog isa :=
  seq [buildStart n context, buildColumns n e context, buildSubsets n context]

end VG.Impl.Mont.X86.Comb
