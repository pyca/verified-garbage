module

public import VerifiedGarbage.Impl.Rsa.X86_64.Keys
public import VerifiedGarbage.Impl.Rsa.X86_64.CheckKeyCore

/-! # Reusing the normalized word reducer during CRT-key validation

The original eight-array workspace remains intact. A second workspace starts
at array 8, within the caller's existing scratch allocation. It receives the
product and modulus, and returns only the remainder to the original array 6.
-/

@[expose] public section

namespace VG.Impl.Rsa.X86_64.WordValidation

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64

/-- Public size and modulus pointer before the common-layout guard. -/
def guardHead : List Instr :=
  [.mov .r12 (.mem (hdr sK)), .alu .add .r12 (.imm 7), .shift .shr .r12 3,
    .mov .rdx (.mem (hdr sN))]

def guardTail : List Instr :=
  [.mov .rax (.reg .r12), .alu .and .rax (.imm 1),
    .mov .rcx (.reg .r12), .shift .shl .rcx 3, .alu .xor .rcx (.mem (hdr sK)), .alu .or .rax (.reg .rcx),
    .mov .rcx (.mem (hdr CheckKey.sPlen)), .shift .shl .rcx 1, .alu .xor .rcx (.mem (hdr sK)), .alu .or .rax (.reg .rcx),
    .mov .rcx (.mem (hdr CheckKey.sPlen)), .alu .xor .rcx (.mem (hdr CheckKey.sQlen)), .alu .or .rax (.reg .rcx),
    .movzx8 .rcx { base := .rdx }, .shift .shr .rcx 7, .alu .xor .rcx (.imm 1), .alu .or .rax (.reg .rcx)]

def choice (fast slow : Prog isa) : Prog isa :=
  .seq (.block guardHead) (.seq (.block guardTail) (.ite .e fast slow))

/-- Enter the second workspace, retaining the two original input pointers. -/
def enterLoad : List Instr :=
  [.mov .rsi (.mem (hdr (sArr aAcc))), .mov .r10 (.mem (hdr (sArr CheckKey.aM))),
    .mov .r12 (.mem (hdr sW)),
    .mov .r9 (.reg .r12), .alu .add .r9 (.imm 2), .shift .shl .r9 3]

def enterHeader : List Instr :=
  [.store (hdr sW) .r12, .store (hdr Keys.sStride) .r9]

def enter : List Instr := enterLoad ++ Keys.base 8 .rdi ++ enterHeader

def productSetup : List Instr := Keys.base WordDivide.aD .rbx

def modulusSetup : List Instr := [.mov .rsi (.reg .r10)] ++ Keys.base WordDivide.aM .rbx

/-- Recover the original base using only public workspace dimensions. -/
def restore : List Instr :=
  [.mov .rax (.reg .r9), .shift .shl .rax 3, .alu .add .rax (.imm (BitVec.ofNat 32 256)),
    .alu .sub .rdi (.reg .rax)]

/-- Pin the result source, restore the original base and compute its destination. -/
def resultSetup : List Instr := Keys.ws ++ Keys.base WordDivide.aR .rsi ++ restore ++ Keys.base CheckKey.aR .rbx

def inputs : Prog isa := seqs [
  .block enter, .block setBases, .block productSetup, copyWords, .block modulusSetup, copyWords]

def code : Prog isa := .seq inputs (seqs [
  .seq (.block WordDivide.normalize) WordDivide.code,
  .block resultSetup, copyWords])

/-- The final CRT-key check, with a word remainder for the product. -/
def qinv : Prog isa := seqs (
  CheckKey.loadNum CheckKey.aM CheckKey.sP CheckKey.sPlen ++
  CheckKey.loadNum aX CheckKey.sQI CheckKey.sPlen ++ CheckKey.ltMask aX CheckKey.aM ++
  CheckKey.loadNum CheckKey.aR CheckKey.sQ CheckKey.sQlen ++ CheckKey.mulXR ++ [code] ++ CheckKey.eqOne)

end VG.Impl.Rsa.X86_64.WordValidation
