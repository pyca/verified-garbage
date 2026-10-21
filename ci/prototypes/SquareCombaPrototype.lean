import VerifiedGarbage.Impl.Rsa.X86.RecoverRt
import VerifiedGarbage.TCB.X86.Print
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
open VG.Impl.Rsa.X86.Keys (seqs)
namespace SquareProto
-- Scratch, unproven: product scanning with independent 64-bit sums.
def accum : List Instr := [
  .mop (.movd .mm2 .eax), .mop (.bin .paddq .mm0 (.reg .mm2)),
  .mop (.movd .mm2 .edx), .mop (.bin .paddq .mm1 (.reg .mm2))]
def prod : List Instr := [.mov .eax (.mem (at_ .ecx 0)),
  .mov .edx (.mem (at_ .ebp 0)), .mul .edx] ++ accum

def pairLoop : Prog isa := .loop (.block (prod ++ [
  .alu .add .ecx (.imm 4), .alu .sub .ebp (.imm 4), .alu .cmp .ecx (.reg .ebp)])) .b

def cross : Prog isa := seqs [
  .block (lenTimes .eax 0 ++ [.mov .edx (.reg .esi), .alu .add .edx (.imm 4), .alu .sub .edx (.reg .eax)]),
  .ite .b (.block [.mov .edx (.imm 0)]) (.block []),
  .block [.mov .ecx (.mem argWs), .mov .eax (.mem argA), .alu .add .ecx (.reg .eax),
    .mov .ebp (.reg .ecx), .alu .add .ecx (.reg .edx),
    .alu .add .ebp (.reg .esi), .alu .sub .ebp (.reg .edx), .alu .cmp .ecx (.reg .ebp)],
  .ite .b pairLoop (.block []),
  .block [.mop (.shift .psllq .mm0 1), .mop (.shift .psllq .mm1 1),
    .mov .eax (.reg .esi), .alu .and .eax (.imm 4)],
  .ite .e (.block ([.mov .eax (.reg .esi), .shift .shr .eax 1,
    .mov .edx (.mem argWs), .alu .add .eax (.reg .edx), .mov .edx (.mem argA),
    .alu .add .eax (.reg .edx), .mov .eax (.mem (at_ .eax 0)), .mul .eax] ++ accum)) (.block [])]

def carryIn : List Instr := [
  .mop (.movq .mm2 (.reg .mm3)), .mop (.bin .pand .mm2 (.reg .mm7)),
  .mop (.bin .paddq .mm0 (.reg .mm2)), .mop (.shift .psrlq .mm3 32),
  .mop (.bin .paddq .mm1 (.reg .mm3))]

def redLoop : Prog isa := .loop (.block (prod ++ [
  .alu .add .ecx (.imm 4), .alu .sub .ebp (.imm 4), .alu .cmp .ecx (.reg .ebx)])) .b

def reduction : Prog isa := seqs [
  .block (lenTimes .ebx 0 ++ [.mov .edx (.reg .esi), .alu .add .edx (.imm 4), .alu .sub .edx (.reg .ebx)]),
  .ite .b (.block [.mov .edx (.imm 0)]) (.block []),
  .block [.mov .ecx (.reg .edi), .alu .add .ecx (.imm 52), .alu .add .ecx (.reg .edx),
    .mov .ebp (.mem argWs), .mov .eax (.mem argM), .alu .add .ebp (.reg .eax),
    .alu .add .ebp (.reg .esi), .alu .sub .ebp (.reg .edx),
    .alu .cmp .esi (.reg .ebx)],
  .ite .b (.block [.mov .ebx (.reg .esi)]) (.block []),
  .block [.alu .add .ebx (.reg .edi), .alu .add .ebx (.imm 52), .alu .cmp .ecx (.reg .ebx)],
  .ite .b redLoop (.block []),
  .block ([.mmxStore (sc 20) .mm0] ++ lenTimes .eax 0 ++ [.alu .cmp .esi (.reg .eax)]),
  .ite .b
    (.block (ptr .edx argInv .eax ++ [.mov .edx (.mem (at_ .edx 0)),
      .mov .eax (.mem (sc 20)), .mul .edx,
      .mov .ecx (.reg .edi), .alu .add .ecx (.imm 52), .alu .add .ecx (.reg .esi),
      .store (at_ .ecx 0) .eax, .mov .ebx (.reg .eax)] ++ ptr .ebp argM .edx ++
      [.mov .eax (.mem (at_ .ebp 0)), .mul .ebx] ++ accum))
    (.block [.mov .eax (.mem (sc 20)), .mov .ecx (.reg .edi),
      .alu .add .ecx (.imm 52), .alu .add .ecx (.reg .esi), .store (at_ .ecx 0) .eax])]

def column : Prog isa := seqs [
  .block [.mop (.bin .pxor .mm0 (.reg .mm0)), .mop (.bin .pxor .mm1 (.reg .mm1))],
  cross, .block carryIn, reduction,
  .block ([.mop (.movq .mm3 (.reg .mm0)), .mop (.shift .psrlq .mm3 32),
    .mop (.bin .paddq .mm3 (.reg .mm1)), .alu .add .esi (.imm 4)] ++
    lenTimes .eax 1 ++ [.alu .cmp .esi (.reg .eax)])]

def columns : Prog isa := seqs [
  .block [.mov .esi (.imm 0), .mop (.bin .pxor .mm3 (.reg .mm3)),
    .mov .eax (.imm (-1)), .mop (.movd .mm7 .eax)],
  .loop column .ne,
  .block ([.mov .ebp (.reg .edi), .alu .add .ebp (.imm 52), .alu .add .ebp (.reg .esi),
    .mmxStore (at_ .ebp 0) .mm3] ++ lenTimes .eax 0 ++ [.alu .sub .ebp (.reg .eax)])]

def square : Prog isa := seqs [.block save, .frame .mmxEnter columns .emms,
  subM, .block mask, select, .block restoreRegs]

def dispatch : Prog isa := .seq (.block [.mov .eax (.mem argA), .alu .cmp .eax (.mem argB)])
  (.ite .e square VG.Impl.Mont.X86.Rt.body)

def printFn (name : String) (p : Prog isa) (callee : String := "proto_mont") : String :=
  ".globl " ++ name ++ "\n.p2align 6\n" ++ name ++ ":\n" ++
  "\n".intercalate ((printer.function p).map fun l => match l with
    | .text s => s | .call _ => "call " ++ callee | .sym .. => "ERROR") ++ "\n"
end SquareProto

def main : IO Unit := do
  IO.FS.writeFile "/workspace/scratch/openssl/square-generated.S" (
    ".intel_syntax noprefix\n.text\n" ++
    SquareProto.printFn "proto_baseline" VG.Impl.Rsa.X86.RecoverRt.code ++
    SquareProto.printFn "proto_recover" VG.Impl.Rsa.X86.RecoverRt.code "proto_comba_mont" ++
    SquareProto.printFn "proto_profiled" VG.Impl.Rsa.X86.RecoverRt.code "profile_mont" ++
    SquareProto.printFn "proto_comba_mont" SquareProto.dispatch ++
    SquareProto.printFn "proto_mont" VG.Impl.Mont.X86.Rt.body ++
    ".section .note.GNU-stack,\"\",@progbits\n")
