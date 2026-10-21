import VerifiedGarbage.Impl.Rsa.X86.RecoverRt
import VerifiedGarbage.TCB.X86.Print

open VG VG.X86 VG.Impl.Rsa.X86.Keys VG.Impl.Rsa.X86.Recover
open VG.Impl.Mont.X86
open VG.Impl.Rsa.X86.RecoverRt
open VG.Impl.Rsa.X86.KeyRt (copy sel addMod)
namespace Prototype
-- Scratch prototype only: no artifact, no production registration.
def small : Prog isa := seqs [copy nar mXm mX,
  .block [.mov .esi (.mem (sc sCand)), .alu .add .esi (.imm 1)],
  .loop (seqs (addMod nar mXm mXm mX aN aZ mAcc ++
    [.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)]])) .ne]

def bitHead (k : Nat) : List Instr := [.mov .eax (.mem (sc sWin))] ++
  (if k = 0 then [] else [.shift .shr .eax k]) ++
  [.alu .and .eax (.imm 1), .store (sc sBit) .eax]

def hit : List Instr := [.mov .eax (.mem (sc sDone)), .alu .xor .eax (.imm 1),
  .alu .and .eax (.mem (sc sE1)), .mov .ecx (.mem (sc sBit)), .alu .xor .ecx (.imm 1),
  .alu .and .eax (.reg .ecx), .store (sc sLive) .eax,
  .alu .or .eax (.mem (sc sOk)), .alu .and .eax (.reg .ecx), .store (sc sOk) .eax,
  .mov .eax (.mem (sc sDone)), .alu .or .eax (.mem (sc sE1)), .alu .or .eax (.mem (sc sE2)),
  .alu .and .eax (.reg .ecx), .store (sc sDone) .eax]

def tail : List Instr := [.mov .eax (.mem (sc sE1)), .alu .or .eax (.mem (sc sE2)),
  .alu .and .eax (.mem (sc sBit)), .alu .or .eax (.mem (sc sDone)), .store (sc sDone) .eax]

def bitBody (k : Nat) : Prog isa := seqs [
  .block (bitHead k), mmul mX mY mY, eqAt sE1 mX aO, eqAt sE2 mX aNg,
  .block hit, sel nar 0 0 mY sLive,
  small, sel nar mY mX mXm sBit,
  eqAt sE1 mY aO, eqAt sE2 mY aNg, .block tail]

def window : Prog isa := seqs [.block windowTop, shiftUp,
  bitBody 3, bitBody 2, bitBody 1, bitBody 0, .block cntNext]

def cand : Prog isa := seqs [alignStart, .loop alignBody .ne,
  copy nar 0 aZ, .block [.mov .eax (.imm 1), .store (sc sDone) .eax,
    .mov .eax (.imm 0), .store (sc sOk) .eax],
  .block windowCount, .loop window .ne, copy nar mY 0, .block candNext]

def loop : Prog isa := .seq (.block [.mov .eax (.imm 0), .store (sc sCand) .eax]) (.loop cand .ne)
def rest : Prog isa := seqs [copy wid wR wM, mont, loop, fin]
def body : Prog isa := .seq (.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 4))
  (.seq (.block VG.Impl.Bignum.X86.modulusCheck)
    (.ite .e (.seq numbers (.ite .e rest failure)) failure))
def code : Prog isa := seqs [.block entry, body, .block VG.Impl.Bignum.X86.PublicFn.restore]

def fastMac (d : Nat) : List Instr := [
  .mov .eax (.mem (at_ .ecx d)), .mul .edi,
  .alu .add .eax (.mem (at_ .ebp d)), .alu .adc .edx (.imm 0),
  .alu .add .eax (.reg .ebx), .alu .adc .edx (.imm 0),
  .store (at_ .ebp d) .eax, .mov .ebx (.reg .edx)]

def fastRow (x : MemOp) : Prog isa :=
  let R := VG.Impl.Mont.X86.Rt.ptr
  seqs [.block ([.mov .ebx (.imm 0)] ++ R .ecx x .edx ++ VG.Impl.Mont.X86.Rt.lenTimes .esi 0 ++
      [.mov .edi (.mem (sc VG.Impl.Mont.X86.Rt.multOff))]),
    .loop (.block (fastMac 0 ++ fastMac 4 ++
      [.alu .add .ecx (.imm 8), .alu .add .ebp (.imm 8), .alu .sub .esi (.imm 8)])) .ne,
    .block (VG.Impl.Mont.X86.Rt.carryUp ++ R .edi VG.Impl.Mont.X86.Rt.argS .edx)]

def fastMont : Prog isa :=
  let R := VG.Impl.Mont.X86.Rt.rowEnd
  let row := seqs [.block VG.Impl.Mont.X86.Rt.loadA, fastRow VG.Impl.Mont.X86.Rt.argB,
    .block VG.Impl.Mont.X86.Rt.redDigit, fastRow VG.Impl.Mont.X86.Rt.argM, .block R]
  seqs [.block VG.Impl.Mont.X86.Rt.save, VG.Impl.Mont.X86.Rt.zeroAcc,
    .block VG.Impl.Mont.X86.Rt.accPtr, .loop row .ne, VG.Impl.Mont.X86.Rt.subM,
    .block VG.Impl.Mont.X86.Rt.mask, VG.Impl.Mont.X86.Rt.select,
    .block VG.Impl.Mont.X86.Rt.restoreRegs]

def printFn (name : String) (p : Prog isa) (callee : String := "proto_mont") : String :=
  ".globl " ++ name ++ "\n.p2align 6\n" ++ name ++ ":\n" ++
  "\n".intercalate ((printer.function p).map fun l => match l with
    | .text s => s
    | .call _ => "call " ++ callee
    | .sym .. => "ERROR") ++ "\n"
end Prototype

def main : IO Unit := do
  IO.FS.writeFile "/workspace/scratch/openssl/prototype-generated.S" (
    ".intel_syntax noprefix\n.text\n" ++
    Prototype.printFn "proto_recover" Prototype.code ++
    Prototype.printFn "proto_fast" Prototype.code "proto_fast_mont" ++
    Prototype.printFn "proto_fast_mont" Prototype.fastMont ++
    Prototype.printFn "proto_baseline" VG.Impl.Rsa.X86.RecoverRt.code ++
    Prototype.printFn "proto_mont" VG.Impl.Mont.X86.Rt.body ++
    ".section .note.GNU-stack,\"\",@progbits\n")
