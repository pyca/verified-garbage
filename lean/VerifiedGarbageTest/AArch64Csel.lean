import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Inline

/-!
# AArch64 CSEL

Expected results below were produced by `cmp` (setting or clearing C) and then
`csel …, hs` in a Clang inline-assembly probe on an Apple M1 Max (macOS 27).
The sources have distinct upper and lower halves, so the 32-bit results check
both truncation of the inputs and zero-extension of the destination. These are
instruction-semantic checks, not cryptographic known-answer vectors.
-/

namespace VG.Test.AArch64Csel
open AArch64

def input (c : Bool) : State where
  gpr r := if r = .x1 then 0x0123456789abcdef else
    if r = .x2 then 0xfedcba9876543210 else 0xdeadbeefdeadbeef
  sp := 0x1000
  c := c
  mem _ := 0
  rd := []
  wr := []

def run (c : Bool) (i : Instr) : Option (BitVec 64) := (exec i (input c)).map (·.gpr .x0)

#guard run true (.csel .x .x0 .x1 .x2) == some 0x0123456789abcdef
#guard run false (.csel .x .x0 .x1 .x2) == some 0xfedcba9876543210
#guard run true (.csel .w .x0 .x1 .x2) == some 0x0000000089abcdef
#guard run false (.csel .w .x0 .x1 .x2) == some 0x0000000076543210

-- Aliased destinations read the old sources before writing the result.
#guard (exec (.csel .x .x1 .x2 .x1) (input true)).map (·.gpr .x1) == some 0xfedcba9876543210
#guard (exec (.csel .x .x2 .x2 .x1) (input false)).map (·.gpr .x2) == some 0x0123456789abcdef

-- The flags are kept, no optional CPU features, and the framework recognizes writes.
#guard (exec (.csel .x .x0 .x1 .x2) (input true)).map (·.c) == some true
#guard (exec (.csel .x .x0 .x1 .x2) (input false)).map (·.c) == some false
#guard Instr.requires (.csel .x .x0 .x1 .x2) == []
#guard dstOf (.csel .x .x0 .x1 .x2) == some .x0

#guard printer.instr (.csel .x .x0 .x1 .x2) == ["csel x0, x1, x2, hs"]
#guard printer.instr (.csel .w .x0 .x1 .x2) == ["csel w0, w1, w2, hs"]

-- The carry is secret in this domain, so the result is too.
#guard ((AArch64.Taint.step (AArch64.Taint.ofRegs [.x1, .x2])
  (.csel .x .x0 .x1 .x2)).map (AArch64.Taint.pub · .x0)) == some false

end VG.Test.AArch64Csel
