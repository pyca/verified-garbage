module

import VerifiedGarbage.TCB.X86_64.Print
meta import VerifiedGarbage.TCB.X86_64.Print

/-!
# Semantics tests for the x86-64 `add QWORD PTR [m], r64` and `add DWORD PTR [m], r32`

Each expected value was computed on an x86-64 CPU (an AMD Ryzen 9 9950X), by
the same instruction in inline assembly (`add QWORD PTR [mem], r64` and
`add DWORD PTR [mem], r32`, reading RFLAGS with `pushfq` after it), and is
compared with the model's result on the same inputs: the sum written back
to memory, CF (the carry out), OF (signed overflow), ZF and SF from the
sum. This tests the transcription of the SDM's pseudocode, which review of
the TCB would otherwise have to catch by eye. The 32-bit form reads the low
32 bits of its register (here with other bits above them) and writes 4
bytes, leaving the bytes after them alone. Both fault where the memory may
not be read, or not written.

The encodings are GNU as's (`as` 2.46, `objdump -d`), for each kind of
memory operand: a displacement of 8 and of 32 bits, none, the `rsp`/`r12`
base (which needs a SIB byte), the `rbp`/`r13` base (which needs a
displacement), an index, and the registers `r8`–`r15` (REX.R and REX.B).
-/

namespace VG.Test.X86_64AddMem

open X86_64

/-- A state with `r` in `rcx` (over other bits, for the 32-bit form), the
little-endian `v` (16 bytes) at `0x200`, which it may read and write (or
only read if `ro`), and every flag defined. -/
def s (v : BitVec 128) (r : BitVec 64) (ro : Bool := false) : State where
  gpr q := if q = .rcx then r else if q = .rdi then 0x200 else 7
  cf := some true
  zf := some true
  sf := some true
  of := some true
  mem a := if 0x200 ≤ a.toNat ∧ a.toNat < 0x210 then v.extractLsb' (8 * (a.toNat - 0x200)) 8 else 0
  rd := [⟨0x200, 16⟩]
  wr := if ro then [] else [⟨0x200, 16⟩]

def at0 : MemOp := { base := .rdi }

/-- `add QWORD PTR [rdi], rcx` with `m` at `[rdi]` and `r` in `rcx`: the
expected sum at `[rdi]`, CF, ZF, SF and OF, and the 8 bytes after it kept. -/
def q (m r sum : BitVec 64) (cf zf sf o : Bool) : Bool :=
  (exec (.addMem at0 .rcx) (s ((0xa5a5a5a5a5a5a5a5 : BitVec 64) ++ m) r)).map
      (fun t => (t.mem.readW 0x200 64, t.mem.readW 0x208 64, t.cf, t.zf, t.sf, t.of)) ==
    some (sum, 0xa5a5a5a5a5a5a5a5, some cf, some zf, some sf, some o)

/-- `add DWORD PTR [rdi], ecx` with `m` at `[rdi]` and `r` in `ecx` (and
`0xdeadbeef` above it in `rcx`): the expected sum at `[rdi]`, CF, ZF, SF and
OF, and the 12 bytes after it kept. -/
def d (m r sum : BitVec 32) (cf zf sf o : Bool) : Bool :=
  (exec (.addMem32 at0 .rcx) (s ((0xa5a5a5a5a5a5a5a5a5a5a5a5 : BitVec 96) ++ m) ((0xdeadbeef : BitVec 32) ++ r))).map
      (fun t => (t.mem.readW 0x200 32, t.mem.readW 0x204 64, t.mem.readW 0x20c 32, t.cf, t.zf, t.sf, t.of)) ==
    some (sum, 0xa5a5a5a5a5a5a5a5, 0xa5a5a5a5, some cf, some zf, some sf, some o)

-- 64 bits: zero, a sum, a carry to zero, signed overflow, both, mixed, a
-- negative sum, and a carry with overflow.
#guard q 0 0 0 false true false false
#guard q 1 2 3 false false false false
#guard q 0xffffffffffffffff 1 0 true true false false
#guard q 0x7fffffffffffffff 1 0x8000000000000000 false false true true
#guard q 0x8000000000000000 0x8000000000000000 0 true true false true
#guard q 0x123456789abcdef0 0x0fedcba987654321 0x2222222222222211 false false false false
#guard q 0xfffffffffffffffe 0xfffffffffffffffe 0xfffffffffffffffc true false true false
#guard q 0x8000000000000000 0xffffffffffffffff 0x7fffffffffffffff true false false true

-- 32 bits, the same cases, and the carry and overflow of a 32-bit sum
-- that a 64-bit one would not have.
#guard d 0 0 0 false true false false
#guard d 1 2 3 false false false false
#guard d 0xffffffff 1 0 true true false false
#guard d 0x7fffffff 1 0x80000000 false false true true
#guard d 0x80000000 0x80000000 0 true true false true
#guard d 0x9abcdef0 0x87654321 0x22222211 true false false true
#guard d 0xfffffffe 0xfffffffe 0xfffffffc true false true false
#guard d 0x80000000 0xffffffff 0x7fffffff true false false true

-- Memory it may read but not write, or not read: a fault.
#guard (exec (.addMem at0 .rcx) (s 0 1 (ro := true))).isNone
#guard (exec (.addMem32 at0 .rcx) (s 0 1 (ro := true))).isNone
#guard (exec (.addMem { base := .rdi, disp := 12 } .rcx) (s 0 1)).isNone
#guard (exec (.addMem32 { base := .rdi, disp := 13 } .rcx) (s 0 1)).isNone
#guard (exec (.addMem32 { base := .rdi, disp := 12 } .rcx) (s 0 1)).isSome

-- One memory access, at the operand's address, and no register written.
#guard addrs (.addMem at0 .rcx) (s 0 1) == [0x200]
#guard addrs (.addMem32 { base := .rdi, disp := 8 } .rcx) (s 0 1) == [0x208]
#guard (Instr.addMem at0 .rcx).dst == none
#guard (Instr.addMem32 at0 .rcx).dst == none
#guard Instr.requires (.addMem at0 .rcx) == []
#guard Instr.requires (.addMem32 at0 .rcx) == []

-- The encodings, against GNU as.
#guard Instr.encode (.addMem { base := .r9, disp := 16 } .rax) == some [[0x49, 0x01, 0x41, 0x10]]
#guard Instr.encode (.addMem { base := .rdi } .r14) == some [[0x4c, 0x01, 0x37]]
#guard Instr.encode (.addMem { base := .rsp, disp := 8 } .rcx) == some [[0x48, 0x01, 0x4c, 0x24, 0x08]]
#guard Instr.encode (.addMem { base := .r12, disp := 0x200 } .r15) ==
  some [[0x4d, 0x01, 0xbc, 0x24, 0x00, 0x02, 0x00, 0x00]]
#guard Instr.encode (.addMem { base := .rbp } .rdx) == some [[0x48, 0x01, 0x55, 0x00]]
#guard Instr.encode (.addMem { base := .r13 } .r8) == some [[0x4d, 0x01, 0x45, 0x00]]
#guard Instr.encode (.addMem { base := .rsi, index := some .rcx, scale := 4, disp := 8 } .rbx) ==
  some [[0x48, 0x01, 0x5c, 0x8e, 0x08]]
#guard Instr.encode (.addMem32 { base := .r9, disp := 16 } .rax) == some [[0x41, 0x01, 0x41, 0x10]]
#guard Instr.encode (.addMem32 { base := .rdi } .r14) == some [[0x44, 0x01, 0x37]]
#guard Instr.encode (.addMem32 { base := .rsp, disp := 8 } .rcx) == some [[0x01, 0x4c, 0x24, 0x08]]
#guard Instr.encode (.addMem32 { base := .r12, disp := 0x200 } .r15) ==
  some [[0x45, 0x01, 0xbc, 0x24, 0x00, 0x02, 0x00, 0x00]]
#guard Instr.encode (.addMem32 { base := .rbp } .rdx) == some [[0x01, 0x55, 0x00]]
#guard Instr.encode (.addMem32 { base := .r13 } .r8) == some [[0x45, 0x01, 0x45, 0x00]]
#guard Instr.encode (.addMem32 { base := .rsi, index := some .rcx, scale := 4, disp := 8 } .rbx) ==
  some [[0x01, 0x5c, 0x8e, 0x08]]
#guard Instr.encode (.addMem32 { base := .r9, disp := -4 } .r11) == some [[0x45, 0x01, 0x59, 0xfc]]

-- The text.
#guard Instr.asm (.addMem { base := .r9, disp := 16 } .rax) == ["add QWORD PTR [r9+16], rax"]
#guard Instr.asm (.addMem32 { base := .r9, disp := -4 } .r11) == ["add DWORD PTR [r9-4], r11d"]

end VG.Test.X86_64AddMem
