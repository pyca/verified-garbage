module
public import VerifiedGarbage.Impl.Rc2.X86.Lookup


/-! # RC2 block rounds on baseline x86

The four words live in EAX, EBX, ECX and EDX throughout, each in the low half
of its register: what the upper half holds does not matter, and only a
rotation clears it, which needs it. EDI is the schedule and EBP the scratch
pointer throughout; ESI is the temporary.

A MIX reads its key word as the doubleword there, whose upper half is the
next one (the last word is the upper half of the doubleword before its end).
MASH selects its key word from all 64 (`keyLookup`), so its addresses and
branches never depend on secret data.
-/

@[expose] public section

namespace VG.Impl.Rc2.X86

open VG.X86

/-- ECX is also preserved so CBC can keep its IV pointer across calls. -/
def blockSaved : List Reg := [.ebp, .ebx, .esi, .edi, .ecx]

def blockSave : List Instr :=
  blockSaved.zipIdx |>.map fun (r, i) => .store (memOp .eax (4 * i)) r

def blockRestore : List Instr :=
  blockSaved.zipIdx |>.map fun (r, i) => .mov r (.mem (memOp .eax (4 * i)))

def wordReg (i : Nat) : Reg := #[Reg.eax, .ebx, .ecx, .edx][i % 4]!

/-- The low half of `r` rotated left by `n`, its upper half cleared first. -/
def rotate16 (r : Reg) (n : Nat) : List Instr :=
  [.alu .and r (.imm 65535), rr .esi r, .shift .shr .esi (16 - n), .shift .ror r (32 - n),
    .alu .or r (.reg .esi)]

/-- The bits of word `i + 2` where word `i + 3` has ones, and of word `i + 1`
where it has zeros, into ESI: word `i + 3`, the last one computed, enters last. -/
def mixSelect (i : Nat) : List Instr :=
  [rr .esi (wordReg (i + 2)), .alu .xor .esi (.reg (wordReg (i + 1))),
    .alu .and .esi (.reg (wordReg (i + 3))), .alu .xor .esi (.reg (wordReg (i + 1)))]

def adjustOp (sub : Bool) : AluOp := if sub then .sub else .add

def adjust (sub : Bool) (r : Reg) : List Instr := [.alu (adjustOp sub) r (.reg .esi)]

/-- Key word `j` added to or subtracted from `r`. -/
def keyAdjust (sub : Bool) (j : Nat) (r : Reg) : List Instr :=
  if j = 63 then
    ([.mov .esi (.mem (memOp .edi 124)), .shift .shr .esi 16] : List Instr) ++ adjust sub r
  else [.alu (adjustOp sub) r (.mem (memOp .edi (2 * j)))]

def mixArithmetic (sub : Bool) (j i : Nat) : List Instr :=
  keyAdjust sub j (wordReg i) ++ mixSelect i ++ adjust sub (wordReg i)

def mixCore (d : Spec.Rc2.Direction) (j i : Nat) : List Instr :=
  match d with
  | .encrypt => mixArithmetic false j i ++ rotate16 (wordReg i) (Spec.Rc2.rotation i)
  | .decrypt => rotate16 (wordReg i) (16 - Spec.Rc2.rotation i) ++ mixArithmetic true j i

def mash (d : Spec.Rc2.Direction) (i : Nat) : List Instr :=
  keyLookup (wordReg (i + 3)) ++ adjust (d == .decrypt) (wordReg i)

def round (direction : Spec.Rc2.Direction) (j : Nat) : List Instr :=
  match direction with
  | .encrypt => (List.range 4).flatMap (fun i => mixCore .encrypt (4 * j + i) i) ++
      (if j = 4 ∨ j = 10 then (List.range 4).flatMap (mash .encrypt) else [])
  | .decrypt => [3, 2, 1, 0].flatMap (fun i => mixCore .decrypt (4 * (15 - j) + i) i) ++
      (if j = 4 ∨ j = 10 then [3, 2, 1, 0].flatMap (mash .decrypt) else [])

/-- The block at ESI into the four registers. -/
def blockLoad : List Instr :=
  [.mov .eax (.mem (memOp .esi 0)), .mov .ecx (.mem (memOp .esi 4)), rr .ebx .eax, .shift .shr .ebx 16,
    rr .edx .ecx, .shift .shr .edx 16]

/-- `lo`'s low half below `hi`'s, in `lo`. -/
def joinWords (lo hi : Reg) : List Instr :=
  [.alu .and lo (.imm 65535), .shift .ror hi 16, .alu .and hi (.imm 0xffff0000), .alu .or lo (.reg hi)]

/-- The four words to the block at ESI. -/
def blockStore : List Instr :=
  joinWords .eax .ebx ++ joinWords .ecx .edx ++
    ([.store (memOp .esi 0) .eax, .store (memOp .esi 4) .ecx] : List Instr)

def blockCode (direction : Spec.Rc2.Direction) : List Instr :=
  ([.mov .eax (.mem (memOp .esp 12))] : List Instr) ++ blockSave ++
    ([rr .ebp .eax, .mov .edi (.mem (memOp .esp 4)), .mov .esi (.mem (memOp .esp 8))] : List Instr) ++
    blockLoad ++ (List.range 16).flatMap (round direction) ++
    ([.mov .esi (.mem (memOp .esp 8))] : List Instr) ++ blockStore ++
    ([rr .eax .ebp] : List Instr) ++ blockRestore

def encryptBlock : Prog isa := .block (blockCode .encrypt)
def decryptBlock : Prog isa := .block (blockCode .decrypt)

end VG.Impl.Rc2.X86
