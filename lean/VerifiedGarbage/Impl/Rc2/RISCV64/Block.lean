module

public import VerifiedGarbage.Impl.Rc2.RISCV64.Lookup
public import VerifiedGarbage.Impl.Words.RISCV64.Bytes
public import VerifiedGarbage.Impl.Words.RISCV64.Loops
public import VerifiedGarbage.Spec.Rc2

/-! # RC2 block encryption and decryption on RISC-V

`vg_rc2_{en,de}crypt_block(schedule = a0, data = a1, scratch = a2)`, the
algorithm of the PPC64LE implementation (`Impl/Rc2/PPC64LE/Block.lean`).
The model faults on misaligned accesses, and the contracts state no
alignment for the schedule or the block, so the schedule is first copied a
byte at a time to the start of the working space, which is aligned, and
read there: a key word at a public index with `lhu`, at the secret index of
a mash by a scan of the copy's doublewords (`keyLookup`). The block is read
and written a byte at a time, as a little-endian doubleword. The four words
are kept zero-extended in `a3`–`a6`. A mix computes `a & b` and `c & ~a`
(as `c XOR (a & c)`) from the neighbouring words, adds them and the key
word, masks the sum to 16 bits and rotates it with two shifts. Only
temporaries and argument registers are used, and no stack.
-/

@[expose] public section

namespace VG.Impl.Rc2.RISCV64

open VG.RISCV64
open VG.Impl.Words.RISCV64 (loadLE64 storeLE64 copyLoop)

def wordReg (i : Nat) : Reg := #[Reg.a3, .a4, .a5, .a6][i % 4]!

/-- The schedule (at `a0`) to its copy at the start of the working space
(`a2`), a byte at a time through `t3`, `t4` and `t5`. -/
def copySchedule : Prog isa :=
  .seq (.block [.addi .t3 .a0 0, .addi .t4 .a2 0, .li .t5 128]) (copyLoop .a7 .t3 .t4 .t5)

/-- The block at `a1`, a little-endian doubleword, into the four words. -/
def blockLoad : List Instr :=
  loadLE64 .t1 .a7 .t2 .a1 0 ++
    [.shift .sll .d .a3 .t1 48, .shift .srl .d .a3 .a3 48, .shift .sll .d .a4 .t1 32,
     .shift .srl .d .a4 .a4 48, .shift .sll .d .a5 .t1 16, .shift .srl .d .a5 .a5 48,
     .shift .srl .d .a6 .t1 48]

/-- The four words to the block at `a1`, a little-endian doubleword. -/
def blockStore : List Instr :=
  [.shift .sll .d .t1 .a4 16, .logic .or .t1 .t1 .a3, .shift .sll .d .t2 .a5 32,
   .logic .or .t1 .t1 .t2, .shift .sll .d .t2 .a6 48, .logic .or .t1 .t1 .t2] ++
    storeLE64 .t1 .a7 .t2 .a1 0

/-- Key word `j` of the schedule's copy into `t2`. -/
def loadKey (j : Nat) : List Instr := [.load .h .t2 .a2 (2 * j)]

/-- Rotate the (zero-extended) word in `r` left by `s` bits, through `a7`. -/
def rotate16 (r : Reg) (s : Nat) : List Instr :=
  [.shift .sll .d .a7 r s, .shift .srl .d r r (16 - s), .logic .or r r .a7] ++ mask r 16

/-- `a & b` into `t0`, `c & ~a` into `t1` (`a`, `b`, `c` the words before
`i`), and key word `j` into `t2`. -/
def mixInputs (j i : Nat) : List Instr :=
  ([.logic .and .t0 (wordReg (i + 3)) (wordReg (i + 2)),
    .logic .and .t1 (wordReg (i + 3)) (wordReg (i + 1)),
    .logic .xor .t1 (wordReg (i + 1)) .t1] : List Instr) ++ loadKey j

def addInputs (r : Reg) : List Instr :=
  ([.add r r .t2, .add r r .t0, .add r r .t1] : List Instr) ++ mask r 16

def subInputs (r : Reg) : List Instr :=
  ([.sub r r .t2, .sub r r .t0, .sub r r .t1] : List Instr) ++ mask r 16

def mix (j i : Nat) : List Instr :=
  mixInputs j i ++ addInputs (wordReg i) ++ rotate16 (wordReg i) (Spec.Rc2.rotation i)

def reverseMix (j i : Nat) : List Instr :=
  rotate16 (wordReg i) (16 - Spec.Rc2.rotation i) ++ mixInputs j i ++ subInputs (wordReg i)

/-- `q := 2 (w & 63)` for the word `w` before `i`. -/
def mashIndex (i : Nat) : List Instr :=
  [.shift .sll .d .t0 (wordReg (i + 3)) 58, .shift .srl .d .t0 .t0 57]

def adjust (sub : Bool) (r : Reg) : List Instr :=
  [if sub then .sub r r .t1 else .add r r .t1] ++ mask r 16

def mash (direction : Spec.Rc2.Direction) (i : Nat) : Prog isa :=
  .seq (.block (mashIndex i)) (.seq keyLookup (.block (adjust (direction == .decrypt) (wordReg i))))

/-- The order of the words in a round. -/
def order (direction : Spec.Rc2.Direction) : List Nat :=
  match direction with
  | .encrypt => List.range 4
  | .decrypt => [3, 2, 1, 0]

def mashRound (direction : Spec.Rc2.Direction) : Prog isa :=
  (order direction).foldr (fun i rest => .seq (mash direction i) rest) (.block [])

def mixRound (direction : Spec.Rc2.Direction) (j : Nat) : List Instr :=
  match direction with
  | .encrypt => (List.range 4).flatMap (fun i => mix (4 * j + i) i)
  | .decrypt => [3, 2, 1, 0].flatMap (fun i => reverseMix (4 * (15 - j) + i) i)

def round (direction : Spec.Rc2.Direction) (j : Nat) : Prog isa :=
  .seq (.block (mixRound direction j)) (if j = 4 ∨ j = 10 then mashRound direction else .block [])

def rounds (direction : Spec.Rc2.Direction) : Prog isa :=
  (List.range 16).foldr (fun j rest => .seq (round direction j) rest) (.block [])

def blockCode (direction : Spec.Rc2.Direction) : Prog isa :=
  .seq copySchedule (.seq (.block blockLoad) (.seq (rounds direction) (.block blockStore)))

def encryptBlock : Prog isa := blockCode .encrypt
def decryptBlock : Prog isa := blockCode .decrypt

end VG.Impl.Rc2.RISCV64
