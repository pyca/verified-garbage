module

public import VerifiedGarbage.Impl.Words.RISCV64.Bytes

/-!
# RC4 on RISC-V

The algorithm of the PPC64LE implementation (`Impl/Rc4/PPC64LE.lean`): the
256-byte table is visited as 32 doublewords at fixed addresses: a
secret-indexed lookup keeps, with masks, the doubleword that holds the byte
and then the byte of it; a secret-indexed replacement stores every
doubleword back, XORed with a masked difference that is nonzero only in the
selected byte. There is no compare instruction: a mask is all ones or zero
by whether a value `v < 2 ^ 63` is zero, `0 - ((v - 1) >> 63)` (`isZero`).
Only the doubleword addresses, the PRGA index `i`, the key offset, the
pointers and the lengths are public.

The model faults on misaligned accesses, and the contracts state no
alignment for the context, so the table is kept in a 256-byte frame on the
stack (`alloc`), which is 16-byte aligned: `apply` copies it there from the
context and back, a byte at a time, and `init` builds it there and copies
it out. Both zero the frame before returning (`wipe`).

Registers: the frame at `a7`, the public index `i` in `a3`, the secret
index of a lookup or replacement in `a4`, its result in `a5`, zero in `t6`;
`t0`, `t1` and `t2` are scratch. Initialization keeps the key at `a0`, its
length in `a1`, the context at `a2`, the key offset in `t3` and `j` in
`a4`; the stream function keeps the context at `a0`, the data at `a1`, the
remaining length in `a2` and `j` in `t4`. Only temporaries are used.
-/

@[expose] public section

namespace VG.Impl.Rc4.RISCV64

open VG.RISCV64
open VG.Impl.Words.RISCV64 (copyBytes)

/-- The bytes of the frame holding the table. -/
def frameBytes : Nat := 256

/-- `t2` := all ones if `t2` (below `2 ^ 63`) is zero, else 0. -/
def isZero : List Instr := [.addi .t2 .t2 (-1), .shift .srl .d .t2 .t2 63, .sub .t2 .t6 .t2]

/-- `t2` := all ones if `a4 XOR 8k < 8` (byte `a4` is in doubleword `k`), else 0. -/
def rowMask (k : Nat) : List Instr :=
  [.li .t2 (8 * k : Nat), .logic .xor .t2 .t2 .a4, .shift .srl .d .t2 .t2 3] ++ isZero

/-- `t2` := all ones if `a4 AND 7 = j`, else 0. -/
def laneMask (j : Nat) : List Instr :=
  [.li .t2 (j : Nat), .logic .xor .t2 .t2 .a4, .shift .sll .d .t2 .t2 61,
    .shift .srl .d .t2 .t2 61] ++ isZero

/-- Keep doubleword `k` in `t1` if it holds byte `a4`. -/
def gatherStep (k : Nat) : List Instr :=
  rowMask k ++ ([.load .d .t0 .a7 (8 * k), .logic .and .t0 .t0 .t2, .logic .or .t1 .t1 .t0] :
    List Instr)

/-- Keep byte `j` of the doubleword in `t1` (shifted down by `8j` so far) in
`a5` if it is byte `a4`. -/
def pickStep (j : Nat) : List Instr :=
  laneMask j ++ ([.logic .and .t0 .t1 .t2, .logic .or .a5 .a5 .t0, .shift .srl .d .t1 .t1 8] :
    List Instr)

/-- The byte of the table at `a7` indexed by the low byte `a4`, into `a5`.
Clobbers `t0`, `t1` and `t2`. -/
def lookup : List Instr :=
  ([.li .t1 0] : List Instr) ++ (List.range 32).flatMap gatherStep ++
    ([.li .a5 0] : List Instr) ++ (List.range 8).flatMap pickStep ++
    ([.shift .sll .d .a5 .a5 56, .shift .srl .d .a5 .a5 56] : List Instr)

/-- Shift the difference in `t1` up a byte and add the byte in `a5` if `j`
is the lane of `a4`: run for `j` from 7 down to 0, it leaves `a5` shifted to
the lane of `a4`. -/
def spreadStep (j : Nat) : List Instr :=
  laneMask j ++ ([.logic .and .t0 .a5 .t2, .shift .sll .d .t1 .t1 8, .logic .or .t1 .t1 .t0] :
    List Instr)

/-- XOR doubleword `k` with the difference in `t1` if it holds byte `a4`,
and store it back. -/
def scatterStep (k : Nat) : List Instr :=
  rowMask k ++ ([.logic .and .t2 .t2 .t1, .load .d .t0 .a7 (8 * k),
    .logic .xor .t0 .t0 .t2, .store .d .t0 .a7 (8 * k)] : List Instr)

/-- The lanes 7 down to 0. -/
def lanesDown : List Nat := [7, 6, 5, 4, 3, 2, 1, 0]

/-- `t0` := the byte at the public index `a3` of the table, through `t2`. -/
def loadI : List Instr := [.add .t2 .a7 .a3, .load .b .t0 .t2 0]

/-- Replace the byte of the table at `a7` indexed by the low byte of `a4`
with the byte at the public index `a3`, returning its original value in
`a5`. Clobbers `t0`, `t1` and `t2`. -/
def replace : List Instr :=
  lookup ++ loadI ++ ([.logic .xor .a5 .a5 .t0, .li .t1 0] : List Instr) ++
    lanesDown.flatMap spreadStep ++ loadI ++ ([.logic .xor .a5 .a5 .t0] : List Instr) ++
    (List.range 32).flatMap scatterStep

/-- Zero the frame at `a7`, from `t6`. -/
def wipe : List Instr := (List.range 32).map fun k => .store .d .t6 .a7 (8 * k)

/-- Store the identity permutation, a byte at a time; `t2 := i - 256`. -/
def identityStep : List Instr :=
  [.add .t2 .a7 .a3, .store .b .a3 .t2 0, .addi .a3 .a3 1, .li .t2 256, .sub .t2 .a3 .t2]

/-- `j += S[i] + key[off]`, the swap, then the next key offset (0 at the key
length, without a branch) and `i`; `t2 := i - 256`. -/
def scheduleStep : List Instr :=
  loadI ++ ([.add .a4 .a4 .t0, .add .t2 .a0 .t3, .load .b .t0 .t2 0, .add .a4 .a4 .t0,
    .shift .sll .d .a4 .a4 56, .shift .srl .d .a4 .a4 56] : List Instr) ++ replace ++
    ([.add .t2 .a7 .a3, .store .b .a5 .t2 0,
      .addi .t3 .t3 1, .sub .t2 .t3 .a1, .addi .t0 .t2 (-1), .logic .xor .t0 .t0 .t2,
      .shift .srl .d .t2 .t0 63, .addi .t2 .t2 (-1), .logic .and .t3 .t3 .t2,
      .addi .a3 .a3 1, .li .t2 256, .sub .t2 .a3 .t2] : List Instr)

/-- Key scheduling after the key-length check, in its frame: the table is
built there and copied to the context. -/
def initMain : Prog isa :=
  .seq (.block [.addSp .a7 0, .li .a3 0])
    (.seq (.loop (.block identityStep) (.nonzero .t2))
      (.seq (.block [.li .a3 0, .li .t3 0, .li .a4 0, .li .t6 0])
        (.seq (.loop (.block scheduleStep) (.nonzero .t2))
          (.block (copyBytes .t0 .a7 .a2 0 0 256 ++
            [.li .t2 0, .store .b .t2 .a2 256, .store .b .t2 .a2 257, .li .a0 0] ++ wipe)))))

/-- Checked key scheduling: `(key_len - 1) >> 8` is zero exactly for
`key_len` in 1..=256; invalid lengths return 1, valid lengths 0. -/
def init : Prog isa :=
  .seq (.block [.addi .t2 .a1 (-1), .shift .srl .d .t2 .t2 8])
    (.ite (.nonzero .t2) (.block [.li .a0 1])
      (.frame (.alloc frameBytes) initMain (.free frameBytes)))

/-- One PRGA step: `i += 1`, `j += S[i]`, the swap, then the keystream byte
`S[S[i] + S[j]]` XORed into the next data byte. -/
def applyStep : List Instr :=
  ([.addi .a3 .a3 1, .shift .sll .d .a3 .a3 56, .shift .srl .d .a3 .a3 56] : List Instr) ++ loadI ++
    ([.add .t4 .t4 .t0, .shift .sll .d .t4 .t4 56, .shift .srl .d .t4 .t4 56, .logic .or .a4 .t4 .t4] :
      List Instr) ++ replace ++ loadI ++
    ([.store .b .a5 .t2 0, .add .a4 .a5 .t0, .shift .sll .d .a4 .a4 56,
      .shift .srl .d .a4 .a4 56] : List Instr) ++
    lookup ++
    ([.load .b .t0 .a1 0, .logic .xor .t0 .t0 .a5, .store .b .t0 .a1 0, .addi .a1 .a1 1,
      .addi .a2 .a2 (-1)] : List Instr)

/-- Streaming XOR of a nonempty input, in its frame: the table is copied to
the frame, updated there and copied back with both PRGA indices. -/
def applyMain : Prog isa :=
  .seq (.block (.addSp .a7 0 :: copyBytes .t0 .a0 .a7 0 0 256))
    (.seq (.loop (.block applyStep) (.nonzero .a2))
      (.block (copyBytes .t0 .a7 .a0 0 0 256 ++ [.store .b .a3 .a0 256, .store .b .t4 .a0 257] ++
        wipe)))

/-- Streaming XOR, preserving the permutation and both PRGA indices. The
indices are loaded first; an empty input needs no frame. -/
def apply : Prog isa :=
  .seq (.block [.load .b .a3 .a0 256, .load .b .t4 .a0 257, .li .t6 0])
    (.ite (.zero .a2) (.block []) (.frame (.alloc frameBytes) applyMain (.free frameBytes)))

end VG.Impl.Rc4.RISCV64
