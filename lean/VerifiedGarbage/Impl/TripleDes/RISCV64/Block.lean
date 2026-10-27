module

public import VerifiedGarbage.Impl.TripleDes.RISCV64.Common
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Feistel
public import VerifiedGarbage.Impl.Words.RISCV64
public import VerifiedGarbage.Impl.Words.RISCV64.Word64
public import VerifiedGarbage.Spec.TripleDes

/-!
# Scalar Triple DES blocks on RISC-V

The algorithm of the PPC64LE implementation (`Impl/TripleDes/PPC64LE/Block.lean`),
one block at a time, but with the round function of `Feistel.lean`, which
looks the eight S-boxes up at once in the 64 lanes of a word: `block d dp
doff` encrypts (or decrypts) the block at `doff(dp)` in place, with a frame
at `sb` (`s4`, a multiple of 16) that holds the three DES schedules from byte
`keyOff` on (`keySlot`), as the modes and ECB copy them there. The two
32-bit Feistel halves stay in `a1` (L) and `a2` (R). The three passes share
IP and FP, and one loop runs them, with the pass's first key and its step
chosen by the passes left. `a4` counts the rounds, `a3` points at the round
key, `a5` holds the key step (8 or −8) and `a6` the passes left. Slots 7–12
of the frame save `s5`–`s10`, which the round function uses, and slots
15–69 hold its words of constants, which the block stores first
(`storeConsts`). Only temporaries, argument registers other than `a0`, and
those saved registers are written, so that a caller can keep public values
(a frame's base, a data pointer, a count) in `s1`–`s4` across a block: the
taint analysis cannot follow a value through memory. Round counters and key
addresses are public. The block is accessed a byte at a time, as it may be
anywhere.
-/

@[expose] public section

namespace VG.Impl.TripleDes.RISCV64

open VG.RISCV64
open VG.Impl.Words.RISCV64 (loadBE64 storeBE)
open VG.Spec.TripleDes (Direction)

def lReg : Reg := .a1
def rReg : Reg := .a2
def kp : Reg := .a3
def cnt : Reg := .a4
def kstep : Reg := .a5
def passes : Reg := .a6

/-- The first byte of the schedules' copy in the frame, after the round
function's words of constants (slots 15–69). -/
def keyOff : Nat := 560

/-- The registers the block saves for its caller, and their slots' offsets. -/
def savedSlots : List (Reg × Nat) :=
  [(.s5, 56), (.s6, 64), (.s7, 72), (.s8, 80), (.s9, 88), (.s10, 96)]

def blockSave : List Instr := savedSlots.map fun (r, d) => .store .d r sb d
def blockRestore : List Instr := savedSlots.map fun (r, d) => .load .d r sb d

/-- Load the block big-endian, apply IP, and split it into L and R. -/
def blockLoad (dp : Reg) (doff : Nat) : List Instr :=
  loadBE64 .t0 .t1 dp doff ++ permuteCode Spec.TripleDes.ip 64 .t2 .t0 .t3 ++
    ([.shift .srl .d lReg .t2 32, .shift .sll .d rReg .t2 32, .shift .srl .d rReg rReg 32] :
      List Instr)

def swapHalves : List Instr := [movR .t0 lReg, movR lReg rReg, movR rReg .t0]

def roundBody : List Instr := feistel ++ swapHalves

/-- The next round key, `kstep` bytes on, and the round counted. -/
def roundAdvance : List Instr := [.add kp kp kstep, .addi cnt cnt (-1)]

def passStart (component : Nat) (d : Direction) : List Instr :=
  [.addi kp sb (keyOff + 128 * component + if d = .encrypt then 0 else 120 : Nat), .li cnt 16,
    .li kstep (if d = .encrypt then 8 else -8)]

/-- The component and direction of the pass with `left` passes left (3, 2, 1). -/
def passOf (d : Direction) (left : Nat) : Nat × Direction :=
  match d, left with
  | .encrypt, 3 => (0, .encrypt)
  | .encrypt, 2 => (1, .decrypt)
  | .encrypt, _ => (2, .encrypt)
  | .decrypt, 3 => (2, .decrypt)
  | .decrypt, 2 => (1, .encrypt)
  | .decrypt, _ => (0, .decrypt)

/-- Choose the pass's first key and step by the passes left. -/
def passSelect (d : Direction) : Prog isa :=
  .seq (.block [.addi .t6 passes (-3)])
    (.ite (.zero .t6) (.block (passStart (passOf d 3).1 (passOf d 3).2))
      (.seq (.block [.addi .t6 passes (-2)])
        (.ite (.zero .t6) (.block (passStart (passOf d 2).1 (passOf d 2).2))
          (.block (passStart (passOf d 1).1 (passOf d 1).2)))))

def passCountAdvance : List Instr := [.addi passes passes (-1)]

def pass (d : Direction) : Prog isa :=
  .seq (passSelect d)
    (.seq (.loop (.block (roundBody ++ roundAdvance)) (.nonzero cnt))
      (.block (swapHalves ++ passCountAdvance)))

def blockBody (d : Direction) : Prog isa :=
  .seq (.block [.li passes 3]) (.loop (pass d) (.nonzero passes))

/-- Join R and L, apply FP, and store the block big-endian. -/
def blockStore (dp : Reg) (doff : Nat) : List Instr :=
  ([.shift .sll .d .t0 lReg 32, .logic .xor .t0 .t0 rReg] : List Instr) ++
    permuteCode Spec.TripleDes.fp 64 .t2 .t0 .t3 ++ storeBE 8 .t2 .t1 dp doff

/-- The block at `doff(dp)`, encrypted or decrypted in place. -/
def block (d : Direction) (dp : Reg) (doff : Nat) : Prog isa :=
  .seq (.block (blockSave ++ storeConsts roundConsts constOff ++ blockLoad dp doff))
    (.seq (blockBody d) (.block (blockStore dp doff ++ blockRestore)))

end VG.Impl.TripleDes.RISCV64
