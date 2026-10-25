module

public import VerifiedGarbage.Impl.TripleDes.RISCV64.Common
public import VerifiedGarbage.Impl.TripleDes.RISCV64.Sbox
public import VerifiedGarbage.Impl.Words.RISCV64
public import VerifiedGarbage.Impl.Words.RISCV64.Word64
public import VerifiedGarbage.Spec.TripleDes

/-!
# Scalar Triple DES blocks on RISC-V

The algorithm of the PPC64LE implementation (`Impl/TripleDes/PPC64LE/Block.lean`),
one block at a time: `block d dp doff` encrypts (or decrypts) the block at
`doff(dp)` in place, with a frame at `sb` (`s4`, a multiple of 16) that holds
the three DES schedules from byte `keyOff` on (`keySlot`), as the modes and
ECB copy them there. The two 32-bit Feistel halves stay in `a1` (L) and `a2`
(R). S-box input bits are formed with fixed shifts and XORs with the round
key, passed through Boolean circuits, and XORed directly into their
P-permuted destinations. The three passes share IP and FP, and one loop
runs them, with the pass's first key and its step chosen by the passes
left. `a4` counts the rounds, `a3` points at the round key, `a5` holds the
key step (8 or −8) and `a6` the passes left. Slots 7–14 of the frame save
`s0` and `s5`–`s11`, which the S-boxes use for their temporaries, and slots
15–30 are the S-boxes' spills. Only temporaries, argument registers other
than `a0`, and those saved registers are written, so that a caller can keep
public values (a frame's base, a data pointer, a count) in `s1`–`s4` across
a block: the taint analysis cannot follow a value through memory. Round
counters and key addresses are public. The block is accessed a byte at a
time, as it may be anywhere.
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

/-- The first byte of the schedules' copy in the frame. -/
def keyOff : Nat := 256

/-- The registers the block saves for its caller, and their slots' offsets. -/
def savedSlots : List (Reg × Nat) :=
  [(.s0, 56), (.s5, 64), (.s6, 72), (.s7, 80), (.s8, 88), (.s9, 96), (.s10, 104), (.s11, 112)]

def blockSave : List Instr := savedSlots.map fun (r, d) => .store .d r sb d
def blockRestore : List Instr := savedSlots.map fun (r, d) => .load .d r sb d

/-- Load the block big-endian, apply IP, and split it into L and R. -/
def blockLoad (dp : Reg) (doff : Nat) : List Instr :=
  loadBE64 .t0 .t1 dp doff ++ permuteCode Spec.TripleDes.ip 64 .t2 .t0 .t3 ++
    ([.shift .srl .d lReg .t2 32, .shift .sll .d rReg .t2 32, .shift .srl .d rReg rReg 32] :
      List Instr)

/-- Six inputs, least significant first, for public S-box number `i`.
The source R bit comes directly from E; the key's upper sixteen bits are
never read as cipher bits. -/
def sboxInputs (i : Nat) : List Instr :=
  ([.load .d .t6 kp 0] : List Instr) ++ (List.range 6).flatMap fun j =>
    let k := 6 * i + 5 - j
    shrFrom (q j) rReg (32 - Spec.TripleDes.expansion.getD k 1) ++
      shrFrom .a7 .t6 (47 - k) ++
      ([.logic .xor (q j) (q j) .a7, .logicImm .and (q j) (q j) 1] : List Instr)

/-- Deposit each output's low bit directly into its destination in L.
The P table contains all 32 positions, so each destination is unique. -/
def sboxOutputs (i : Nat) : List Instr :=
  (List.range 4).flatMap fun j =>
    let position := 4 * i + 4 - j
    let dst := (Spec.TripleDes.p.toList.findIdx? (· == position)).getD 0
    ([.logicImm .and (q j) (q j) 1] : List Instr) ++ placeBit (q j) (31 - dst) ++
      ([.logic .xor lReg lReg (q j)] : List Instr)

def box (i : Nat) : List Instr := sboxInputs i ++ sboxCode i ++ sboxOutputs i

def swapHalves : List Instr := [movR .t0 lReg, movR lReg rReg, movR rReg .t0]

def roundBody : List Instr := (List.range 8).flatMap box ++ swapHalves

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
  .seq (.block (blockSave ++ blockLoad dp doff))
    (.seq (blockBody d) (.block (blockStore dp doff ++ blockRestore)))

end VG.Impl.TripleDes.RISCV64
