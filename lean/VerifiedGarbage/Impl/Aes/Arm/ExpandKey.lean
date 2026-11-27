module

public import VerifiedGarbage.Impl.Aes.Arm.Ctr32

/-!
# The AES key expansion on ARMv7

`vg_aes_expand_key(key = r0, key_len = r1, schedule = r2)`, with its working
space (512 bytes, laid out as `Ctr32.lean`'s) at `r3`: the key is copied, and
then each word of the schedule made from the last (in `r0`) and the one `Nk`
words back.

SUBWORD of `w` needs no transpose: the S-box's code acts on each bit position
for itself, so with `w` shifted right by `j` as slice `j`, the positions of
the bytes' lowest bits hold the bytes, and the others do not matter
(`subWord`).

During the loop over the words `r9` points at the word `Nk` back, `r10` at the
next, `r11` is its index modulo `Nk`, `r12` is `Nk` and `lr` counts the words
left; `subWord` keeps the last four in slots meanwhile. The next round constant is in
slot `rconSlot`.
-/

@[expose] public section

namespace VG.Impl.Aes.Arm

open VG.Arm

def rconSlot : Nat := 41

/-- The loop's registers that the S-box uses, and their slots. -/
def loopRegs : List (Reg × Nat) := [(.r10, 42), (.r11, 43), (.r12, 44), (.lr, 45)]

/-- `r0` shifted right by `j`, to `q j`. -/
def wordSlices : List Instr :=
  ([1, 2, 3, 4, 5, 6, 7] : List Nat).map fun j => .mov (q j) (lsrOp (q 0) j)

/-- The bytes from the slices `q j`, to `r0`, with `{63}` added. -/
def wordGather : List Instr :=
  imm32 t0 0x01010101 ++ ([andR (q 0) (q 0) t0] : List Instr) ++
  ([1, 2, 3, 4, 5, 6, 7] : List Nat).flatMap (fun j =>
    [andR t1 (q j) t0, .dp .eor (q 0) (q 0) (rorOp t1 (32 - j))]) ++
  imm32 t0 0x63636363 ++ ([eorR (q 0) (q 0) t0] : List Instr)

/-- SUBWORD of `r0`. -/
def subWord : List Instr :=
  (loopRegs.map fun (r, k) => stS k r) ++ (wordSlices ++ subBytesQ ++ wordGather) ++
  loopRegs.map fun (r, k) => ldS r k

/-- ROTWORD of `r0` plus the round constant, and the next round constant. -/
def rotTail : List Instr :=
  [.mov (q 0) (rorOp (q 0) 8), ldS (q 1) rconSlot, eorR (q 0) (q 0) (q 1),
   .mov (q 2) (lsrOp (q 1) 7), .mov (q 3) (.imm 0x1b), .mul (q 2) (q 2) (q 3),
   .mov (q 1) (.shifted (q 1) .lsl 1), eorR (q 1) (q 1) (q 2), .dp .and (q 1) (q 1) (.imm 0xff),
   stS rconSlot (q 1)]

def rotWordStep : List Instr := subWord ++ rotTail

/-- One word of the schedule. -/
def wordBody : Prog isa :=
  .seq (.block [.cmp .r11 (.imm 0)])
    (.seq (.ite .eq (.block rotWordStep)
        (.seq (.block [.dp .sub (q 1) .r11 (.imm 4), .dp .sub (q 2) .r12 (.imm 8),
            .dp .orr (q 1) (q 1) (.reg (q 2)), .cmp (q 1) (.imm 0)])
          (.ite .eq (.block subWord) (.block []))))
      (.seq (.block [.ldr (q 1) .r9 0, eorR (q 0) (q 0) (q 1), .str (q 0) .r10 0,
          .dp .add .r9 .r9 (.imm 4), .dp .add .r10 .r10 (.imm 4), .dp .add .r11 .r11 (.imm 1),
          .cmp .r11 (.reg .r12)])
        (.seq (.ite .eq (.block [.mov .r11 (.imm 0)]) (.block []))
          (.block [.subs .lr .lr (.imm 1)]))))

/-- One word of the key copied. -/
def copyBody : List Instr :=
  [.ldr (q 0) .r9 0, .str (q 0) .r10 0, .dp .add .r9 .r9 (.imm 4), .dp .add .r10 .r10 (.imm 4),
   .subs .lr .lr (.imm 4)]

/-- The words' loop set up: `3 Nk + 28` words to go. -/
def wordSetup : List Instr :=
  [.dp .sub .r9 .r10 (.reg .r1), .mov .r12 (lsrOp .r1 2), .mov .r11 (.imm 0),
   .dp .add .lr .r12 (.shifted .r12 .lsl 1), .dp .add .lr .lr (.imm 28), .mov (q 1) (.imm 1),
   stS rconSlot (q 1)]

def expandKey : Prog isa :=
  .seq (.block (saveRegs .r3 ++ [movR sb .r3, movR .r9 .r0, movR .r10 .r2, movR .lr .r1]))
    (.seq (.loop (.block copyBody) .ne)
      (.seq (.block wordSetup)
        (.seq (.loop wordBody .ne) (.block (movR .r12 sb :: restoreRegs .r12)))))

end VG.Impl.Aes.Arm
