module

public import VerifiedGarbage.Impl.Aes.Arm.Crypt

/-!
# AES counter mode on ARMv7, bitsliced

`vg_aes_ctr32(schedule = r0, rounds = r1, counter = r2, data = r3, n = [sp],
scratch = [sp, #4])` (`Spec/Gcm/Contract.lean`), and `vg_aes_ctr32_to`, with
the destination in `r6` and `data` the source.

The scratch buffer holds, in 4-byte slots: the S-boxes' spills and the round
keys' pointer (0–31, `Crypt.lean`), the callee-saved registers (32–40), the
first three words of the counter block (41–43) and the counter (44), and
between groups' uses of them the data's pointer, the blocks left, the first
round key's address and the destination's pointer (45–48); then the bitsliced
round keys, up to byte `lastKey`. The final counter is written back first.
The round keys are bitsliced (`keyBody`), from the last down, with the
schedule's in `r12` and `lr` counting them; then each group of two blocks (or
the last one) has its counter blocks made in the state registers, encrypted
and XORed into the data.

Only the pointers, `rounds` and `n` decide addresses and branches.
-/

@[expose] public section

namespace VG.Impl.Aes.Arm

open VG.Arm

/-- The bytes of the scratch buffer the block functions use. -/
def scratchUsed : Nat := 704

/-! ## Slots -/

def savedSlot : Nat := 32
/-- Word `k` of the counter block, `k < 3`, and the counter. -/
def cW (k : Nat) : Nat := 41 + k
def cNum : Nat := 44
def dSlot : Nat := 45
def lSlot : Nat := 46
def dstSlot : Nat := 48

def savedRegs : List (Reg × Nat) :=
  [(.r4, savedSlot), (.r5, savedSlot + 1), (.r6, savedSlot + 2), (.r7, savedSlot + 3), (.r8, savedSlot + 4),
   (.r9, savedSlot + 5), (.r10, savedSlot + 6), (.r11, savedSlot + 7), (.lr, savedSlot + 8)]

/-- Save and restore the callee-saved registers, with the scratch buffer's
base in `b`. -/
def saveRegs (b : Reg) : List Instr := savedRegs.map fun (r, k) => .str r b (4 * k)
def restoreRegs (b : Reg) : List Instr := savedRegs.map fun (r, k) => .ldr r b (4 * k)

/-! ## The prologue and the round keys -/

/-- The scratch buffer's base to `r12`, the registers saved, the counter block
to its slots and the final counter written back. -/
def prologue : List Instr :=
  ([.ldrSp .r12 4] : List Instr) ++ saveRegs .r12 ++
  [.ldr t0 .r2 0, .str t0 .r12 (4 * cW 0), .ldr t0 .r2 4, .str t0 .r12 (4 * cW 1),
   .ldr t0 .r2 8, .str t0 .r12 (4 * cW 2),
   .ldr t0 .r2 12, .rev t0 t0, .str t0 .r12 (4 * cNum),
   .ldrSp t1 0, .dp .add t0 t0 (.reg t1), .rev t0 t0, .str t0 .r2 12]

/-- The last round key's places to `kp` and `r12`, the number of round keys to
`lr`, and the data's pointer to `r8`. -/
def keySetup : List Instr :=
  [.dp .add kp .r12 (.imm (BitVec.ofNat 32 lastKey)), .dp .add .r12 .r0 (.shifted .r1 .lsl 4),
   .dp .add .lr .r1 (.imm 1), movR .r8 .r3]

/-- Back a round key, and whether one is left. -/
def keyStep : List Instr :=
  [.dp .sub .r12 .r12 (.imm 16), .dp .sub kp kp (.imm 32), .subs .lr .lr (.imm 1)]

def keyBody : Prog isa := .seq keyFront (.block keyStep)

/-- The first round key to `r12`, the data's pointer to `r10`, `n` to `r11`
and the scratch buffer's base to `sb`. -/
def keyDone : List Instr :=
  [.dp .add .r12 kp (.imm 32), movR .r10 .r8, .ldrSp .r11 0, .ldrSp sb 4]

/-! ## Groups -/

def groupSave : List Instr :=
  [stS dSlot .r10, stS lSlot .r11, stS fkSlot .r12, movR kp .r12]

def groupLoad : List Instr := [ldS .r10 dSlot, ldS .r11 lSlot, ldS .r12 fkSlot]

/-- Counter block `b` of the group. -/
def ctrBlock (b : Nat) : List Instr :=
  [ldS (q b) (cW 0), ldS (q (2 + b)) (cW 1), ldS (q (4 + b)) (cW 2), ldS t0 cNum,
   .dp .add t0 t0 (.imm (BitVec.ofNat 32 b)), .rev (q (6 + b)) t0]

def ctrBlocks : List Instr :=
  ctrBlock 0 ++ ctrBlock 1 ++
  ([ldS t0 cNum, .dp .add t0 t0 (.imm 2), stS cNum t0] : List Instr)

/-- The destination's register, and its pointer loaded, set up and advanced,
if it is not the source's. -/
def dstReg (to : Bool) : Reg := if to then kp else .r10
def dstLoad (to : Bool) : List Instr := if to then [ldS kp dstSlot] else []
def dstSave (to : Bool) : List Instr := if to then [ldS kp (savedSlot + 2), stS dstSlot kp] else []
def dstStep (to : Bool) : List Instr :=
  if to then [.dp .add kp kp (.imm 32), stS dstSlot kp] else []

/-- Word `k` of the group, with the keystream XORed in. -/
def xorWord (to : Bool) (k : Nat) : List Instr :=
  [.ldr .lr .r10 (4 * k), eorR .lr .lr (q (2 * (k % 4) + k / 4)), .str .lr (dstReg to) (4 * k)]

def xorFullG (to : Bool) : List Instr :=
  (List.range 8).flatMap (xorWord to) ++
  ([.dp .add .r10 .r10 (.imm 32), .dp .sub .r11 .r11 (.imm 2)] : List Instr)

def xorTailG (to : Bool) : List Instr :=
  (List.range 4).flatMap (xorWord to) ++ ([.mov .r11 (.imm 0)] : List Instr)

def groupG (to : Bool) : Prog isa :=
  .seq (.block (groupSave ++ ctrBlocks))
    (.seq encrypt2
      (.seq (.block (groupLoad ++ ([.mov kp (lsrOp .r11 1), .cmp kp (.imm 0)] : List Instr) ++ dstLoad to))
        (.seq (.ite .ne (.block (xorFullG to)) (.block (xorTailG to)))
          (.block (dstStep to ++ ([.cmp .r11 (.imm 0)] : List Instr))))))

/-! ## The whole function -/

def ctr32Gen (to : Bool) : Prog isa :=
  .seq (.block (prologue ++ keySetup))
    (.seq (.loop keyBody .ne)
      (.seq (.block (keyDone ++ dstSave to ++ ([.cmp .r11 (.imm 0)] : List Instr)))
        (.seq (.ite .eq (.block []) (.loop (groupG to) .ne)) (.block (.ldrSp .r12 4 :: restoreRegs .r12)))))

def ctr32 : Prog isa := ctr32Gen false
def ctr32To : Prog isa := ctr32Gen true

end VG.Impl.Aes.Arm
