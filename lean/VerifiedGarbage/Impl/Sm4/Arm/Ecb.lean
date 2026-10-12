module

public import VerifiedGarbage.Impl.Sm4.Arm.Layers

/-!
# SM4 ECB, bitsliced, on ARMv7

`ecb dir(schedule = r0, data = r1, n = r2, scratch = r3)`:
`vg_sm4_ecb_encrypt` and `vg_sm4_ecb_decrypt` with their working space in
the scratch buffer (`Layers.lean` has its layout), which the artifact
allocates on the stack.

* The callee-saved registers are saved, the scratch buffer moves to `r8`,
  the schedule's pointer to `r12`; the data pointer and `n` stay in `r1`
  and `r2`, which the round keys' bitslicing leaves alone.
* The round keys are bitsliced into the table at slot 96, in the order the
  rounds use them: `rk₀ … rk₃₁` for encryption, `rk₃₁ … rk₀` for decryption
  (§7.2), counting in `lr`. Decryption then runs the same rounds as
  encryption.
* Each group of up to eight blocks is copied to the tail buffer,
  bitsliced, run through the 32 rounds (eight times four, the state's words
  taking the new words in turn), and copied back; the data pointer and the
  blocks left wait in their slots during the rounds, which use every
  register.

Only the pointers, `n`, and what is computed from them (the copies'
pointers and counts, `kp`, the loop tests, and the slots holding them) are
public; no address and no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Sm4.Arm

open VG.Arm VG.Impl.Aes.Arm
open VG.Impl.Sm4 (Lin)

inductive Dir | encrypt | decrypt
  deriving DecidableEq, Repr

/-! ## The round keys -/

/-- `kp := ` the address of slot `k`. -/
def kpAt (k : Nat) : Instr := .dp .add kp sb (.imm (BitVec.ofNat 32 (4 * k)))

/-- Encryption's table: round key `i` (at `r12`) to entry `i`. -/
def encKeys : Prog isa :=
  .seq (.block [kpAt tableSlot, .mov .lr (.imm 32)])
    (.loop (.block (keyOne ++ [.dp .add .r12 .r12 (.imm 4), .dp .add kp kp (.imm 32), .subs .lr .lr (.imm 1)])) .ne)

/-- Decryption's table: round key `i` to entry `31 - i`. -/
def decKeys : Prog isa :=
  .seq (.block [kpAt (tableSlot + 8 * 31), .mov .lr (.imm 32)])
    (.loop (.block (keyOne ++ [.dp .add .r12 .r12 (.imm 4), .dp .sub kp kp (.imm 32), .subs .lr .lr (.imm 1)])) .ne)

def keys : Dir → Prog isa
  | .encrypt => encKeys
  | .decrypt => decKeys

/-! ## Eight blocks -/

/-- Four rounds, `kp += 128`, and whether `kp` is at the table's end. -/
def roundsBody (l : Lin) : List Instr :=
  rounds4 l ++ [.dp .add kp kp (.imm 128), .dp .sub t0 kp (.reg sb),
    .cmp t0 (.imm (BitVec.ofNat 32 (4 * tableEnd)))]

/-- The 32 rounds, with `kp` from the table's start to its end. -/
def rounds (l : Lin) : Prog isa := .seq (.block [kpAt tableSlot]) (.loop (.block (roundsBody l)) .ne)

/-- The eight blocks of the tail buffer, in place. -/
def crypt8 : Prog isa := .seq (.block toBs) (.seq (rounds .enc) (.block fromBs))

/-! ## The groups -/

/-- Copy `r3` blocks from `r0` to `r12` (through `t0`). -/
def copyBlocks : Prog isa :=
  .loop (.block [.ldr t0 .r0 0, .str t0 .r12 0, .ldr t0 .r0 4, .str t0 .r12 4,
      .ldr t0 .r0 8, .str t0 .r12 8, .ldr t0 .r0 12, .str t0 .r12 12,
      .dp .add .r0 .r0 (.imm 16), .dp .add .r12 .r12 (.imm 16), .subs .r3 .r3 (.imm 1)]) .ne

/-- `r3 := min(r2, 8)`, the blocks of this group. -/
def groupCount : Prog isa :=
  .seq (.block [.mov t0 (lsrOp .r2 3), .cmp t0 (.imm 0)])
    (.ite .ne (.block [.mov .r3 (.imm 8)]) (.block [movR .r3 .r2]))

/-- The tail buffer's address, in `r`. -/
def tailAddr (r : Reg) : Instr := .dp .add r sb (.imm (BitVec.ofNat 32 (4 * tailSlot)))

/-- The group's blocks (at `r1`) to the tail buffer. -/
def copyIn : Prog isa := .seq groupCount (.seq (.block [movR .r0 .r1, tailAddr .r12]) copyBlocks)

/-- The tail buffer back to the group's blocks. -/
def copyOut : Prog isa := .seq groupCount (.seq (.block [tailAddr .r0, movR .r12 .r1]) copyBlocks)

/-- The eight blocks of the tail buffer, with the data pointer and the blocks
left in their slots meanwhile: the rounds use every register, and store
only through `sb`, which keeps the slots' values public for the analysis of
constant time (a store through another pointer would forget them, so the
copies keep these values in `r1` and `r2`). -/
def cryptSaved : Prog isa :=
  .seq (.block [stS dSlot .r1, stS nSlot .r2]) (.seq crypt8 (.block [ldS .r1 dSlot, ldS .r2 nSlot]))

/-- On to the next group, or none left (Z set). -/
def advance : Prog isa := .seq groupCount (.block [.dp .add .r1 .r1 (.imm 128), .subs .r2 .r2 (.reg .r3)])

/-- Eight blocks, or the last one to seven. -/
def group : Prog isa := .seq copyIn (.seq cryptSaved (.seq copyOut advance))

/-- The whole function: the table, then the groups. -/
def ecb (dir : Dir) : Prog isa :=
  .seq (.block (saveRegs .r3 ++ [movR sb .r3, movR .r12 .r0]))
    (.seq (keys dir)
      (.seq (.block [.cmp .r2 (.imm 0)])
        (.seq (.ite .eq (.block []) (.loop group .ne)) (.block ([movR .r12 sb] ++ restoreRegs .r12)))))

end VG.Impl.Sm4.Arm
