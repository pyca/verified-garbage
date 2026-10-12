module

public import VerifiedGarbage.Impl.Sm4.X86.Layers

/-!
# SM4 ECB, bitsliced, on x86 (32-bit)

`ecb dir(schedule, data, n, scratch)`, cdecl (the arguments at
`[esp + 4]` … `[esp + 16]`): `vg_sm4_ecb_encrypt` and `vg_sm4_ecb_decrypt`
with their working space in the scratch buffer (`Layers.lean` has its
layout), which the artifact allocates on the stack.

* The callee-saved registers are saved in the scratch buffer, whose address
  moves to `edi`.
* The round keys are bitsliced into the table at slot 96, in the order the
  rounds use them: `rk₀ … rk₃₁` for encryption, `rk₃₁ … rk₀` for decryption
  (§7.2), counting in `ebp`, the schedule's pointer in `ecx`. Decryption
  then runs the same rounds as encryption.
* The data pointer and `n` go to their slots. Each group of up to eight
  blocks is copied to the tail buffer, bitsliced, run through the 32 rounds
  (eight times four, the state's words taking the new words in turn), and
  copied back. The rounds use every register, so the data pointer and the
  blocks left wait in their slots, stored again after each copy (the
  analysis of constant time forgets what the buffer holds after a store
  through another pointer than `edi`).

Only the pointers, `n`, and what is computed from them (the copies'
pointers and counts, `kp`, the loop tests, and the slots holding them) are
public; no address and no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Sm4.X86

open VG.X86 VG.Impl.Aes.X86

inductive Dir | encrypt | decrypt
  deriving DecidableEq, Repr

/-! ## The round keys -/

/-- `kp := ` the address of slot `k`. -/
def kpAt (k : Nat) : List Instr := [movR kp .edi, addI kp (BitVec.ofNat 32 (4 * k))]

/-- The loop over the round keys: round key `i` (at `ecx`) to the entry at
`kp`, which `step` moves to the next. -/
def keyLoop (step : Instr) : Prog isa :=
  .loop (.block (keyOne ++ [addI .ecx 4, step, subI .ebp 1])) .ne

/-- Encryption's table: round key `i` to entry `i`. -/
def encKeys : Prog isa :=
  .seq (.block ([.mov .ecx (.mem (argOp 0))] ++ kpAt tableSlot ++ [movI .ebp 32])) (keyLoop (addI kp 32))

/-- Decryption's table: round key `i` to entry `31 - i`. -/
def decKeys : Prog isa :=
  .seq (.block ([.mov .ecx (.mem (argOp 0))] ++ kpAt (tableSlot + 8 * 31) ++ [movI .ebp 32]))
    (keyLoop (subI kp 32))

def keys : Dir → Prog isa
  | .encrypt => encKeys
  | .decrypt => decKeys

/-! ## Eight blocks -/

/-- Four rounds, `kp += 128`, and whether `kp` is at the table's end. -/
def roundsBody (l : VG.Impl.Sm4.Lin) : List Instr :=
  rounds4 l ++ [addI kp 128, movR .eax kp, subR .eax .edi, .alu .cmp .eax (.imm (BitVec.ofNat 32 (4 * tableEnd)))]

/-- The 32 rounds, with `kp` from the table's start to its end. -/
def rounds (l : VG.Impl.Sm4.Lin) : Prog isa := .seq (.block (kpAt tableSlot)) (.loop (.block (roundsBody l)) .ne)

/-- The eight blocks of the tail buffer, in place. -/
def crypt8 : Prog isa := .seq (.block toBs) (.seq (rounds .enc) (.block fromBs))

/-! ## The groups -/

/-- Copy `ecx` blocks from `edx` to `ebx` (through `eax`). -/
def copyBlocks : Prog isa :=
  .loop (.block [.mov .eax (.mem (at_ .edx 0)), .store (at_ .ebx 0) .eax, .mov .eax (.mem (at_ .edx 4)),
      .store (at_ .ebx 4) .eax, .mov .eax (.mem (at_ .edx 8)), .store (at_ .ebx 8) .eax,
      .mov .eax (.mem (at_ .edx 12)), .store (at_ .ebx 12) .eax, addI .edx 16, addI .ebx 16, subI .ecx 1]) .ne

/-- `ecx := min(ebp, 8)`, the blocks of this group. -/
def countR : Prog isa :=
  .seq (.block [movR .ecx .ebp, .alu .cmp .ebp (.imm 8)]) (.ite .b (.block []) (.block [movI .ecx 8]))

/-- The data pointer and the blocks left from their slots to `esi` and `ebp`,
and the blocks of this group to `ecx`. -/
def groupCount : Prog isa := .seq (.block [movS .esi dSlot, movS .ebp nSlot]) countR

/-- `r := ` the tail buffer's address. -/
def tailAddr (r : Reg) : List Instr := [movR r .edi, addI r (BitVec.ofNat 32 (4 * tailSlot))]

/-- The group's blocks to the tail buffer, and the data pointer and the
blocks left back to their slots. -/
def copyIn : Prog isa :=
  .seq groupCount (.seq (.block ([movR .edx .esi] ++ tailAddr .ebx))
    (.seq copyBlocks (.block [st dSlot .esi, st nSlot .ebp])))

/-- The tail buffer back to the group's blocks. -/
def copyOut : Prog isa := .seq groupCount (.seq (.block (tailAddr .edx ++ [movR .ebx .esi])) copyBlocks)

/-- On to the next group, the data pointer and the blocks left (still in
`esi` and `ebp`) back to their slots (Z set when none are left). -/
def advance : Prog isa :=
  .seq countR (.block [addI .esi 128, subR .ebp .ecx, st dSlot .esi, st nSlot .ebp])

/-- Eight blocks, or the last one to seven. -/
def group : Prog isa := .seq copyIn (.seq crypt8 (.seq copyOut advance))

/-- The whole function: the table, then the groups. -/
def ecb (dir : Dir) : Prog isa :=
  .seq (.block (saveRegs 3))
    (.seq (keys dir)
      (.seq (.block [.mov .eax (.mem (argOp 1)), st dSlot .eax, .mov .eax (.mem (argOp 2)), st nSlot .eax,
          .alu .test .eax (.reg .eax)])
        (.seq (.ite .e (.block []) (.loop group .ne)) (.block restoreRegs))))

end VG.Impl.Sm4.X86
