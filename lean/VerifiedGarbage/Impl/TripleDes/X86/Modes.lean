import VerifiedGarbage.Impl.TripleDes.X86.Ecb
import VerifiedGarbage.Impl.Modes.X86.Seq

/-!
# Triple DES's core for the modes on x86 (32-bit)

`dirCore d`: the verified block function of the direction `d`, called one
block at a time, as a core for the modes (`Impl/Modes/X86/Seq.lean`). Its
slots: the block function's 512-byte working space (slots 0 to 127), the
buffer's one block (slots 128 and 129), and a copy of the 384-byte schedule
(slots 130 to 225), which `prepare` makes so that nothing the modes write
can reach it. `crypt` passes the working space, the buffer and the copy to
the block function in `eax`, `ecx` and `edx`, pushed as its arguments, with
16 bytes of stack. 236 slots in all, with the modes' (`[u64; 118]`).

The block function's output store goes through a pointer into the scratch
buffer that the analysis of constant time does not know as a region's base,
so it forgets what the scratch buffer holds. `crypt` therefore holds the
modes' data pointer and steps left (their slots 4 and 5, `Core.dSlot` and
`Core.nSlot`) in `esi` and `ebp` across the call, which the block function
restores, and stores them back, unchanged, after it.
-/

namespace VG.Impl.TripleDes.X86

open VG.X86
open VG.Impl.Modes.X86 (sb at_ argOp slotAt)
open VG.Spec.TripleDes (Direction)

/-- The buffer's block. -/
def bufSlot : Nat := 128

/-- The schedule's copy. -/
def schedSlot : Nat := 130

/-- The schedule (argument 0, at `ecx`) to its copy, a word at a time
through `eax`. -/
def copySchedule : List Instr :=
  ([.mov .ecx (.mem (argOp 0))] : List Instr) ++
    (List.range 96).flatMap fun w => [.mov .eax (.mem (at_ .ecx (4 * w))), .store (slotAt (schedSlot + w)) .eax]

/-- The modes' data pointer and steps left (`Core.dSlot`, `Core.nSlot`). -/
def dSlot : Nat := schedSlot + 100
def nSlot : Nat := schedSlot + 101

/-- The modes' state to `esi` and `ebp`, and the block function's arguments
to `eax`, `ecx` and `edx`. -/
def cryptSetup : List Instr :=
  [.mov .esi (.mem (slotAt dSlot)), .mov .ebp (.mem (slotAt nSlot)), .mov .eax (.reg sb),
   .mov .ecx (.reg sb), .alu .add .ecx (.imm (BitVec.ofNat 32 (4 * bufSlot))),
   .mov .edx (.reg sb), .alu .add .edx (.imm (BitVec.ofNat 32 (4 * schedSlot)))]

/-- The block function, with the working space, the block and the schedule
pushed as its arguments. -/
def cryptCall (d : Direction) : Prog isa :=
  .frame (.push [.eax, .ecx, .edx])
    (match d with
    | .encrypt => .call "vg_triple_des_encrypt_block" encryptBlock
    | .decrypt => .call "vg_triple_des_decrypt_block" decryptBlock)
    (.pop .eax 3)

/-- The modes' state back to its slots. -/
def cryptDone : List Instr := [.store (slotAt dSlot) .esi, .store (slotAt nSlot) .ebp]

/-- Triple DES's core for the modes, in the direction `d`. -/
def dirCore (d : Direction) : Modes.X86.Core where
  prepare := .block copySchedule
  crypt := .seq (.block cryptSetup) (.seq (cryptCall d) (.block cryptDone))
  slots := schedSlot + 96
  total := schedSlot + 106
  buf := bufSlot
  G := 1
  bw := 2
  stack := 16

/-- `vg_triple_des_cbc_encrypt`, with its scratch buffer as the fifth argument. -/
def cbcEncrypt : Prog isa := (dirCore .encrypt).seq (Modes.Mode.cbcEnc 2)

/-- `vg_triple_des_cbc_decrypt`, with its scratch buffer as the fifth argument. -/
def cbcDecrypt : Prog isa := (dirCore .decrypt).seq (Modes.Mode.cbcDec 2)

end VG.Impl.TripleDes.X86
