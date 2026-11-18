module

public import VerifiedGarbage.Impl.Modes.X86.Wide
public import VerifiedGarbage.Impl.Modes.CbcChained
public import VerifiedGarbage.Impl.TripleDes.X86.Block
public import VerifiedGarbage.Impl.TripleDes.X86.Bitsliced

/-!
# Triple DES's cores for the modes on x86 (32-bit)

Two cores: `dirCore`, a block at a time, for the modes whose blocks each
need the one before (CBC encryption, OFB, CFB64 encryption, CFB8), and
`wideCore` (below), the bitsliced function on 32 blocks, for CBC and CFB64
decryption.

`dirCore`: the verified encryption block function, called one
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

@[expose] public section

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
def cryptCall : Prog isa :=
  .frame (.push [.eax, .ecx, .edx]) (.call "vg_triple_des_encrypt_block" encryptBlock) (.pop .eax 3)

/-- The modes' state back to its slots. -/
def cryptDone : List Instr := [.store (slotAt dSlot) .esi, .store (slotAt nSlot) .ebp]

/-- Triple DES's core for the modes, a block at a time: encryption. -/
def dirCore : Modes.X86.Core where
  prepare := .block copySchedule
  crypt := .seq (.block cryptSetup) (.seq cryptCall (.block cryptDone))
  slots := schedSlot + 96
  total := schedSlot + 106
  buf := bufSlot
  G := 1
  bw := 2
  stack := 16

/-! ## The bitsliced core

`wideCore d`: the bitsliced function of the direction `d`
(`Bitsliced.lean`) as a core of 32 blocks, for the modes whose blocks can
be enciphered independently (`Impl/Modes/X86/Wide.lean`): CBC and CFB64
decryption. Its slots: the function's working space (slots 0 to 195, with
the buffer's 32 blocks from slot 132 on) and the copy of the schedule
(slots 196 to 291). `crypt` passes the working space, `sb` itself, and the
copy to the function, pushed as its arguments, with 12 bytes of stack; the
function stores only through the working space's address, at fixed
offsets, so the analysis of constant time keeps what the modes' slots
hold. 302 slots in all, with the modes' (`[u64; 151]`).

The modes take the blocks in groups of 32, the buffer, while 32 are left,
then of 16, 8, 4 and 2 (`levels`), then one: each group is one call of the
function, which costs the same for any number of the buffer's blocks. -/

/-- The schedule's copy, after the bitsliced function's working space. -/
def wideSchedSlot : Nat := Bitslice.wsWords

/-- The schedule (argument 0, at `ecx`) to its copy, a word at a time
through `eax`. -/
def copyScheduleWide : List Instr :=
  ([.mov .ecx (.mem (argOp 0))] : List Instr) ++
    (List.range 96).flatMap fun w => [.mov .eax (.mem (at_ .ecx (4 * w))), .store (slotAt (wideSchedSlot + w)) .eax]

/-- The address of the schedule's copy to `eax`. -/
def wideSetup : List Instr :=
  [.mov .eax (.reg sb), .alu .add .eax (.imm (BitVec.ofNat 32 (4 * wideSchedSlot)))]

/-- The bitsliced function, with the working space and the schedule's copy
pushed as its arguments. -/
def wideCall (d : Direction) : Prog isa :=
  .frame (.push [.eax, sb])
    (match d with
    | .encrypt => .call "vg_triple_des_encrypt_batch" Bitslice.encryptBatch
    | .decrypt => .call "vg_triple_des_decrypt_batch" Bitslice.decryptBatch)
    (.pop .eax 2)

/-- Triple DES's bitsliced core for the modes, in the direction `d`. -/
def wideCore (d : Direction) : Modes.X86.Core where
  prepare := .block copyScheduleWide
  crypt := .seq (.block wideSetup) (wideCall d)
  slots := wideSchedSlot + 96
  total := wideSchedSlot + 106
  buf := Bitslice.bufSlot
  G := 32
  bw := 2
  stack := 16

/-- The sizes of the groups of blocks the modes whose blocks are independent
take, in turn, before single blocks. -/
def levels : List Nat := [32, 16, 8, 4, 2]

/-- `vg_triple_des_cbc_encrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcEncryptChained : Prog isa := dirCore.seq (Modes.Mode.cbcEncChained 2)

/-- `vg_triple_des_cbc_decrypt_chained`, with its scratch buffer as the fifth argument. -/
def cbcDecryptChained : Prog isa :=
  (wideCore .decrypt).seqLevels (Modes.Mode.cbcDecWide 2) levels (Modes.Mode.cbcDecChained 2)

end VG.Impl.TripleDes.X86
