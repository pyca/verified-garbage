module

public import VerifiedGarbage.Impl.TripleDes.X86.Common
public import VerifiedGarbage.Impl.CmacTripleDes.X86.Round
public import VerifiedGarbage.Spec.TripleDes

/-! The Triple DES encryption block on x86 (32-bit),
`vg_triple_des_encrypt_block` (`encryptBlock`: the schedule, the block and a
working space as its arguments): CMAC's block
(`Impl/CmacTripleDes/X86/Round.lean`, `block`: the S-boxes as multiplexer
trees on two halves of 24 bits), on the block as two big-endian words, with
its slots the first words of the working space and the caller's registers
saved after them.

The modes whose blocks each need the one before call it, a block at a time
(`Modes.lean`); ECB and the modes whose blocks are independent call the
bitsliced functions (`Bitsliced.lean`), 32 blocks at a time. Key expansion
saves and restores the caller's registers as `saveWithArg` and
`blockRestore` do. -/

@[expose] public section

namespace VG.Impl.TripleDes.X86
open VG.X86

def savedRegs : List Reg := [.ebp, .ebx, .esi, .edi]
def saveWithArg (slot : Nat) : List Instr :=
  ([.mov .eax (.mem (memOp .esp (4 * slot)))] : List Instr) ++
    savedRegs.zipIdx.map (fun (r, i) => .store (memOp .eax (4 * i)) r) ++
    [rr .ebp .eax]
def blockRestore : List Instr :=
  [rr .eax .ebp] ++ savedRegs.zipIdx.map fun (r, i) => .mov r (.mem (memOp .eax (4 * i)))
/-- Where the encryption block saves the caller's registers: the words
after its 21 slots. -/
def encSaveAt : Nat := 128

/-- The working space into `ebp`, with the caller's registers saved in it. -/
def encSave : List Instr :=
  ([.mov .eax (.mem (memOp .esp 12))] : List Instr) ++
    savedRegs.zipIdx.map (fun (r, i) => .store (memOp .eax (encSaveAt + 4 * i)) r) ++
    [rr .ebp .eax]

/-- The block into `eax:edx`, its high and low words as big-endian integers,
and the schedule's address into `esi`. -/
def encLoad : List Instr :=
  [.mov .ecx (.mem (memOp .esp 8)), .mov .eax (.mem (memOp .ecx 0)), .mov .edx (.mem (memOp .ecx 4)),
    .bswap .eax, .bswap .edx, .mov .esi (.mem (memOp .esp 4))]

/-- The caller's registers back, `ebp` last, and then `eax:edx` to the
block: the store is through a pointer, after every load from the working
space. -/
def encStore : List Instr :=
  [.bswap .eax, .bswap .edx, rr .ecx .ebp, .mov .ebx (.mem (memOp .ecx (encSaveAt + 4))),
    .mov .esi (.mem (memOp .ecx (encSaveAt + 8))), .mov .edi (.mem (memOp .ecx (encSaveAt + 12))),
    .mov .ebp (.mem (memOp .ecx encSaveAt)), .mov .ecx (.mem (memOp .esp 8)),
    .store (memOp .ecx 0) .eax, .store (memOp .ecx 4) .edx]

def encryptBlock : Prog isa :=
  .seq (.block (encSave ++ encLoad)) (.seq Impl.CmacTripleDes.X86.block (.block encStore))
end VG.Impl.TripleDes.X86
