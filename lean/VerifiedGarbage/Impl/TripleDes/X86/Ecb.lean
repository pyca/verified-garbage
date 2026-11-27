module

public import VerifiedGarbage.Impl.TripleDes.X86.Block
public import VerifiedGarbage.Impl.TripleDes.X86.Bitsliced

/-!
# Triple DES ECB on x86 (32-bit)

`ecb d(schedule, data, n, scratch)`, cdecl: `vg_triple_des_ecb_encrypt` and
`vg_triple_des_ecb_decrypt` with their working space in the scratch buffer,
which the artifact allocates on the stack.

The callee-saved registers are saved in the scratch buffer (its words 128
to 131, which the bitsliced functions keep), whose address moves to `ebp`,
with the schedule in `ebx`, the data pointer in `esi` and the blocks left in
`edi`. Each group of up to 32 blocks is copied to the blocks of the
bitsliced function's working space (`Bitsliced.lean`), the scratch buffer
itself, encrypted or decrypted there by a call of
`vg_triple_des_encrypt_batch` or `vg_triple_des_decrypt_batch` (with 16
bytes of stack), which works on all 32 whatever the group holds, and copied
back. The count of a group, `min(edi, 32)`, is computed again wherever it
is used, since the call keeps only the callee-saved registers.

Only the pointers, `n`, and what is computed from them are public; no
address and no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.TripleDes.X86.Ecb
open VG.X86 VG.Impl.TripleDes.X86
open VG.Spec.TripleDes (Direction)

def save : List Instr := savedRegs.zipIdx.map fun (r, i) => .store (memOp .eax (512 + 4 * i)) r
def setup : List Instr :=
  [rr .ebp .eax, .mov .ebx (.mem (memOp .esp 4)), .mov .esi (.mem (memOp .esp 8)),
    .mov .edi (.mem (memOp .esp 12)), .alu .cmp .edi (.imm 0)]
def restore : List Instr := [rr .eax .ebp] ++
  savedRegs.zipIdx.map fun (r, i) => .mov r (.mem (memOp .eax (512 + 4 * i)))

/-- `ecx := min(edi, 32)`, the blocks of this group. -/
def countR : Prog isa :=
  .seq (.block [rr .ecx .edi, .alu .cmp .edi (.imm 32)]) (.ite .b (.block []) (.block [imm .ecx 32]))

/-- Copy `ecx` blocks from `src` to `dst` (through `eax`), which move past them. -/
def copyBlocks (src dst : Reg) : Prog isa :=
  .loop (.block [.mov .eax (.mem (memOp src 0)), .store (memOp dst 0) .eax, .mov .eax (.mem (memOp src 4)),
    .store (memOp dst 4) .eax, .alu .add src (.imm 8), .alu .add dst (.imm 8), .alu .sub .ecx (.imm 1)]) .ne

/-- `edx :=` the address of the blocks in the working space. -/
def bufAddr : List Instr :=
  [rr .edx .ebp, .alu .add .edx (.imm (BitVec.ofNat 32 (4 * Bitslice.bufSlot)))]

/-- The group's blocks to the working space; `esi` moves past them. -/
def copyIn : Prog isa := .seq countR (.seq (.block bufAddr) (copyBlocks .esi .edx))

/-- `esi` back to the group's first block: eight times the count less. -/
def rewind : Prog isa :=
  .seq countR (.block [.alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx),
    .alu .sub .esi (.reg .ecx)])

/-- The bitsliced function, with the working space and the schedule pushed
as its arguments. -/
def batchCall (d : Direction) : Prog isa :=
  .frame (.push [.ebx, .ebp])
    (match d with
    | .encrypt => .call "vg_triple_des_encrypt_batch" Bitslice.encryptBatch
    | .decrypt => .call "vg_triple_des_decrypt_batch" Bitslice.decryptBatch)
    (.pop .eax 2)

/-- The working space's blocks back to the group's; `esi` moves past them. -/
def copyOut : Prog isa := .seq countR (.seq (.block bufAddr) (copyBlocks .edx .esi))

/-- The blocks left (Z set when there are none). -/
def advance : Prog isa := .seq countR (.block [.alu .sub .edi (.reg .ecx)])

/-- 32 blocks, or the last one to 31. -/
def group (d : Direction) : Prog isa :=
  .seq copyIn (.seq rewind (.seq (batchCall d) (.seq copyOut advance)))

def ecb (d : Direction) : Prog isa :=
  .seq (.block [.mov .eax (.mem (memOp .esp 16))])
    (.seq (.block (save ++ setup))
      (.seq (.ite .e (.block []) (.loop (group d) .ne)) (.block restore)))
def encrypt : Prog isa := ecb .encrypt
def decrypt : Prog isa := ecb .decrypt
end VG.Impl.TripleDes.X86.Ecb
