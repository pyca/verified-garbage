module

public import VerifiedGarbage.Impl.Camellia.X86.Prepared

/-!
# Camellia ECB, bitsliced, on x86 (32-bit)

`ecb dir(schedule, rounds, data, n, scratch)`, cdecl (the arguments at
`[esp + 4]` … `[esp + 20]`): `vg_camellia_ecb_encrypt` and
`vg_camellia_ecb_decrypt` with their working space in the scratch buffer
(`Layers.lean` has its layout), which the artifact allocates on the stack.

* The callee-saved registers are saved in the scratch buffer, whose address
  moves to `edi`.
* The subkeys are bitsliced into the table at slot 104, for 18 rounds or 24
  (three groups of six rounds or four), in the order the rounds use them:
  the stored order for encryption; for decryption the order RFC 3713
  §2.3.3 swaps them into, `kw3, kw4`, then the subkeys between `kw2` and
  `kw3` from the last back to the first, then `kw1, kw2`. Decryption then
  runs the same rounds as encryption.
* Each group of up to eight blocks is copied to the tail buffer, run through
  the rounds by a call of `vg_camellia_crypt_prepared` (`Prepared.lean`),
  whose arguments are pushed in a frame (16 bytes of stack with the return
  address; the number of rounds is its own second stack argument, the
  scratch buffer the working space), and copied back. The data pointer and
  the blocks left wait in their slots, stored again after each copy (the
  analysis of constant time forgets what the buffer holds after a store
  through another pointer than `edi`), which the call keeps.

Only the pointers, `rounds`, `n`, and what is computed from them (the
copies' pointers and counts, `kp`, the loop tests, and the slots holding
them) are public; no address and no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Camellia.X86

open VG.X86 VG.Impl.Aes.X86

/-! ## The subkeys -/

/-- Plane `j` of the subkey's word in slot 0, to word `w` of the entry at
`kp`: bit `j` of each byte, masked into `ebx` and spread over its byte by
three shifted XORs (their bits never overlap), through `edx`. -/
def keyPlane (w j : Nat) : List Instr :=
  [movS .ebx 0] ++ (if j = 0 then [] else [shrI .ebx j]) ++
  [andI .ebx 0x01010101, movR .edx .ebx, rorI .edx 31, xorR .ebx .edx, movR .edx .ebx, rorI .edx 30,
   xorR .ebx .edx, movR .edx .ebx, rorI .edx 28, xorR .ebx .edx, .store (slotAt kp (8 * w + j)) .ebx]

/-- Bitslice the subkey at `[ecx + d]` (its bytes the most significant
first, so that a little-endian load puts byte `i` at bits `8 i … 8 i + 7`)
into the entry at `kp`, and step `kp` to the next entry. -/
def keyOne (d : Nat) : List Instr :=
  (List.range 2).flatMap (fun w => [.mov .eax (.mem (at_ .ecx (d + 4 * w))), st 0 .eax] ++
    (List.range 8).flatMap (keyPlane w)) ++ [addI kp 64]

/-- Encryption's table, for `g` groups: the `8 g + 2` subkeys in order. -/
def encKeys (g : Nat) : Prog isa :=
  .seq (.block ([.mov .ecx (.mem (argOp 0))] ++ kpAt keySlot ++ [movI .ebp (BitVec.ofNat 32 (8 * g + 2))]))
    (.loop (.block (keyOne 0 ++ [addI .ecx 8, subI .ebp 1])) .ne)

/-- Decryption's table, for `g` groups: `kw3, kw4` (words `8 g`, `8 g + 1`),
words `8 g - 1` down to 2, then `kw1, kw2`. -/
def decKeys (g : Nat) : Prog isa :=
  .seq (.block ([.mov .ecx (.mem (argOp 0))] ++ kpAt keySlot ++ [addI .ecx (BitVec.ofNat 32 (64 * g))] ++
      keyOne 0 ++ keyOne 8 ++ [subI .ecx 8, movI .ebp (BitVec.ofNat 32 (8 * g - 2))]))
    (.seq (.loop (.block (keyOne 0 ++ [subI .ecx 8, subI .ebp 1])) .ne)
      (.block ([subI .ecx 8] ++ keyOne 0 ++ keyOne 8)))

def keys (dir : Dir) (g : Nat) : Prog isa :=
  match dir with | .encrypt => encKeys g | .decrypt => decKeys g

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
def group : Prog isa := .seq copyIn (.seq cryptCall (.seq copyOut advance))

/-- The data pointer and the count to their slots, and the groups. -/
def groups : Prog isa :=
  .seq (.block [.mov .eax (.mem (argOp 2)), st dSlot .eax, .mov .eax (.mem (argOp 3)), st nSlot .eax,
      .alu .test .eax (.reg .eax)])
    (.ite .e (.block []) (.loop group .ne))

/-- The whole function: the table for 18 rounds or 24, and the groups. -/
def ecb (dir : Dir) : Prog isa :=
  .seq (.block (saveRegs 4 ++ [.mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm 18)]))
    (.seq (.ite .e (keys dir 3) (keys dir 4)) (.seq groups (.block restoreRegs)))

end VG.Impl.Camellia.X86
