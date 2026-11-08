module

public import VerifiedGarbage.Impl.Aes.X86.AesNi

/-!
# AES with AES-NI on x86 (32-bit): encryption and decryption of whole blocks

`vg_aes_encrypt_blocks_aesni(schedule, rounds, data, n, scratch)` and
`vg_aes_decrypt_blocks_aesni`, cdecl (the arguments are at `[esp + 4]` …
`[esp + 20]`), with the contracts of `vg_aes_encrypt_blocks` and
`vg_aes_decrypt_blocks` (`Spec/Aes/Contract.lean`), for CPUs with AES-NI.

As `vg_aes_ctr32_to_aesni` (`AesNi.lean`) does: six blocks at a time
(`xmm0`–`xmm5`), each round key loaded once into `xmm6` and applied to all
six, then the remaining blocks one at a time, with a branch on the public
`rounds` around rounds 10–13; here each group of blocks is loaded from the
data and stored back in place. `eax` holds the schedule, `ecx` the number
of rounds, `edx` the scratch buffer, `esi` the data and `edi` the number
of blocks left; `esi` and `edi`, which are callee-saved, are saved in the
scratch buffer's first eight bytes.

Encryption needs no scratch buffer, and keeps to the registers it may
change, so that it writes neither the scratch buffer nor the stack: `edx`
holds the data, and after each group of blocks `ecx` is set to the number
of blocks done, from `edx` and the data's address, and compared with `n`
(the stack arguments, which it reads again each time, into `eax`), then
`ecx` and `eax` are reloaded with `rounds` and the schedule (`encTest`).

Decryption runs FIPS 197's equivalent inverse cipher (§5.3.5), which is
what `aesdec` computes: the middle rounds take `InvMixColumns` of the round
keys (`aesimc`), which are computed once, into `scratch + 16 j` for round
key `j` (`1 ≤ j < Nr`), before the blocks, and the last round key, with
which decryption starts, is copied to `scratch + 224`.

Every branch and every address depends only on the pointers, `rounds` and
`n`.
-/

@[expose] public section

namespace VG.Impl.Aes.X86.AesNi

open VG.X86

/-- Load the data blocks `p + 16 (j + i)` into the block registers. -/
def loadData (p : Reg) : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => .movdquLoad b (at_ p (16 * j)) :: loadData p bs (j + 1)

/-- Store the block registers to the data blocks `p + 16 (j + i)`. -/
def storeData (p : Reg) : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => .movdquStore (at_ p (16 * j)) b :: storeData p bs (j + 1)

/-- Save `esi` and `edi` in the scratch buffer (argument 4), and load the
arguments; then `cmp edi, 6`. -/
def blocksPrologue : List Instr :=
  [.mov .edx (.mem (argOp 4)), .store (at_ .edx 0) .esi, .store (at_ .edx 4) .edi,
   .mov .eax (.mem (argOp 0)), .mov .ecx (.mem (argOp 1)), .mov .esi (.mem (argOp 2)),
   .mov .edi (.mem (argOp 3))]

def blocksCmp : List Instr := [.alu .cmp .edi (.imm 6)]

/-- Restore `esi` and `edi`. -/
def blocksRestore : List Instr := [.mov .esi (.mem (at_ .edx 0)), .mov .edi (.mem (at_ .edx 4))]

/-- Six blocks through `f`. -/
def blocks6 (f : List XReg → Prog isa) : Prog isa :=
  .seq (.block (loadData .esi regs6 0))
    (.seq (f regs6)
      (.block (storeData .esi regs6 0 ++ ([.alu .add .esi (.imm 96), .alu .sub .edi (.imm 6),
        .alu .cmp .edi (.imm 6)] : List Instr))))

/-- One block through `f`. -/
def blocks1 (f : List XReg → Prog isa) : Prog isa :=
  .seq (.block (loadData .esi [.xmm0] 0))
    (.seq (f [.xmm0])
      (.block (storeData .esi [.xmm0] 0 ++ ([.alu .add .esi (.imm 16), .alu .sub .edi (.imm 1)] : List Instr))))

/-- The blocks, six and then one at a time, after `cmp edi, 6`. -/
def blocksTail (f : List XReg → Prog isa) : Prog isa :=
  .seq (.ite .b (.block []) (.loop (blocks6 f) .ae))
    (.seq (.block [.alu .test .edi (.reg .edi)]) (.ite .e (.block []) (.loop (blocks1 f) .ne)))

/-- `mov eax, data; mov ecx, edx; sub ecx, eax; shr ecx, 4; add ecx, k; mov
eax, n; cmp ecx, eax; mov ecx, rounds; mov eax, schedule`: with `edx` at
block `c` of the data, CF is set if `c + k < n`, and `eax` and `ecx` hold
the schedule and `rounds` again. -/
def encTest (k : Nat) : List Instr :=
  [.mov .eax (.mem (argOp 2)), .mov .ecx (.reg .edx), .alu .sub .ecx (.reg .eax), .shift .shr .ecx 4,
   .alu .add .ecx (.imm (BitVec.ofNat 32 k)), .mov .eax (.mem (argOp 3)), .alu .cmp .ecx (.reg .eax),
   .mov .ecx (.mem (argOp 1)), .mov .eax (.mem (argOp 0))]

/-- `rs.length` blocks at `edx` through `aes`, then on to the next, and
`encTest k`. -/
def encBlocks (rs : List XReg) (k : Nat) : Prog isa :=
  .seq (.block (loadData .edx rs 0))
    (.seq (aes rs)
      (.block (storeData .edx rs 0 ++ (.alu .add .edx (.imm (BitVec.ofNat 32 (16 * rs.length))) :: encTest k))))

/-- The schedule in `eax`, the data in `edx`, and `encTest 5`. -/
def encPrologue : List Instr := [.mov .eax (.mem (argOp 0)), .mov .edx (.mem (argOp 2))] ++ encTest 5

/-- Six blocks at a time while six are left, then one at a time. -/
def encryptBlocks : Prog isa :=
  .seq (.block encPrologue)
    (.seq (.ite .ae (.block []) (.loop (encBlocks regs6 5) .b))
      (.seq (.block (encTest 0)) (.ite .ae (.block []) (.loop (encBlocks [.xmm0] 0) .b))))

/-- `InvMixColumns` of round key `j` into `scratch + 16 j`. -/
def imcKey (j : Nat) : List Instr :=
  [.movdquLoad .xmm6 (at_ .eax (16 * j)), .xop (.bin .aesimc .xmm6 .xmm6),
   .movdquStore (at_ .edx (16 * j)) .xmm6]

/-- The last round key, `nr`, to `scratch + 224`. -/
def copyLast (nr : Nat) : List Instr :=
  [.movdquLoad .xmm6 (at_ .eax (16 * nr)), .movdquStore (at_ .edx 224) .xmm6]

/-- Round keys 1 … `Nr − 1` through `aesimc`, and the last round key, for
`rounds` (10, 12 or 14) in `ecx`. -/
def imcKeys : Prog isa :=
  .seq (.block ((List.range 9).flatMap (fun j => imcKey (j + 1)) ++ ([.alu .cmp .ecx (.imm 10)] : List Instr)))
    (.ite .e (.block (copyLast 10))
      (.seq (.block (imcKey 10 ++ imcKey 11 ++ ([.alu .cmp .ecx (.imm 12)] : List Instr)))
        (.ite .e (.block (copyLast 12)) (.block (imcKey 12 ++ imcKey 13 ++ copyLast 14)))))

/-- `op` with the round key at `m` into each block register, through `xmm6`. -/
def keyOpAt (regs : List XReg) (op : XBinOp) (m : MemOp) : List Instr :=
  .movdquLoad .xmm6 m :: regs.map fun b => .xop (.bin op b .xmm6)

/-- The middle round with round key `j` (`1 ≤ j < Nr`) of each block, from
`scratch + 16 j`. -/
def dround (regs : List XReg) (j : Nat) : List Instr := keyOpAt regs .aesdec (at_ .edx (16 * j))

/-- The inverse cipher on each block register, with `rounds` in `ecx`, the
key schedule at `eax`, and round keys 1 … `Nr − 1` through `aesimc` and the
last round key in the scratch buffer at `edx`. -/
def aesDec (regs : List XReg) : Prog isa :=
  .seq (.block (keyOpAt regs .pxor (at_ .edx 224) ++ ([.alu .cmp .ecx (.imm 10)] : List Instr)))
    (.seq
      (.ite .e (.block [])
        (.seq (.block [.alu .cmp .ecx (.imm 12)])
          (.seq (.ite .e (.block []) (.block (dround regs 13 ++ dround regs 12)))
            (.block (dround regs 11 ++ dround regs 10)))))
      (.block ((List.range 9).flatMap (fun j => dround regs (9 - j)) ++
        keyOpAt regs .aesdeclast (at_ .eax 0))))

def decryptBlocks : Prog isa :=
  .seq (.block blocksPrologue)
    (.seq imcKeys (.seq (.block blocksCmp) (.seq (blocksTail aesDec) (.block blocksRestore))))

end VG.Impl.Aes.X86.AesNi
