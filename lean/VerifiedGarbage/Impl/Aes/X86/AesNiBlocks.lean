module

public import VerifiedGarbage.Impl.Aes.X86.AesNi

/-!
# AES with AES-NI on x86 (32-bit): encryption and decryption of whole blocks

`vg_aes_encrypt_blocks_aesni(schedule, rounds, data, n, scratch)` and
`vg_aes_decrypt_blocks_aesni`, cdecl (the arguments are at `[esp + 4]` …
`[esp + 20]`), with the contracts of `vg_aes_encrypt_blocks` and
`vg_aes_decrypt_blocks` (`Spec/Aes/Contract.lean`), for CPUs with AES-NI.

Seven blocks at a time (`xmm0`–`xmm5` and `xmm7`), each round key loaded once
into `xmm6` and applied to all seven (`aes` of `AesNi.lean`, `aesDec`), with
a branch on the public `rounds` around rounds 10–13; each group of blocks is
loaded from the data and stored back in place. The blocks left after the
turns of seven, six at most, are a group of four, a group of two and one
block, each taken once if the count of those blocks has its bit (`regs4`,
`regs2`, `regs1`). The three groups are in registers apart from each
other: where the processor keeps the registers' upper halves, a load into
a register waits for the value the register had, so that blocks taken one
after the other in one register would each wait for the one before, and
these do not. `eax` holds the schedule, `ecx` the number of rounds, `edx`
the scratch buffer, `esi` the data and `edi` the number of blocks left
(after the turns of seven, the number left then); `esi` and `edi`, which
are callee-saved, are saved in the scratch buffer's first eight bytes.

Encryption needs no scratch buffer, and keeps to the registers it may
change, so that it writes neither the scratch buffer nor the stack: `edx`
holds the data, and after each group of blocks `ecx` is set to the number
of blocks done, from `edx` and the data's address, and compared with `n`
(the stack arguments, which it reads again each time, into `eax`), then
`ecx` and `eax` are reloaded with `rounds` and the schedule (`encTest`):
before a group of four, two or one, whether that many blocks are left.

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
arguments. -/
def blocksPrologue : List Instr :=
  [.mov .edx (.mem (argOp 4)), .store (at_ .edx 0) .esi, .store (at_ .edx 4) .edi,
   .mov .eax (.mem (argOp 0)), .mov .ecx (.mem (argOp 1)), .mov .esi (.mem (argOp 2)),
   .mov .edi (.mem (argOp 3))]

def blocksCmp : List Instr := [.alu .cmp .edi (.imm 7)]

/-- Restore `esi` and `edi`. -/
def blocksRestore : List Instr := [.mov .esi (.mem (at_ .edx 0)), .mov .edi (.mem (at_ .edx 4))]

/-- The block registers of a turn of seven. -/
def regs7 : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm7]

/-- The block registers of the four, the two and the one block left after
the turns of seven: apart from each other. -/
def regs4 : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3]
def regs2 : List XReg := [.xmm4, .xmm5]
def regs1 : List XReg := [.xmm7]

/-- `rs.length` blocks at `esi` through `f`, and on to the next; then
`rest`. -/
def blocksGroup (f : List XReg → Prog isa) (rs : List XReg) (rest : List Instr) : Prog isa :=
  .seq (.block (loadData .esi rs 0))
    (.seq (f rs)
      (.block (storeData .esi rs 0 ++ (.alu .add .esi (.imm (BitVec.ofNat 32 (16 * rs.length))) :: rest))))

/-- Seven blocks through `f`. -/
def blocks7 (f : List XReg → Prog isa) : Prog isa :=
  blocksGroup f regs7 [.alu .sub .edi (.imm 7), .alu .cmp .edi (.imm 7)]

/-- The `rs.length` blocks at `esi` through `f`, if the number of blocks in
`edi` has the bit `rs.length` (a power of two). -/
def blocksOnce (f : List XReg → Prog isa) (rs : List XReg) : Prog isa :=
  .seq (.block [.alu .test .edi (.imm (BitVec.ofNat 32 rs.length))]) (.ite .e (.block []) (blocksGroup f rs []))

/-- The blocks, seven at a time, and then four, two and one, after
`cmp edi, 7`. -/
def blocksTail (f : List XReg → Prog isa) : Prog isa :=
  .seq (.ite .b (.block []) (.loop (blocks7 f) .ae))
    (.seq (blocksOnce f regs4) (.seq (blocksOnce f regs2) (blocksOnce f regs1)))

/-- `mov eax, data; mov ecx, edx; sub ecx, eax; shr ecx, 4; add ecx, k; mov
eax, n; cmp ecx, eax; mov ecx, rounds; mov eax, schedule`: with `edx` at
block `c` of the data, CF is set if `c + k < n`, and `eax` and `ecx` hold
the schedule and `rounds` again. -/
def encTest (k : Nat) : List Instr :=
  [.mov .eax (.mem (argOp 2)), .mov .ecx (.reg .edx), .alu .sub .ecx (.reg .eax), .shift .shr .ecx 4,
   .alu .add .ecx (.imm (BitVec.ofNat 32 k)), .mov .eax (.mem (argOp 3)), .alu .cmp .ecx (.reg .eax),
   .mov .ecx (.mem (argOp 1)), .mov .eax (.mem (argOp 0))]

/-- `rs.length` blocks at `edx` through `aes`, and on to the next. -/
def encGroup (rs : List XReg) : Prog isa :=
  .seq (.block (loadData .edx rs 0))
    (.seq (aes rs)
      (.block (storeData .edx rs 0 ++ [.alu .add .edx (.imm (BitVec.ofNat 32 (16 * rs.length)))])))

/-- Seven blocks, and `encTest 6`. -/
def encBlocks : Prog isa := .seq (encGroup regs7) (.block (encTest 6))

/-- The `rs.length` blocks at `edx`, if that many are left. -/
def encOnce (rs : List XReg) : Prog isa :=
  .seq (.block (encTest (rs.length - 1))) (.ite .ae (.block []) (encGroup rs))

/-- The schedule in `eax`, the data in `edx`, and `encTest 6`. -/
def encPrologue : List Instr := [.mov .eax (.mem (argOp 0)), .mov .edx (.mem (argOp 2))] ++ encTest 6

/-- Seven blocks at a time while seven are left, then four, two and one. -/
def encryptBlocks : Prog isa :=
  .seq (.block encPrologue)
    (.seq (.ite .ae (.block []) (.loop encBlocks .b))
      (.seq (encOnce regs4) (.seq (encOnce regs2) (encOnce regs1))))

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
