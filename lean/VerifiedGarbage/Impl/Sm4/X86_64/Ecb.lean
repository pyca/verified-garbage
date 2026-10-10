import VerifiedGarbage.Impl.Sm4.X86_64.Layers

/-!
# SM4 ECB, bitsliced, on x86-64

`ecb dir(schedule = rdi, data = rsi, n = rdx, scratch = rcx)`:
`vg_sm4_ecb_encrypt` and `vg_sm4_ecb_decrypt` with their working space in
the scratch buffer (`Layers.lean` has its layout), which the artifact
allocates on the stack.

* The scratch buffer moves to `r9`, `n` to `r8` and the data pointer to
  `rdx`; the callee-saved registers are saved, the masks set.
* The round keys are bitsliced into the table at slot 128, in the order the
  rounds use them: `rk₀ … rk₃₁` for encryption, `rk₃₁ … rk₀` for decryption
  (§7.2). Decryption then runs the same rounds as encryption.
* Each group of up to sixteen blocks is copied to the tail buffer,
  bitsliced, run through the 32 rounds (eight times four, the state's words
  taking the new words in turn), and copied back.

Only `rdi` and `rsi` (pointers into the schedule and the table, and the
round key's entry), `rdx` (the data), `r8` (the blocks left), `r15` during
the key setup, and the copies' pointers and counts hold public values; no
address and no branch depends on anything else.
-/

namespace VG.Impl.Sm4.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64
open VG.Impl.Sm4 (Lin)

inductive Dir | encrypt | decrypt
  deriving DecidableEq, Repr

/-! ## The round keys -/

/-- `r := ` the address of slot `k`. -/
def slotAddr (r : Reg) (k : Nat) : List Instr := [movR r sb, .alu .add r (.imm (BitVec.ofNat 32 (8 * k)))]

/-- Encryption's table: round keys `2 m` and `2 m + 1`, from the word at
`rdi`, to entries `2 m` and `2 m + 1`. -/
def encKeys : Prog isa :=
  .seq (.block (slotAddr .rsi tableSlot ++ [.movImm64 t1 16]))
    (.loop (.block (keyOne 0 ++ [.alu .add .rsi (.imm 64)] ++ keyOne 1 ++
      [.alu .add .rsi (.imm 64), .alu .add .rdi (.imm 8), .alu .sub t1 (.imm 1)])) .ne)

/-- Decryption's table: round keys `2 m` and `2 m + 1` to entries `31 - 2 m`
and `30 - 2 m`. -/
def decKeys : Prog isa :=
  .seq (.block (slotAddr .rsi (tableSlot + 8 * 31) ++ [.movImm64 t1 16]))
    (.loop (.block (keyOne 0 ++ [.alu .sub .rsi (.imm 64)] ++ keyOne 1 ++
      [.alu .sub .rsi (.imm 64), .alu .add .rdi (.imm 8), .alu .sub t1 (.imm 1)])) .ne)

/-- The table, then `rdi := ` its end. -/
def keys (dir : Dir) : Prog isa :=
  .seq (match dir with | .encrypt => encKeys | .decrypt => decKeys) (.block (slotAddr .rdi tableEnd))

/-! ## Sixteen blocks -/

/-- Four rounds, `add kp, 256`, `cmp kp, rdi`. -/
def roundsBody (l : Lin) : List Instr := rounds4 l ++ [.alu .add kp (.imm 256), .alu .cmp kp (.reg .rdi)]

/-- The 32 rounds, with `kp` from the table's start to its end (in `rdi`). -/
def rounds (l : Lin) : Prog isa :=
  .seq (.block (slotAddr kp tableSlot)) (.loop (.block (roundsBody l)) .ne)

/-- The sixteen blocks of the tail buffer, in place. -/
def crypt16 : Prog isa := .seq (.block toBs) (.seq (rounds .enc) (.block fromBs))

/-! ## The groups

Each group of up to sixteen blocks is copied to the tail buffer, transformed
there and copied back. -/

/-- Copy `rcx` blocks from `rax` to `rbx` (through `rbp`). -/
def copyBlocks : Prog isa :=
  .loop (.block [.mov .rbp (.mem (at_ .rax 0)), .store (at_ .rbx 0) .rbp,
      .mov .rbp (.mem (at_ .rax 8)), .store (at_ .rbx 8) .rbp,
      .alu .add .rax (.imm 16), .alu .add .rbx (.imm 16), .alu .sub .rcx (.imm 1)]) .ne

/-- `rcx := min(r8, 16)`, the blocks of this group. -/
def groupCount : Prog isa :=
  .seq (.block [.movImm64 .rcx 16, .alu .cmp .r8 (.imm 16)]) (.ite .b (.block [movR .rcx .r8]) (.block []))

/-- The group's blocks to the tail buffer. -/
def copyIn : Prog isa := .seq groupCount (.seq (.block ([movR .rax .rdx] ++ slotAddr .rbx tailSlot)) copyBlocks)

/-- The tail buffer back to the group's blocks. -/
def copyOut : Prog isa := .seq groupCount (.seq (.block (slotAddr .rax tailSlot ++ [movR .rbx .rdx])) copyBlocks)

/-- On to the next group, or none left (ZF set). -/
def advance : Prog isa :=
  .seq (.block [.alu .cmp .r8 (.imm 16)])
    (.ite .b (.block [.alu .sub .r8 (.reg .r8)]) (.block [.alu .add .rdx (.imm 256), .alu .sub .r8 (.imm 16)]))

/-- Sixteen blocks, or the last one to fifteen (and none left: ZF set). -/
def group : Prog isa := .seq copyIn (.seq crypt16 (.seq copyOut advance))

/-- The whole function: the table, then the groups. -/
def ecb (dir : Dir) : Prog isa :=
  .seq (.block ([movR sb .rcx, movR .r8 .rdx, movR .rdx .rsi] ++ saveRegs ++ setMasks keyMasks))
    (.seq (keys dir)
      (.seq (.block [.alu .test .r8 (.reg .r8)])
        (.seq (.ite .e (.block []) (.loop group .ne)) (.block restoreRegs))))

end VG.Impl.Sm4.X86_64
