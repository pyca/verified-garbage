import VerifiedGarbage.Impl.Sm4.X86_64.Ecb

/-!
# SM4-CTR, bitsliced, on x86-64

`ctr(schedule = rdi, ctr = rsi, data = rdx, n = rcx, scratch = r8)`:
`vg_sm4_ctr` with its working space in the scratch buffer (`Layers.lean` has
its layout), which the artifact allocates on the stack. It reuses ECB's
pieces (`Ecb.lean`): the table of bitsliced round keys, built once, and the
sixteen-block transformation of the tail buffer.

* The scratch buffer moves to `r9` and `n` to `r8`; the callee-saved
  registers are saved, the masks set.
* The counter block `T₁` is read as two big-endian 64-bit integers (`bswap`)
  into the running counter's slots (`ctrHi`, `ctrLo`), and the counter block
  to continue from, `T₁ + n mod 2¹²⁸`, is written to `ctr` at once.
* Each group of up to sixteen blocks: the next sixteen counter blocks are
  written to the tail buffer (`add`, `adc` on the running counter, and
  `bswap` back to big-endian), transformed in place into the keystream, and
  XORed into the group's blocks.

Only the pointers and `n` (and the copies' pointers and counts, `kp`, and the
loop tests) are public; the counter is secret like the key and the data,
and no address or branch depends on it.
-/

namespace VG.Impl.Sm4.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64

/-! ## The counter -/

/-- The counter block at `rsi` to the running counter's slots, and `T₁ + n`
(`n` in `r8`) back to `rsi`. -/
def ctrSetup : List Instr :=
  [.mov .rax (.mem (at_ .rsi 0)), .bswap .rax, .mov .rbx (.mem (at_ .rsi 8)), .bswap .rbx,
   st ctrHi .rax, st ctrLo .rbx,
   .alu .add .rbx (.reg .r8), .alu .adc .rax (.imm 0), .bswap .rax, .bswap .rbx,
   .store (at_ .rsi 0) .rax, .store (at_ .rsi 8) .rbx]

/-- Counter block `b` of the group (the running counter in `rax`, `rbx`) to
block `b` of the tail buffer, and the running counter incremented. -/
def ctrBlock (b : Nat) : List Instr :=
  [movR .rcx .rax, .bswap .rcx, st (tailAt b 0) .rcx, movR .rcx .rbx, .bswap .rcx, st (tailAt b 1) .rcx,
   .alu .add .rbx (.imm 1), .alu .adc .rax (.imm 0)]

/-- The group's sixteen counter blocks to the tail buffer, and the running
counter stepped by sixteen. -/
def ctrBlocks : List Instr :=
  [movS .rax ctrHi, movS .rbx ctrLo] ++ (List.range 16).flatMap ctrBlock ++ [st ctrHi .rax, st ctrLo .rbx]

/-! ## The groups -/

/-- XOR `rcx` blocks at `rax` into the blocks at `rbx` (through `rbp`). -/
def xorBlocks : Prog isa :=
  .loop (.block [.mov .rbp (.mem (at_ .rax 0)), .alu .xor .rbp (.mem (at_ .rbx 0)), .store (at_ .rbx 0) .rbp,
      .mov .rbp (.mem (at_ .rax 8)), .alu .xor .rbp (.mem (at_ .rbx 8)), .store (at_ .rbx 8) .rbp,
      .alu .add .rax (.imm 16), .alu .add .rbx (.imm 16), .alu .sub .rcx (.imm 1)]) .ne

/-- The keystream in the tail buffer XORed into the group's blocks. -/
def xorOut : Prog isa := .seq groupCount (.seq (.block (slotAddr .rax tailSlot ++ [movR .rbx .rdx])) xorBlocks)

/-- Sixteen blocks, or the last one to fifteen (and none left: ZF set). -/
def ctrGroup : Prog isa := .seq (.block ctrBlocks) (.seq crypt16 (.seq xorOut advance))

/-- The whole function: the counter, the table, then the groups. -/
def ctr : Prog isa :=
  .seq (.block ([movR sb .r8, movR .r8 .rcx] ++ saveRegs ++ setMasks keyMasks ++ ctrSetup))
    (.seq (keys .encrypt)
      (.seq (.block [.alu .test .r8 (.reg .r8)])
        (.seq (.ite .e (.block []) (.loop ctrGroup .ne)) (.block restoreRegs))))

end VG.Impl.Sm4.X86_64
