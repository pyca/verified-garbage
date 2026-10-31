module

public import VerifiedGarbage.TCB.Code

/-!
# 64-bit RISC-V machine model

**Trusted.** A model of the subset of RV64IM used by our implementations.
Each instruction's semantics here must agree with The RISC-V Instruction Set
Manual, Volume I: Unprivileged Architecture (Version 20250508), chapters "RV32I
Base Integer Instruction Set", "RV64I Base Integer Instruction Set" and "M
Extension for Integer Multiplication and Division" (whose sections the
docstrings cite by title); when adding an instruction, cite the
section that defines it. The calling convention and linkage are the RISC-V
ELF psABI's (RISC-V ABIs Specification, Version 1.0: "RISC-V Calling
Conventions" and "RISC-V ELF Specification"; see `Target.lean`).

Modelling choices:
* Registers are `x1` and `x5`–`x31`, by their ABI names (`ra`, `t0`–`t6`,
  `s0`–`s11`, `a0`–`a7`; psABI, "Integer Register Convention"). `x0`
  (`zero`) is not a register of the model: its uses are separate forms
  (`li`, the conditions on zero). The stack pointer `x2` (`sp`) is
  separate: only the push and pop of a frame (see `push`) write it, and only
  they and `addSp` (`addi rd, sp, imm`, a pointer into the stack) read it.
  `x3` (`gp`) and `x4` (`tp`) are "unallocatable" ("procedures should not
  modify the integer registers tp and gp, because signal handlers may rely
  upon their values"): they are never operands, so never changed.
* The return address is in `ra`, an ordinary register: a call writes it
  (`call`) and the return jumps to it (`ret`), which faults unless it is the
  address the call left.
* The registers are 64 bits. The 32-bit operations are the `*w` forms
  (`addw`, `subw`, `addiw`, `slliw`, `srliw`, `sraiw`, `sllw`, `srlw`,
  `sraw`), which read the low 32 bits of their operands (`sllw`, `srlw` and
  `sraw` only the low 5 bits of their shift amount) and sign-extend their
  32-bit result (RV64I, "Integer Computational Instructions": "These *w
  instructions ignore the upper 32 bits of their inputs and always produce
  32-bit signed values, sign-extending them to 64 bits"), the loads of words
  (`lwu`, zero-extended) and the stores of words (the low 32 bits); every
  other operation acts on all 64 bits.
* Immediates the instruction cannot encode make it fault, so verified code
  only ever contains encodable instructions: the I-type immediates are
  12-bit signed (`-2048 ≤ imm < 2048`), shift amounts are below the operand
  size, and the U-type immediate of `lui` is 20 bits. The displacements of
  loads and stores are non-negative here (`0 ≤ off < 2048`).
* Memory accesses (bytes, halfwords, words and doublewords) must lie within
  the state's permitted regions: loads within `rd ++ wr`, stores within
  `wr`; otherwise the instruction faults. The memory system is
  little-endian ("In a little-endian configuration, multibyte stores write
  the least-significant register byte at the lowest memory byte address
  ... Loads similarly transfer the contents of the lesser memory byte
  addresses to the less-significant register bytes"), so a load is a
  little-endian read (`Mem.read`): the target is little-endian (`rustCfg`).
* An access whose address is not naturally aligned (a multiple of its size)
  faults: misaligned loads and stores "have behavior dependent on the EEI",
  which "may not guarantee misaligned loads and stores are handled
  invisibly", and even where they complete they "might run extremely slowly
  depending on the implementation (e.g., when implemented via an invisible
  trap)" (RV32I, "Load and Store Instructions"). Naturally aligned accesses
  "shall not raise an address-misaligned exception", whatever the EEI.
* A branch condition (`Cond`) is a conditional branch's comparison of two
  registers, or of one with `x0`: `beqz`/`bnez` (`beq`/`bne rs1, x0`), and
  `beq`, `bne`, `bltu` and `bgeu` of two registers. The assembler may relax
  a branch whose label is out of the 12-bit range of a conditional branch
  into the opposite branch over a `j` to it, which takes the same path.
  A compressed (C) encoding, which the assembler may choose for an
  instruction, "expands into a single 32-bit instruction in the base ISA"
  (Zca), the one it was chosen for.
* Instructions whose timing depends on their operands (e.g. `div`, `rem`)
  must never be added: the constant-time leakage model assumes they do not
  exist. The base ISA makes no promise about timing; the Zkt extension
  ("Extension for Data-Independent Execution Latency", "Zkt listings")
  attests data-independent latency for a list of instructions, which
  includes every computational instruction modelled here (`lui`, `auipc`,
  `addi`, `andi`, `ori`, `xori`, `slli`, `srli`, `srai`, `add`, `sub`,
  `sll`, `srl`, `sra`, `sltu`, `and`, `or`, `xor`, `addiw`, `slliw`,
  `srliw`, `sraiw`, `addw`, `subw`, `sllw`, `srlw`, `sraw`, and, of the M
  extension, `mul` and `mulhu`: "Multiplication is included; division and
  remaindering excluded"). The shifts by a register are in Zkt's RVI listing
  (`sll`, `srl` and `sra`, and of RV64 `sllw`, `srlw` and `sraw`; Scalar
  Cryptography, "Data Independent Execution Latency Subset: Zkt": "The Zkt
  extension attests that the machine has data-independent execution time for
  a safe subset of instructions"), so their latency is independent of the
  shift amount as well as of the value shifted.
  As for the other ISAs, the leakage model assumes these take the same time
  whatever their operands; loads, stores and branches leak their addresses
  and conditions, which the taint analysis keeps public.
* The multiplies are the M extension's `mul` and `mulhu`, the low and the
  high 64 bits of the unsigned 128-bit product: `rustCfg` requires the
  extension (`target_feature = "m"`, which every RV64 target Rust has,
  RV64GC's among them, enables), so they are not CPU features to detect.
  `mulh`, `mulhsu`, `mulw` and the divisions are not modelled.
* Calls are `call` (the pseudoinstruction `auipc ra, …; jalr ra, …(ra)`,
  which the linker may relax to `jal ra, …`; psABI, "Procedure Calls")
  and returns `ret` (`jalr x0, 0(ra)`; RV32I, "Unconditional Jumps"). The
  return addresses are the next of the state's `unknowns`, which nothing
  constrains (see `TCB/Code.lean`). The call may go through a PLT entry
  (psABI, "Procedure Linkage Table"), whose code uses `t1` and `t3` (and
  whose header, run by lazy binding, `t0`–`t3`, before it runs the dynamic
  linker's resolver, which the psABI does not constrain beyond the calling
  convention, in which `t0`–`t6` are not preserved), so a call leaves
  unknown values in `t0`–`t6` too. The PLT accesses only the GOT, which no
  region of the model covers.
* The stack pointer is always 16-byte aligned (psABI: "the stack pointer
  shall be aligned to a 128-bit boundary upon procedure entry", and "must
  remain aligned throughout procedure execution"; `Abi.wf` assumes it on
  entry, see `Target.lean`), and a frame moves it by a multiple of 16, so
  the model does not check the alignment of its frames' accesses.
* A frame is `push` (`addi sp, sp, -16` then `sd rs, 8(sp)`) and `pop`
  (`ld rd, 8(sp)` then `addi sp, sp, 16`): 16 bytes, which become a writable
  region. A frame may instead allocate a buffer on the stack (`alloc`,
  `addi sp, sp, -bytes`), released by its pop (`free`, `addi sp, sp,
  bytes`), whose `bytes` bytes become a writable region. `bytes` is a
  multiple of 16 of at most 4064: less than a page, so that the allocation
  does not move `sp` past a guard page below the stack. Below 2048, `addi`
  encodes it; from 2048 on, it is two `addi`s of at most 2032 bytes each
  (see `push`).
* A `static` the code reads (`Artifact.consts`) is at the address
  `State.syms name`, where `name` is its name, which `lla` puts in a
  register: `auipc` of the high part of the static's distance from the
  `auipc` itself, then `addi` of the low part, which the linker resolves
  (see `exec`). No instruction changes `syms`: a static's address is fixed
  for the run of the program.
-/

@[expose] public section

namespace VG.RISCV64

inductive Reg
  | ra | t0 | t1 | t2 | s0 | s1 | a0 | a1 | a2 | a3 | a4 | a5 | a6 | a7
  | s2 | s3 | s4 | s5 | s6 | s7 | s8 | s9 | s10 | s11 | t3 | t4 | t5 | t6
  deriving DecidableEq, Repr, Inhabited

/-- Operand size of the shifts: a word (32 bits, the `*w` forms) or a
doubleword (64 bits). -/
inductive Size | w | d
  deriving DecidableEq, Repr

abbrev Size.bits : Size → Nat
  | .w => 32
  | .d => 64

/-- Width of a load or store: a byte, halfword, word or doubleword. -/
inductive Width | b | h | w | d
  deriving DecidableEq, Repr

abbrev Width.bytes : Width → Nat
  | .b => 1
  | .h => 2
  | .w => 4
  | .d => 8

structure State where
  gpr : Reg → BitVec 64
  /-- The stack pointer, `sp` (`x2`). -/
  sp : BitVec 64
  mem : Mem
  /-- Regions the code may read (in addition to `wr`). -/
  rd : List Region
  /-- Regions the code may read and write. -/
  wr : List Region
  /-- Values the model does not know, used in order: the return address each
  call leaves in `ra`, and what a call may leave in `t0`–`t6` (see
  `TCB/Code.lean`). -/
  unknowns : Nat → BitVec 64 := fun _ => 0
  /-- The address of each `static` the code can name (`lla`), by name. -/
  syms : String → BitVec 64 := fun _ => 0

inductive LogicOp | and | or | xor
  deriving DecidableEq, Repr

/-- The shifts, by an immediate (`shift`) or by a register (`shiftReg`):
logical left, logical right, arithmetic right. -/
inductive ShiftOp | sll | srl | sra
  deriving DecidableEq, Repr

inductive Instr
  /-- `add rd, rs1, rs2` -/
  | add (d n m : Reg)
  /-- `sub rd, rs1, rs2`: `d := n - m` -/
  | sub (d n m : Reg)
  /-- `addw rd, rs1, rs2`: the low 32 bits of the sum, sign-extended -/
  | addw (d n m : Reg)
  /-- `subw rd, rs1, rs2`: the low 32 bits of `n - m`, sign-extended -/
  | subw (d n m : Reg)
  /-- `sltu rd, rs1, rs2`: 1 if `n < m` as unsigned numbers, else 0 -/
  | sltu (d n m : Reg)
  /-- `mul rd, rs1, rs2`: the low 64 bits of the product -/
  | mul (d n m : Reg)
  /-- `mulhu rd, rs1, rs2`: the high 64 bits of the unsigned product -/
  | mulhu (d n m : Reg)
  /-- `and`/`or`/`xor rd, rs1, rs2` -/
  | logic (op : LogicOp) (d n m : Reg)
  /-- `addi rd, rs1, imm`, `-2048 ≤ imm < 2048` (`mv rd, rs1` is `imm = 0`) -/
  | addi (d n : Reg) (imm : Int)
  /-- `addiw rd, rs1, imm`, `-2048 ≤ imm < 2048`: the low 32 bits of the sum,
  sign-extended -/
  | addiw (d n : Reg) (imm : Int)
  /-- `andi`/`ori`/`xori rd, rs1, imm`, `-2048 ≤ imm < 2048`, with the
  immediate sign-extended -/
  | logicImm (op : LogicOp) (d n : Reg) (imm : Int)
  /-- `addi rd, x0, imm` (`li rd, imm` with a 12-bit immediate),
  `-2048 ≤ imm < 2048` -/
  | li (d : Reg) (imm : Int)
  /-- `lui rd, imm`: `imm` shifted left by 12, sign-extended from 32 bits -/
  | lui (d : Reg) (imm : BitVec 20)
  /-- `slli`/`srli`/`srai rd, rs1, sh` (a doubleword, `sh < 64`) or
  `slliw`/`srliw`/`sraiw rd, rs1, sh` (the low word, `sh < 32`, the result
  sign-extended) -/
  | shift (op : ShiftOp) (sz : Size) (d n : Reg) (sh : Nat)
  /-- `sll`/`srl`/`sra rd, rs1, rs2` (a doubleword, shifted by the low 6 bits
  of `m`) or `sllw`/`srlw`/`sraw rd, rs1, rs2` (the low word, shifted by the
  low 5 bits of `m`, the result sign-extended) -/
  | shiftReg (op : ShiftOp) (sz : Size) (d n m : Reg)
  /-- `lbu`/`lhu`/`lwu`/`ld rd, off(rs1)`: the value, zero-extended;
  `0 ≤ off < 2048`, the address naturally aligned -/
  | load (wd : Width) (t n : Reg) (off : Nat)
  /-- `sb`/`sh`/`sw`/`sd rs2, off(rs1)`: the low bytes of `t`;
  `0 ≤ off < 2048`, the address naturally aligned -/
  | store (wd : Width) (t n : Reg) (off : Nat)
  /-- `addi sp, sp, -16` then `sd rs, 8(sp)`: the push of a frame of 16
  bytes (see `push`) -/
  | push (r : Reg)
  /-- `ld rd, 8(sp)` then `addi sp, sp, 16`: the pop of a frame of 16 bytes
  (see `pop`) -/
  | pop (r : Reg)
  /-- `addi sp, sp, -bytes` (from 2048 on, `addi sp, sp, -2032` then
  `addi sp, sp, -(bytes - 2032)`): the push of a frame of `bytes` bytes,
  which it does not write (see `push`); `0 < bytes ≤ 4064`, a multiple of 16 -/
  | alloc (bytes : Nat)
  /-- `addi sp, sp, bytes` (from 2048 on, `addi sp, sp, bytes - 2032` then
  `addi sp, sp, 2032`): the pop of a frame of `bytes` bytes (see `pop`) -/
  | free (bytes : Nat)
  /-- `addi rd, sp, imm` with `0 ≤ imm < 2048`: a pointer `imm` bytes above
  the stack pointer -/
  | addSp (d : Reg) (imm : Nat)
  /-- `lla rd, symbol` (`auipc rd, %pcrel_hi(symbol)` then `addi rd, rd,
  %pcrel_lo(…)`), where `symbol` is the `static` named `name`: `rd ←` its
  address (see `exec`) -/
  | lla (d : Reg) (name : String)
  deriving DecidableEq, Repr

/-- Branch conditions: the comparison of a conditional branch. -/
inductive Cond
  /-- `beqz rs` (`beq rs, x0, …`): the register is zero -/
  | zero (r : Reg)
  /-- `bnez rs` (`bne rs, x0, …`): the register is not zero -/
  | nonzero (r : Reg)
  /-- `beq rs1, rs2, …`: the registers are equal -/
  | eq (a b : Reg)
  /-- `bne rs1, rs2, …`: the registers differ -/
  | ne (a b : Reg)
  /-- `bltu rs1, rs2, …`: `a < b` as unsigned numbers -/
  | ltu (a b : Reg)
  /-- `bgeu rs1, rs2, …`: `a ≥ b` as unsigned numbers -/
  | geu (a b : Reg)
  deriving DecidableEq, Repr

namespace State

/-- Write all 64 bits of a register. -/
def write (s : State) (r : Reg) (v : BitVec 64) : State :=
  { s with gpr := fun r' => if r' = r then v else s.gpr r' }

/-- Load `n` bytes, faulting if not permitted. -/
def load (s : State) (a : Addr) (n : Nat) : Option (BitVec (8 * n)) :=
  if InRegions (s.rd ++ s.wr) a n then some (s.mem.read a n) else none

/-- Store `n` bytes, faulting if not permitted. -/
def store (s : State) (a : Addr) (n : Nat) (v : BitVec (8 * n)) : Option State :=
  if InRegions s.wr a n then some { s with mem := s.mem.write a n v } else none

end State

/-- Whether an I-type immediate is encodable: 12 bits, signed. -/
abbrev imm12 (imm : Int) : Prop := -2048 ≤ imm ∧ imm < 2048

/-- The 32-bit value `v`, sign-extended into a register (the result of the
`*w` forms). -/
abbrev sext32 (v : BitVec 32) : BitVec 64 := v.signExtend 64

/-- The effective address `rs1 + off` of an access of `bytes` bytes at
`off(rs1)`, if the displacement is encodable and the address naturally
aligned (RV32I, "Load and Store Instructions": "The effective address is
obtained by adding register rs1 to the sign-extended 12-bit offset"; see the
modelling choices for the alignment). The displacement is non-negative
here. -/
def addr (s : State) (bytes : Nat) (n : Reg) (off : Nat) : Option Addr :=
  let a := s.gpr n + BitVec.ofNat 64 off
  if off < 2048 ∧ a.toNat % bytes = 0 then some a else none

/-- Semantics, transcribing the Unprivileged Architecture's RV32I and RV64I
chapters (which name instructions in lower case):
* RV32I, "Integer Register-Register Operations": "add performs the addition
  of rs1 and rs2. sub performs the subtraction of rs2 from rs1. Overflows are
  ignored and the low XLEN bits of results are written to the destination
  rd. slt and sltu perform signed and unsigned compares respectively, writing
  1 to rd if rs1 < rs2, 0 otherwise"; "and, or, and xor perform bitwise
  logical operations";
* RV64I, "Integer Register-Register Operations": "addw and subw are RV64I-only
  instructions that are defined analogously to add and sub but operate on
  32-bit values and produce signed 32-bit results. Overflows are ignored, and
  the low 32-bits of the result is sign-extended to 64-bits and written to
  the destination register"; "sll, srl, and sra perform logical left,
  logical right, and arithmetic right shifts on the value in register rs1 by
  the shift amount held in register rs2. In RV64I, only the low 6 bits of rs2
  are considered for the shift amount" (the shift amount is `rs2 mod 64`);
  "sllw, srlw, and sraw are RV64I-only instructions that are analogously
  defined but operate on 32-bit values and sign-extend their 32-bit results
  to 64 bits. The shift amount is given by rs2[4:0]" (`rs2 mod 32`);
* RV32I, "Integer Register-Immediate Instructions": "addi adds the
  sign-extended 12-bit immediate to register rs1. Arithmetic overflow is
  ignored and the result is simply the low XLEN bits of the result" (`li rd,
  imm` is `addi rd, x0, imm`, and `addSp` is `addi rd, sp, imm`, whose `rs1`
  is `x2`); "andi, ori, xori are logical operations that perform bitwise AND,
  OR, and XOR on register rs1 and the sign-extended 12-bit immediate and
  place the result in rd";
* RV64I, "Integer Register-Immediate Instructions": "addiw is an RV64I
  instruction that adds the sign-extended 12-bit immediate to register rs1
  and produces the proper sign extension of a 32-bit result in rd. Overflows
  are ignored and the result is the low 32 bits of the result sign-extended
  to 64 bits"; for slli, srli and srai, "the shift amount is encoded in the
  lower 6 bits of the I-immediate field for RV64I", and "slli is a logical
  left shift (zeros are shifted into the lower bits); srli is a logical right
  shift (zeros are shifted into the upper bits); and srai is an arithmetic
  right shift (the original sign bit is copied into the vacated upper
  bits)"; "slliw, srliw, and sraiw are RV64I-only instructions that are
  analogously defined but operate on 32-bit values and sign-extend their
  32-bit results to 64 bits. slliw, srliw, and sraiw encodings with imm[5] ≠
  0 are reserved" (the model faults); "lui places the 32-bit U-immediate into
  register rd, filling in the lowest 12 bits with zeros. The 32-bit result is
  sign-extended to 64 bits" (the assembler's operand is the immediate's upper
  20 bits);
* RV64I, "Load and Store Instructions": "The ld instruction loads a 64-bit
  value from memory into register rd for RV64I. The lw instruction loads a
  32-bit value from memory and sign-extends this to 64 bits before storing it
  in register rd for RV64I. The lwu instruction, on the other hand,
  zero-extends the 32-bit value from memory for RV64I. lh and lhu are defined
  analogously for 16-bit values, as are lb and lbu for 8-bit values. The sd,
  sw, sh, and sb instructions store 64-bit, 32-bit, 16-bit, and 8-bit values
  from the low bits of register rs2 to memory respectively";
* M, "Multiplication Operations": "mul performs an XLEN-bit×XLEN-bit
  multiplication of rs1 by rs2 and places the lower XLEN bits in the
  destination register. mulh, mulhu, and mulhsu perform the same
  multiplication but return the upper XLEN bits of the full 2×XLEN-bit
  product, for signed×signed, unsigned×unsigned, and rs1×unsigned rs2
  multiplication" (the low bits are the same for signed and unsigned
  operands);
* `lla d name` is the assembler's "load local address" pseudoinstruction
  (RISC-V Assembly Programmer's Manual, "Load Local Address" and the table of
  pseudoinstructions: `lla rd, symbol` is `auipc rd, symbol[31:12]` then
  `addi rd, rd, symbol[11:0]`, with the relocations `R_RISCV_PCREL_HI20` and
  `R_RISCV_PCREL_LO12_I`), which the linker completes with the static's
  address `S` (`State.syms name`): RV64I, "Integer Register-Immediate
  Instructions": "auipc forms a 32-bit offset from the U-immediate, filling
  in the lowest 12 bits with zeros, sign-extends the result to 64 bits, adds
  it to the address of the auipc instruction, then places the result in
  register rd", then `addi` as above. The psABI ("Relocations", "PC-Relative
  Symbol Addresses") gives the immediates: "HI20: `(symbol_address -
  hi20_reloc_offset + 0x800) >> 12`", "LO12: `symbol_address -
  hi20_reloc_offset`" (its low 12 bits, sign-extended by `addi`; "the
  preceding high 20-bit relocation may have 1 added to it"), where
  `hi20_reloc_offset` is the address `P` of the `auipc`, so that `rd ← P +
  (S - P) = S` when `S - P` is within the range they reach: the static and
  the code are within 2 GiB, as the psABI's medium any code model (`medany`,
  the Linux targets' default) has them ("Code Models", "Medium Any Code
  Model": it "allows the code to address the range between -2 GiB and +2 GiB
  from the current position"), and otherwise the linker reports an error
  (the same section: "The linker may raise an error if it cannot adjust the
  instructions to access the target address in the current code model").
  The linker may relax the pair ("Linker Relaxation", "Global-Pointer
  Relaxation": the `auipc` "can be removed" and the `addi` "replaced with a
  global-pointer-relative access instruction", `addi rd, gp, …`, which reads
  `gp`, never changed, and forms the same address). Either way it writes
  only `rd`. -/
def exec : Instr → State → Option State
  | .add d n m, s => some (s.write d (s.gpr n + s.gpr m))
  | .sub d n m, s => some (s.write d (s.gpr n - s.gpr m))
  | .addw d n m, s =>
    some (s.write d (sext32 ((s.gpr n).setWidth 32 + (s.gpr m).setWidth 32)))
  | .subw d n m, s =>
    some (s.write d (sext32 ((s.gpr n).setWidth 32 - (s.gpr m).setWidth 32)))
  | .sltu d n m, s => some (s.write d (if s.gpr n < s.gpr m then 1 else 0))
  | .mul d n m, s => some (s.write d (s.gpr n * s.gpr m))
  | .mulhu d n m, s =>
    some (s.write d (BitVec.ofNat 64 ((s.gpr n).toNat * (s.gpr m).toNat / 2 ^ 64)))
  | .logic op d n m, s =>
    let a := s.gpr n
    let b := s.gpr m
    some (s.write d (match op with | .and => a &&& b | .or => a ||| b | .xor => a ^^^ b))
  | .addi d n imm, s =>
    if imm12 imm then some (s.write d (s.gpr n + BitVec.ofInt 64 imm)) else none
  | .addiw d n imm, s =>
    if imm12 imm then some (s.write d (sext32 ((s.gpr n).setWidth 32 + BitVec.ofInt 32 imm)))
    else none
  | .logicImm op d n imm, s =>
    if imm12 imm then
      let a := s.gpr n
      let b := BitVec.ofInt 64 imm
      some (s.write d (match op with | .and => a &&& b | .or => a ||| b | .xor => a ^^^ b))
    else none
  | .li d imm, s => if imm12 imm then some (s.write d (BitVec.ofInt 64 imm)) else none
  | .addSp d imm, s => if imm < 2048 then some (s.write d (s.sp + BitVec.ofNat 64 imm)) else none
  | .lla d name, s => some (s.write d (s.syms name))
  | .lui d imm, s => some (s.write d (sext32 (imm ++ (0 : BitVec 12))))
  | .shift op .d d n sh, s =>
    if sh < 64 then
      let a := s.gpr n
      some (s.write d (match op with
        | .sll => a <<< sh | .srl => a >>> sh | .sra => a.sshiftRight sh))
    else none
  | .shift op .w d n sh, s =>
    if sh < 32 then
      let a := (s.gpr n).setWidth 32
      some (s.write d (sext32 (match op with
        | .sll => a <<< sh | .srl => a >>> sh | .sra => a.sshiftRight sh)))
    else none
  | .shiftReg op .d d n m, s =>
    let a := s.gpr n
    let sh := (s.gpr m).toNat % 64
    some (s.write d (match op with
      | .sll => a <<< sh | .srl => a >>> sh | .sra => a.sshiftRight sh))
  | .shiftReg op .w d n m, s =>
    let a := (s.gpr n).setWidth 32
    let sh := (s.gpr m).toNat % 32
    some (s.write d (sext32 (match op with
      | .sll => a <<< sh | .srl => a >>> sh | .sra => a.sshiftRight sh)))
  | .load wd t n off, s =>
    (addr s wd.bytes n off).bind fun a =>
      (s.load a wd.bytes).map fun v => s.write t (v.setWidth 64)
  | .store wd t n off, s =>
    (addr s wd.bytes n off).bind fun a => s.store a wd.bytes ((s.gpr t).setWidth (8 * wd.bytes))
  -- Only the push and pop of a frame (`push`, `pop`).
  | .push _, _ | .pop _, _ | .alloc _, _ | .free _, _ => none

def addrs : Instr → State → List Addr
  | .load _ _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .store _ _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .push _, s => [s.sp - 8]
  | .pop _, s => [s.sp + 8]
  | _, _ => []

/-- RV32I, "Conditional Branches": "beq and bne take the branch if registers
rs1 and rs2 are equal or unequal respectively. blt and bltu take the branch
if rs1 is less than rs2, using signed and unsigned comparison respectively.
bge and bgeu take the branch if rs1 is greater than or equal to rs2, using
signed and unsigned comparison respectively" (`beqz rs` and `bnez rs` are
`beq` and `bne` of `rs` and `x0`, which reads as zero). -/
def eval : Cond → State → Option Bool
  | .zero r, s => some (s.gpr r == 0)
  | .nonzero r, s => some (s.gpr r != 0)
  | .eq a b, s => some (s.gpr a == s.gpr b)
  | .ne a b, s => some (s.gpr a != s.gpr b)
  | .ltu a b, s => some (decide (s.gpr a < s.gpr b))
  | .geu a b, s => some (decide (s.gpr b ≤ s.gpr a))

/-- RV32I, "Unconditional Jumps": jal and jalr write "the address of the
instruction following the jump (`pc`+4)" to `rd`, and "the standard software
calling convention uses `x1` as the return address register" (`call` is
`auipc ra, …` then `jalr ra, …(ra)`, or `jal ra, …` once relaxed); then
the jump, possibly through a PLT entry, which may change `t0`–`t6` (see the
modelling choices). The return address and the values left in `t0`–`t6` are
the next eight of the state's. -/
def call (s : State) : Option State :=
  some { s with
    gpr := fun r =>
      match r with
      | .ra => s.unknowns 0 | .t0 => s.unknowns 1 | .t1 => s.unknowns 2
      | .t2 => s.unknowns 3 | .t3 => s.unknowns 4 | .t4 => s.unknowns 5
      | .t5 => s.unknowns 6 | .t6 => s.unknowns 7 | r => s.gpr r
    unknowns := fun n => s.unknowns (n + 8) }

/-- RV32I, "Unconditional Jumps" (`ret` is `jalr x0, 0(ra)`: "The target
address is obtained by adding the sign-extended 12-bit I-immediate to the
register rs1, then setting the least-significant bit of the result to zero",
and with `rd = x0` it writes no register). It returns after the call
instruction if `ra` is the return address the call left (`s₁`); otherwise
the model faults. -/
def ret (s₁ s₂ : State) : Option State :=
  if s₂.gpr .ra = s₁.gpr .ra then some s₂ else none

/-- The push of a frame: "Integer Register-Immediate Instructions" (`addi sp,
sp, -16`), then "Load and Store Instructions" (`sd rs, 8(sp)`). The 16 bytes
of the frame, which hold the register (and 8 bytes it does not write),
become a writable region, at the head of `wr`. Faults if the frame would
wrap around the address space (`sp < 16`).

`alloc bytes` is `addi sp, sp, -bytes` alone: the `bytes` bytes of the frame
become a writable region, at the head of `wr`, which it does not write: like
the 8 bytes of `push`'s frame that it does not write, they hold what memory
held there before, below the stack pointer, where the contract says nothing
of them (`Abi.reserved`). Faults unless `bytes` is a multiple of 16 with
`0 < bytes ≤ 4064`, or if the frame would wrap around the address space
(`sp < bytes`). Below 2048, `-bytes` is an encodable immediate, and so is
`bytes` for `free`. From 2048 on, `alloc` is two instructions, `addi sp, sp,
-2032` then `addi sp, sp, -(bytes - 2032)` (`-2048 ≤ -(bytes - 2032)`), and
`free` is `addi sp, sp, bytes - 2032` then `addi sp, sp, 2032`
(`bytes - 2032 < 2048`): one step of the model, as `push` is two
instructions. The stack pointer between them is harmless: neither writes
memory, nothing is stored to the frame until both have run, and each moves
`sp` by less than a page, as does the whole frame. -/
def push : Instr → State → Option State
  | .push r, s =>
    if 16 ≤ s.sp.toNat then
      let sp := s.sp - 16
      some { s with sp := sp, mem := s.mem.write (sp + 8) 8 (s.gpr r), wr := ⟨sp, 16⟩ :: s.wr }
    else none
  | .alloc bytes, s =>
    if 0 < bytes ∧ bytes ≤ 4064 ∧ bytes % 16 = 0 ∧ bytes ≤ s.sp.toNat then
      let sp := s.sp - BitVec.ofNat 64 bytes
      some { s with sp := sp, wr := ⟨sp, bytes⟩ :: s.wr }
    else none
  | _, _ => none

/-- The pop of a frame: "Load and Store Instructions" (`ld rd, 8(sp)`), then
"Integer Register-Immediate Instructions" (`addi sp, sp, 16`). Faults unless
the stack pointer and the writable regions are those the push left (`s₁`),
whose head is the frame; it removes that region. `free bytes` is `addi sp,
sp, bytes` alone (or the two `addi`s of `push`'s `alloc`), likewise for the
frame of `alloc bytes`. -/
def pop : Instr → State → State → Option State
  | .pop r, s₁, s₂ =>
    if s₂.sp = s₁.sp ∧ s₂.wr = s₁.wr ∧ s₁.wr.head? = some ⟨s₁.sp, 16⟩ then
      some { s₂.write r (s₂.mem.read (s₂.sp + 8) 8) with sp := s₂.sp + 16, wr := s₂.wr.tail }
    else none
  | .free bytes, s₁, s₂ =>
    if 0 < bytes ∧ bytes ≤ 4064 ∧ bytes % 16 = 0 ∧
        s₂.sp = s₁.sp ∧ s₂.wr = s₁.wr ∧ s₁.wr.head? = some ⟨s₁.sp, bytes⟩ then
      some { s₂ with sp := s₂.sp + BitVec.ofNat 64 bytes, wr := s₂.wr.tail }
    else none
  | _, _, _ => none

abbrev isa : ISA where
  State := State
  Instr := Instr
  Cond := Cond
  exec := exec
  addrs := addrs
  eval := eval
  call := call
  callAddrs _ := []
  ret := ret
  retAddrs _ := []
  -- No modelled instruction writes the stack pointer, other than the push
  -- and pop of a frame.
  writesSp _ := false
  push := push
  pop := pop
  -- Every modelled instruction is in RV64IM: RV64I, the base of every RV64
  -- target, and the M extension, which `rustCfg` requires.
  requires _ := []

end VG.RISCV64
