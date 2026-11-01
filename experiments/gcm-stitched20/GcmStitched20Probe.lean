import VerifiedGarbage.TCB.Code
import VerifiedGarbage.TCB.VectorCrypto
import VerifiedGarbage.TCB.Print
import VerifiedGarbage.Impl.Gcm.Clmul

-- Isolated experiment: extend only the register enumeration; no production model edits.


/-!
# POWER8 vector cryptography values

**Trusted.** Power ISA v3.1C, Book I §§6.9.1.1 (modular adds), 6.9.4
(logical), 6.8.5/6.8.7 (permute/shift), 6.11.1 (AES), 6.11.2 (SHA sigma), 6.11.3
(polynomial multiply). All were available on POWER8 / ISA 2.07.
https://openpower.foundation/specifications/isa/
https://www.ibm.com/support/pages/power8-cryptography-core-instructions

Architectural element 0 is the most significant element, independently of
memory endianness. AES uses that byte order for FIPS 197's state array.
Reuse the existing FIPS transformations and polynomial product from
`VectorCrypto`; those are pure values, not Arm instruction semantics. Its
AES helpers number bytes from the least significant end, so reverse bytes
at that boundary. In particular, inverse cipher adds the round key BEFORE
InvMixColumns, unlike AESDEC's equivalent-inverse round.

Only volatile vector registers v0–v19 (VSR32–VSR51) are operands. ELFv2
§2.2.2.1, Table 2.21 preserves v20–v31; leaving those and VSR0–VSR31 out
prevents code from modifying them, including the nonvolatile FPR aliases.
-/

@[expose] public section

namespace VG.PPCWideProbe

inductive VReg
  | v0 | v1 | v2 | v3 | v4 | v5 | v6 | v7 | v8 | v9
  | v10 | v11 | v12 | v13 | v14 | v15 | v16 | v17 | v18 | v19
  | v20 | v21 | v22 | v23 | v24 | v25 | v26 | v27 | v28 | v29 | v30 | v31
  deriving DecidableEq, Repr, Inhabited

def vbyte (x : BitVec 128) (i : Nat) : BitVec 8 := x.extractLsb' (8 * (15 - i)) 8
def vword (x : BitVec 128) (i : Nat) : BitVec 32 := x.extractLsb' (32 * (3 - i)) 32
def vdword (x : BitVec 128) (i : Nat) : BitVec 64 := x.extractLsb' (64 * (1 - i)) 64

def ofVBytes (f : Nat → BitVec 8) : BitVec 128 :=
  (List.range 16).foldl (fun x i => x ||| ((f i).setWidth 128 <<< (8 * (15 - i)))) 0

def rev128 (x : BitVec 128) : BitVec 128 := ofVBytes fun i => vbyte x (15 - i)

/-- Book I §6.11.1: SubBytes, ShiftRows, optionally MixColumns, AddRoundKey;
inverse: InvShiftRows, InvSubBytes, AddRoundKey, optionally InvMixColumns. -/
def vcipher (inverse last : Bool) (x k : BitVec 128) : BitVec 128 :=
  let x := rev128 x
  let k := rev128 k
  rev128 (if inverse then
    let y := VectorCrypto.aesMapBytes VectorCrypto.aesInvSbox (VectorCrypto.aesInvShiftRows x) ^^^ k
    if last then y else VectorCrypto.aesInvMixColumns y
  else
    let y := VectorCrypto.aesShiftRows (VectorCrypto.aesMapBytes VectorCrypto.aesSbox x)
    (if last then y else VectorCrypto.aesMixColumns y) ^^^ k)

/-- Book I §6.11.2, four SHA-256 functions; `st` selects upper-case Σ. -/
def sigma256 (st one : Bool) (x : BitVec 32) : BitVec 32 :=
  if st then
    if one then x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25
    else x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22
  else
    if one then x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ (x >>> 10)
    else x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ (x >>> 3)

/-- Book I §6.11.2, four SHA-512 functions. -/
def sigma512 (st one : Bool) (x : BitVec 64) : BitVec 64 :=
  if st then
    if one then x.rotateRight 14 ^^^ x.rotateRight 18 ^^^ x.rotateRight 41
    else x.rotateRight 28 ^^^ x.rotateRight 34 ^^^ x.rotateRight 39
  else
    if one then x.rotateRight 19 ^^^ x.rotateRight 61 ^^^ (x >>> 6)
    else x.rotateRight 1 ^^^ x.rotateRight 8 ^^^ (x >>> 7)

inductive VLogic | and | or | xor
  deriving DecidableEq, Repr

/-- Non-saturating vector instructions: none modifies VSCR or CR. -/
inductive VOp
  | cipher (inverse last : Bool) (d n m : VReg)
  | sbox (d n : VReg)
  | sha256 (d n : VReg) (st : Bool) (six : Nat)
  | sha512 (d n : VReg) (st : Bool) (six : Nat)
  | pmsumd (d n m : VReg)
  | logic (op : VLogic) (d n m : VReg)
  /-- `vsel`: mask bit zero selects VA, mask bit one selects VB.
  NXP AltiVec Programming Environments Manual (06/2014), p. 6-163,
  Figure 6-124; no other registers are changed. Baseline AltiVec.
  https://www.nxp.com/docs/en/reference-manual/ALTIVECPOWERISAPEM.pdf#page=257 -/
  | sel (d n m mask : VReg)
  /-- `vadduwm` / `vaddudm`: add modulo 2^32 / 2^64 per element. -/
  | add (doubleword : Bool) (d n m : VReg)
  /-- `vperm`: each byte selects the low five bits of its control byte. -/
  | perm (d n m c : VReg)
  /-- `vsldoi`: concatenate VA||VB and select bytes SHB through SHB+15. -/
  | sldoi (d n m : VReg) (sh : Nat)
  deriving DecidableEq, Repr

/-- The destination and result; reject unencodable and reserved immediates.
SHA SIX is numbered from its MSB: word i uses bit i, doubleword i bit 2i;
for the doubleword instruction the other two SIX bits are reserved. -/
def VOp.eval (v : VReg → BitVec 128) : VOp → Option (VReg × BitVec 128)
  | .cipher inv last d n m => some (d, vcipher inv last (v n) (v m))
  | .sbox d n => some (d, ofVBytes fun i => VectorCrypto.aesSbox (vbyte (v n) i))
  | .sha256 d n st six => if six < 16 then
      some (d, (List.range 4).foldl (fun x i => x |||
        ((sigma256 st (six.testBit (3 - i)) (vword (v n) i)).setWidth 128 <<< (32 * (3 - i)))) 0)
    else none
  | .sha512 d n st six => if six < 16 ∧ six &&& 5 = 0 then
      some (d, sigma512 st (six.testBit 3) (vdword (v n) 0) ++
        sigma512 st (six.testBit 1) (vdword (v n) 1))
    else none
  | .pmsumd d n m => some (d,
      VectorCrypto.polyMul (vdword (v n) 0) (vdword (v m) 0) ^^^
      VectorCrypto.polyMul (vdword (v n) 1) (vdword (v m) 1))
  | .logic op d n m => some (d, match op with
      | .and => v n &&& v m | .or => v n ||| v m | .xor => v n ^^^ v m)
  | .sel d n m mask => some (d, (v n &&& ~~~v mask) ||| (v m &&& v mask))
  | .add dw d n m => some (d, if dw then
      (vdword (v n) 0 + vdword (v m) 0) ++ (vdword (v n) 1 + vdword (v m) 1)
    else (List.range 4).foldl (fun x i => x |||
      ((vword (v n) i + vword (v m) i).setWidth 128 <<< (32 * (3 - i)))) 0)
  | .perm d n m c => some (d, ofVBytes fun i =>
      let j := (vbyte (v c) i).toNat % 32
      if j < 16 then vbyte (v n) j else vbyte (v m) (j - 16))
  | .sldoi d n m sh => if sh < 16 then
      some (d, ((v n ++ v m) <<< (8 * sh)).extractLsb' 128 128)
    else none

end VG.PPCWideProbe


/-!
# 64-bit little-endian PowerPC machine model

**Trusted.** A model of the subset of the 64-bit Power ISA used by our
implementations, in little-endian mode. Each instruction's semantics here
must agree with the Power ISA, Version 3.1C (OpenPOWER Foundation), Book I
(chapter 2, "Branch Facility", chapter 3, "Fixed-Point Facility", chapter 6,
"Vector Facility", and chapter 7, "Vector-Scalar Floating-Point Operations"); when
adding an instruction, cite the section whose pseudocode (RTL) it
transcribes. The RTL numbers bits from 0 at the most significant end:
`(RS)32:63` is the low 32 bits of `RS`.

Modelling choices:
* Registers are `r0`, `r2`–`r12` and `r14`–`r31`. The stack pointer `r1` is
  separate: only the push and pop of a frame (see `push`) write it, and
  only they and `addSp` (`addi RT, r1, SI`, a pointer into the stack) read
  it. `r13` is the thread pointer, which the ABI reserves (ELFv2 ABI §2.2.2.1,
  Table 2.21, "Reserved"): it is never an operand, so never changed. The link
  register `LR` is modelled (`State.lr`), and of `XER` only its carry bit CA
  (`State.ca`, see below); the count register, the rest of `XER` and the
  condition register are not, and no modelled instruction reads them.
* The carry bit CA is what the carrying adds and subtracts (`addc`, `adde`,
  `addze`, `subc`, `sube`) set and the extended ones read, in 64-bit mode
  the carry out of the 64-bit sum (Book I §3.3.9). `XER` is volatile across
  calls (ELFv2 ABI §2.2.2.1, Table 2.21), so a contract says nothing of CA
  and code may not rely on it across a call or at its entry; nothing else
  reads or writes it, and it is never a branch condition or an address.
* The integer registers are 64 bits. The only 32-bit GPR operations are the rotates and
  shifts of words (`rlwinm`, which reads the low 32 bits and zero-extends
  its 32-bit result), the loads of words (zero-extended), the stores of words
  (the low 32 bits) and the comparison of a word with zero; `add`, `subf`
  and the logical instructions always act on all 64 bits.
* POWER8 / ISA 2.07 vector cryptography is baseline for this target (IBM,
  "POWER8 Cryptography In-core Instructions"). Vector values and their
  most-significant-first element numbering are in `PPCWideProbe/Simd.lean`.
  Only volatile v0–v19 are modelled, so the nonvolatile vector and FPR
  registers cannot be changed. VSX load/store doubleword pairs do not
  require alignment; the first memory doubleword is the high register
  half. `mtvsrd` leaves its low half undefined, supplied by `unknowns`.
* In the forms that read `(RA|0)`, `RA = 0` means the value 0, not `r0`: the
  model has only `li` (`addi RT, 0, SI`) and `lis` (`addis RT, 0, SI`) of
  those, and every other such instruction with `r0` as its base (`RA`)
  faults, so verified code never uses them.
* Immediates and displacements that the instruction cannot encode make the
  instruction fault, so verified code only ever contains encodable
  instructions. Displacements are non-negative.
* A branch condition (`Cond`) is a comparison with zero into condition
  register field 0 followed by the conditional branch on it (`cmpldi`/`cmplwi`
  then `beq`/`bne`): `CR0` is volatile (ELFv2 ABI §2.2.2.1, "Condition
  Register Fields") and nothing else reads it.
* Memory accesses (bytes, words and doublewords) must lie within the state's
  permitted regions: loads within `rd ++ wr`, stores within `wr`; otherwise
  the instruction faults. In little-endian mode `MEM(EA, n)` is the `n`
  bytes at `EA` with the byte at `EA + n - 1` most significant (Book I §1.3.2,
  "Notation", `MEM(x, y)`), i.e. a little-endian read (`Mem.read`).
* Instructions whose timing depends on their operands (e.g. `divd`) must
  never be added: the constant-time leakage model assumes they do not exist.
  The Power ISA makes no architectural promise about multiply timing. The
  model has only the 64-bit multiplies `mulld` and `mulhdu`, which T.
  Pornin's survey ("Constant-Time Mul", BearSSL,
  https://www.bearssl.org/ctmul.html) reports as constant time on POWER8 and
  POWER9 in 64-bit mode (its table: "Y" for every multiply on both, "POWER8
  and POWER9 have constant-time multiplications"), the cores of the baseline
  ISA of `powerpc64le-unknown-linux-gnu` (Power ISA 2.07, POWER8) and its
  successor; it does not cover POWER10 or later. The 32-bit `mullw` is left
  out: the survey notes that older cores may terminate it early depending
  on its operands.
* Calls are `bl` and returns `blr` (Book I §2.4, "Branch Instructions"). The
  return addresses are the next of the state's `unknowns`, which nothing
  constrains (see `TCB/Code.lean`). Linkage code the linker may put between
  a `bl` and its target (a long-branch stub) may change `r0`, `r11` and
  `r12` (ELFv2 ABI §2.2.2.1, "Optional Function Linkage": "a function cannot
  depend on the values of those registers that are optional in the function
  linkage (r0, r11, and r12) because they may be altered by interlibrary
  calls"), so a call leaves unknown values in them too. The linker only adds
  a stub that saves `r2` to the stack if a `nop` follows the `bl` (ELFv2 ABI
  §2.2.1, "Function Call Linkage Protocols"), which the printer never emits,
  so a call does not access memory.
* The stack pointer is always 16-byte aligned (ELFv2 ABI §2.2.3.1, "The
  stack shall be quadword aligned"), and a frame moves it by 48 bytes or
  by a multiple of 16, so the model does not check the alignment.
* A `static` the code reads (`Artifact.consts`) is at the address
  `State.syms name`, where `name` is its name, which `adrSym` puts in a
  register: `bcl 20, 31, $+4` leaves the address of the next instruction in
  `LR`, `mflr` copies it, and `addis` and `addi` add the static's distance
  from there, which the linker resolves (see `exec`). No instruction changes
  `syms`: a static's address is fixed for the run of the program. The model
  does not know the address `bcl` leaves in `LR`: it is the next of the
  state's `unknowns`, as a call's return address is, so code that returns
  after an `adrSym` must restore `LR`.
* A table carried by an instruction (`lxvd2xTbl`, its name and words) is
  the immutable static of that name the emitter writes (`TCB/Rust.lean`),
  as for AArch64's `ldrqTbl` and x86-64's `aluTbl`: throughout execution it
  is readable at `State.syms name`, holds those little-endian 8-byte words,
  and does not wrap around the address space. No writable region or stack
  overlaps it. The linker places the immutable static in read-only memory,
  apart from other objects and the stack; no pointer the program writes
  through may reach it. The model therefore reads its words from the
  instruction, independently of `State.mem` and the contract's regions.
  The printed instruction uses registers, so execution faults unless their
  base register holds the static's address and its index selects two words
  within the table. Leakage records the index, as for x86-64's table loads.
* A frame may instead allocate a buffer on the stack (`alloc`, `stdu r1,
  -bytes(r1)`), released by its pop (`free`, `addi r1, r1, bytes`): the
  frame is the 32-byte header of the ELFv2 minimum frame (as for `push`)
  followed by `bytes - 32` bytes of local variable space, which becomes a
  writable region. `bytes` is a multiple of 16, more than 32 and less than
  4096, as for the frames of the other models: less than a page, so that
  the allocation does not move `r1` past a guard page below the stack.
-/

@[expose] public section

namespace VG.PPCWideProbe

inductive Reg
  | r0 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9 | r10 | r11 | r12
  | r14 | r15 | r16 | r17 | r18 | r19 | r20 | r21 | r22 | r23 | r24 | r25 | r26 | r27 | r28
  | r29 | r30 | r31
  deriving DecidableEq, Repr, Inhabited

/-- Operand size of the loads, stores, rotates, shifts and comparisons: a
word (32 bits) or a doubleword (64 bits). -/
inductive Size | w | d
  deriving DecidableEq, Repr

abbrev Size.bits : Size → Nat
  | .w => 32
  | .d => 64

abbrev Size.bytes : Size → Nat
  | .w => 4
  | .d => 8

structure State where
  gpr : Reg → BitVec 64
  /-- Volatile vector registers only; the nonvolatile vectors cannot be operands. -/
  vpr : VReg → BitVec 128 := fun _ => 0
  /-- The link register. -/
  lr : BitVec 64
  /-- The stack pointer, `r1`. -/
  sp : BitVec 64
  mem : Mem
  /-- Regions the code may read (in addition to `wr`). -/
  rd : List Region
  /-- Regions the code may read and write. -/
  wr : List Region
  /-- Values the model does not know, used in order: the return address each
  call stores, what linkage code may leave in `r0`, `r11` and `r12` (see
  `TCB/Code.lean`), the address each `adrSym` leaves in `LR`, and the
  undefined low doubleword of each `mtvsrd`. -/
  unknowns : Nat → BitVec 64 := fun _ => 0
  /-- The address of each `static` the code can name (`adrSym`), by name. -/
  syms : String → BitVec 64 := fun _ => 0
  /-- `XER`'s carry bit, CA. -/
  ca : Bool := false

inductive LogicOp | and | or | xor
  deriving DecidableEq, Repr

inductive Instr
  /-- `add RT, RA, RB` -/
  | add (d n m : Reg)
  /-- `subf RT, RB, RA` (extended mnemonic `sub RT, RA, RB`): `d := n - m` -/
  | sub (d n m : Reg)
  /-- `mulld RT, RA, RB`: the low 64 bits of the product -/
  | mul (d n m : Reg)
  /-- `mulhdu RT, RA, RB`: the high 64 bits of the unsigned product -/
  | mulhu (d n m : Reg)
  /-- `addc RT, RA, RB`: `d := n + m`, CA the carry out -/
  | addc (d n m : Reg)
  /-- `adde RT, RA, RB`: `d := n + m + CA`, CA the carry out -/
  | adde (d n m : Reg)
  /-- `addze RT, RA`: `d := n + CA`, CA the carry out -/
  | addze (d n : Reg)
  /-- `subfc RT, RB, RA` (extended mnemonic `subc RT, RA, RB`): `d := n - m`,
  CA set iff there is no borrow (`n ≥ m`) -/
  | subc (d n m : Reg)
  /-- `subfe RT, RB, RA`: `d := n - m - 1 + CA`, CA set iff there is no
  borrow (`n + CA ≥ m + 1`) -/
  | sube (d n m : Reg)
  /-- `addi RT, RA, SI` with `0 ≤ SI < 2 ^ 15`, `RA ≠ 0` -/
  | addi (d n : Reg) (imm : Nat)
  /-- `addi RT, RA, -imm` (extended mnemonic `subi`), `0 ≤ imm ≤ 2 ^ 15`,
  `RA ≠ 0` -/
  | subi (d n : Reg) (imm : Nat)
  /-- `li RT, SI` (`addi RT, 0, SI`), `0 ≤ SI < 2 ^ 15` -/
  | li (d : Reg) (imm : Nat)
  /-- `lis RT, SI` (`addis RT, 0, SI`) -/
  | lis (d : Reg) (imm : BitVec 16)
  /-- `ori RA, RS, UI` -/
  | ori (d n : Reg) (imm : BitVec 16)
  /-- `oris RA, RS, UI` -/
  | oris (d n : Reg) (imm : BitVec 16)
  /-- `and`/`or`/`xor RA, RS, RB` -/
  | logic (op : LogicOp) (d n m : Reg)
  /-- A rotation right by `sh < size`: `rlwinm RA, RS, (32 - sh) % 32, 0, 31`
  (extended mnemonic `rotrwi`) for a word, `rldicl RA, RS, (64 - sh) % 64, 0`
  (`rotrdi`) for a doubleword -/
  | rotr (sz : Size) (d n : Reg) (sh : Nat)
  /-- A logical shift right by `sh < size`: `rlwinm RA, RS, (32 - sh) % 32,
  sh, 31` (extended mnemonic `srwi`) for a word, `rldicl RA, RS, (64 - sh) %
  64, sh` (`srdi`) for a doubleword -/
  | lsr (sz : Size) (d n : Reg) (sh : Nat)
  /-- A shift left of a doubleword by `sh < 64`: `rldicr RA, RS, sh, 63 - sh`
  (extended mnemonic `sldi`) -/
  | lsl (d n : Reg) (sh : Nat)
  /-- `lwz RT, D(RA)` (word, zero-extended) or `ld RT, DS(RA)` (doubleword,
  `DS` a multiple of 4), `0 ≤ D < 2 ^ 15`, `RA ≠ 0` -/
  | load (sz : Size) (t n : Reg) (off : Nat)
  /-- `stw RS, D(RA)` (the low 32 bits) or `std RS, DS(RA)` (`DS` a multiple
  of 4), `0 ≤ D < 2 ^ 15`, `RA ≠ 0` -/
  | store (sz : Size) (t n : Reg) (off : Nat)
  /-- `lbz RT, D(RA)`: the byte, zero-extended; `0 ≤ D < 2 ^ 15`, `RA ≠ 0` -/
  | lbz (t n : Reg) (off : Nat)
  /-- `stb RS, D(RA)`: the low byte; `0 ≤ D < 2 ^ 15`, `RA ≠ 0` -/
  | stb (t n : Reg) (off : Nat)
  /-- `lwbrx RT, RA, RB` (word, zero-extended) or `ldbrx RT, RA, RB`
  (doubleword): a load at `RA + RB` with the bytes reversed, i.e. big-endian;
  `RA ≠ 0` -/
  | loadRev (sz : Size) (t a b : Reg)
  /-- `stwbrx RS, RA, RB` (the low 32 bits) or `stdbrx RS, RA, RB`: a store at
  `RA + RB` with the bytes reversed, i.e. big-endian; `RA ≠ 0` -/
  | storeRev (sz : Size) (t a b : Reg)
  /-- `mflr RT` (`mfspr RT, 8`) -/
  | mflr (d : Reg)
  /-- `mtlr RS` (`mtspr 8, RS`) -/
  | mtlr (s : Reg)
  /-- `bcl 20, 31, $+4`, `mflr RT`, `addis RT, RT, (S - L)@ha` and `addi RT,
  RT, (S - L)@l`, where `S` is the address of the `static` named `name` and
  `L` that of the `mflr`: `RT ← S`, and `LR` changed (see `exec`); `RT ≠ 0` -/
  | adrSym (d : Reg) (name : String)
  /-- `stdu r1, -48(r1)` then `std RS, 32(r1)`: the push of a frame of 48
  bytes (see `push`) -/
  | push (r : Reg)
  /-- `ld RT, 32(r1)` then `addi r1, r1, 48`: the pop of a frame of 48 bytes
  (see `pop`) -/
  | pop (r : Reg)
  /-- `stdu r1, -bytes(r1)`: the push of a frame of `bytes` bytes whose local
  variable space it does not write (see `push`); `32 < bytes < 4096`, a
  multiple of 16 -/
  | alloc (bytes : Nat)
  /-- `addi r1, r1, bytes`: the pop of a frame of `bytes` bytes (see `pop`) -/
  | free (bytes : Nat)
  /-- `addi RT, r1, SI` with `0 ≤ SI < 2 ^ 15`: a pointer `SI` bytes above the
  stack pointer -/
  | addSp (d : Reg) (imm : Nat)
  /-- POWER8 vector arithmetic and cryptography (Book I chapter 6). -/
  | vop (op : VOp)
  /-- `lxvd2x XT, RA, RB`, XT = vector register + 32 (Book I §7.6.2.1.2).
  Unaligned 16-byte access; RA must not be r0, as for `addrX`. -/
  | lxvd2x (d : VReg) (a b : Reg)
  /-- The same `lxvd2x` reading two words of the immutable static `name`,
  at the byte offset in RB (a multiple of 8). RA must hold
  `State.syms name`; the emitter supplies `words` (see module docs). -/
  | lxvd2xTbl (d : VReg) (a b : Reg) (name : String) (words : List (BitVec 64))
  /-- `stxvd2x XS, RA, RB`, XS = vector register + 32 (Book I §7.6.2.1.2). -/
  | stxvd2x (n : VReg) (a b : Reg)
  /-- `mtvsrd XT, RA`, XT = vector register + 32 (Book I §3.3.18).
  The high doubleword is RA; the low doubleword is undefined, not zero. -/
  | mtvsrd (d : VReg) (n : Reg)
  /-- `mfvsrd RA, XS`, XS = vector register + 32: the high doubleword. -/
  | mfvsrd (d : Reg) (n : VReg)
  deriving DecidableEq, Repr

/-- Branch conditions: a comparison with zero into `CR0`, then the branch. -/
inductive Cond
  /-- `cmplwi cr0, RA, 0` (word) or `cmpldi cr0, RA, 0` (doubleword), then
  `beq cr0, …`: the register (of the given size) is zero -/
  | zero (sz : Size) (r : Reg)
  /-- `cmplwi`/`cmpldi cr0, RA, 0`, then `bne cr0, …`: the register (of the
  given size) is not zero -/
  | nonzero (sz : Size) (r : Reg)
  deriving DecidableEq, Repr

namespace State

/-- A register at the operand size: the low 32 bits (`(RS)32:63`) of a word. -/
def read (s : State) (sz : Size) (r : Reg) : BitVec sz.bits := (s.gpr r).setWidth sz.bits

/-- Write all 64 bits of a register. -/
def write (s : State) (r : Reg) (v : BitVec 64) : State :=
  { s with gpr := fun r' => if r' = r then v else s.gpr r' }

/-- Write a volatile vector register (VSR32–VSR51). -/
def writeV (s : State) (r : VReg) (v : BitVec 128) : State :=
  { s with vpr := fun r' => if r' = r then v else s.vpr r' }

/-- Write the low 64 bits of the sum `v` into a register, and its carry out
(`2⁶⁴ ≤ v`) into CA. -/
def writeCarry (s : State) (r : Reg) (v : Nat) : State :=
  { s.write r (BitVec.ofNat 64 v) with ca := decide (2 ^ 64 ≤ v) }

/-- Load `n` bytes, faulting if not permitted. -/
def load (s : State) (a : Addr) (n : Nat) : Option (BitVec (8 * n)) :=
  if InRegions (s.rd ++ s.wr) a n then some (s.mem.read a n) else none

/-- Store `n` bytes, faulting if not permitted. -/
def store (s : State) (a : Addr) (n : Nat) (v : BitVec (8 * n)) : Option State :=
  if InRegions s.wr a n then some { s with mem := s.mem.write a n v } else none

end State

/-- The effective address `(RA) + D` of `D(RA)` for an access of `bytes`
bytes, if the displacement is encodable and `RA ≠ 0` (Book I §3.3.2, "Load
Word and Zero", `EA ← b + EXTS(D)` with `b ← (RA)`, and likewise for the
other D-form loads and stores; §3.3.2 "Load Doubleword" and §3.3.3 "Store
Doubleword", DS-form: `EA ← b + EXTS(DS || 0b00)`, so the displacement is a
multiple of 4). The displacement is non-negative here. -/
def addr (s : State) (bytes : Nat) (n : Reg) (off : Nat) : Option Addr :=
  if n ≠ .r0 ∧ off < 2 ^ 15 ∧ (bytes = 8 → off % 4 = 0) then some (s.gpr n + BitVec.ofNat 64 off)
  else none

/-- The effective address `(RA) + (RB)` of an X-form access, if `RA ≠ 0`
(Book I §3.3.5: `EA ← b + (RB)` with `b ← (RA)`). -/
def addrX (s : State) (a b : Reg) : Option Addr :=
  if a ≠ .r0 then some (s.gpr a + s.gpr b) else none

/-- Reverse the bytes of a word. -/
def rev32 (a : BitVec 32) : BitVec 32 :=
  a.extractLsb' 0 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8

/-- Reverse the bytes of a doubleword. -/
def rev64 (a : BitVec 64) : BitVec 64 :=
  a.extractLsb' 0 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8 ++
    a.extractLsb' 32 8 ++ a.extractLsb' 40 8 ++ a.extractLsb' 48 8 ++ a.extractLsb' 56 8

/-- The value `v` at the operand size, zero-extended into a register. -/
abbrev Size.ext (sz : Size) (v : BitVec sz.bits) : BitVec 64 := v.setWidth 64

/-- Swap the doublewords. In little-endian mode `lxvd2x` places MEM(EA,8)
in architectural doubleword 0 (the HIGH half) and MEM(EA+8,8) in doubleword
1. `stxvd2x` is the inverse (Book I §7.6.2.1.2, load/store doubleword*2 indexed).
This is not a byte reversal, nor a plain 128-bit little-endian load. -/
def swapDwords (x : BitVec 128) : BitVec 128 := vdword x 1 ++ vdword x 0

/-- Semantics, transcribing the Power ISA 3.1C, Book I:
* §3.3.9 "Add" (`RT ← (RA) + (RB)`), "Subtract From" (`RT ← ¬(RA) + (RB)
  + 1`, i.e. `(RB) - (RA)`), "Add Immediate" (`RT ← (RA|0) + EXTS(SI)`; `li`
  is `addi RT, 0, SI`, `subi RT, RA, imm` is `addi RT, RA, -imm`, and
  `addSp` is `addi RT, 1, SI`, whose `RA` is `r1`), "Add Immediate
  Shifted" (`lis RT, SI` is `addis RT, 0, SI`: `RT ← EXTS(SI ||
  0x0000)`); the non-record, non-overflow forms, which set no other
  register;
* §3.3.9 "Add Carrying" (`RT ← (RA) + (RB)`), "Add Extended" (`RT ← (RA) +
  (RB) + CA`), "Add to Zero Extended" (`RT ← (RA) + CA`), "Subtract From
  Carrying" (`RT ← ¬(RA) + (RB) + 1`; `subc RT, RA, RB` is `subfc RT, RB,
  RA`) and "Subtract From Extended" (`RT ← ¬(RA) + (RB) + CA`), each of
  which "the carry out ... is placed into CA" (in 64-bit mode, the carry
  out of bit 0: of the 64-bit sum); the non-record, non-overflow forms,
  which set no other register than RT and CA (CA32 is not modelled);
* §3.3.9.1, "64-bit Fixed-Point Arithmetic Instructions": "Multiply Low
  Doubleword" (`prod0:127 ← (RA) × (RB)`, `RT ← prod64:127`: the low 64
  bits of the product, which are the same for signed and unsigned
  operands) and "Multiply High Doubleword Unsigned" (`prod0:127 ← (RA) ×u
  (RB)`, `RT ← prod0:63`: the high 64 bits of the unsigned product); the
  non-record, non-overflow forms, which set no other register;
* §3.3.13 "OR Immediate" (`RA ← (RS) | (48 0 || UI)`), "OR Immediate
  Shifted" (`RA ← (RS) | (32 0 || UI || 16 0)`), "AND", "OR", "XOR" (the
  non-record forms);
* §3.3.14.1 "Rotate Left Word Immediate then AND with Mask" (`r ←
  ROTL32((RS)32:63, SH)`, `m ← MASK(MB+32, ME+32)`, `RA ← r & m`, where
  `ROTL32(x, n)` rotates `x || x` left, so with `MB = 0` and `ME = 31`, `m`
  selects the low 32 bits and `RA` is the word rotated left by `SH`,
  zero-extended; rotating left by `(32 - sh) % 32` rotates right by `sh`;
  with `MB = sh`, `m` further clears the high `sh` bits of the word, which
  leaves the word shifted right by `sh`); "Rotate Left Doubleword Immediate
  then Clear Left" (`RA ← ROTL64((RS), SH) & MASK(MB, 63)`: with `MB = 0` a
  rotation, and a rotation left by `(64 - sh) % 64` is one right by `sh`;
  with `MB = sh`, the doubleword shifted right by `sh`); "Rotate Left
  Doubleword Immediate then Clear Right" (`RA ← ROTL64((RS), SH) & MASK(0,
  ME)`: with `ME = 63 - sh`, the doubleword shifted left by `sh`);
* §3.3.2 "Load Byte and Zero" (`RT ← 56 0 || MEM(EA, 1)`), "Load Word and
  Zero" (`RT ← 32 0 || MEM(EA, 4)`), "Load Doubleword" (`RT ← MEM(EA, 8)`);
  §3.3.3 "Store Byte" (`MEM(EA, 1) ← (RS)56:63`), "Store Word" (`MEM(EA, 4)
  ← (RS)32:63`), "Store Doubleword" (`MEM(EA, 8) ← (RS)`);
* §3.3.5 "Load Word Byte-Reverse Indexed" (`load_data ← MEM(EA, 4)`, `RT ←
  32 0 || load_data24:31 || load_data16:23 || load_data8:15 ||
  load_data0:7`), "Store Word Byte-Reverse Indexed" (`MEM(EA, 4) ←
  (RS)56:63 || (RS)48:55 || (RS)40:47 || (RS)32:39`); §3.3.5.1 "Load
  Doubleword Byte-Reverse Indexed" and "Store Doubleword Byte-Reverse
  Indexed", likewise for the eight bytes;
* §3.3.19 "Move From Special Purpose Register" (`mflr RT` is `mfspr RT, 8`:
  `RT ← LR`) and "Move To Special Purpose Register" (`mtlr RS` is `mtspr 8,
  RS`: `LR ← (RS)`);
* `adrSym d name` is four instructions, which the linker completes with the
  static's address `S` (`State.syms name`): §2.4 "Branch Conditional"
  (`bcl 20, 31, $+4`: `BO = 20`, branch always, to the next instruction,
  and `LK = 1`: `LR ← CIA + 4`), "Move From Special Purpose Register" (`mflr
  RT`: `RT ← LR`, the address `L` of the `mflr` itself), then §3.3.9 "Add
  Immediate Shifted" (`addis RT, RT, SI`: `RT ← (RA) + EXTS(SI || 0x0000)`)
  and "Add Immediate" (`addi RT, RT, SI`: `RT ← (RA) + EXTS(SI)`) of
  `#ha(S - L)` and `#lo(S - L)`, the values of the relocations
  `R_PPC64_REL16_HA` and `R_PPC64_REL16_LO` of `S - L` (ELFv2 ABI, "Relocation
  Types Table"; "Relocation Notations": `#lo(x) = x & 0xffff` and `#ha(x) =
  ((x >> 16) + ((x & 0x8000) ? 1 : 0)) & 0xffff`), so that `RT ← L + (S -
  L) = S` when `S - L` fits in 32 signed bits: the static and the code are
  less than 2 GB apart, as the ABI's medium code model, the default, has
  them (ELFv2 ABI, "Code Models"). With `RT = 0`, `addis` and `addi` would
  read 0 for `(RA|0)`, so the model faults. The model does not know `L`:
  `LR` gets the next of the state's `unknowns`. -/
def exec : Instr → State → Option State
  | .vop op, s => (op.eval s.vpr).map fun (d, v) => s.writeV d v
  | .lxvd2x d a b, s =>
    (addrX s a b).bind fun ea => (s.load ea 16).map fun v => s.writeV d (swapDwords v)
  -- Book I §7.6.2.1.2: `lxvd2x` places MEM(EA,8) in the high
  -- doubleword and MEM(EA+8,8) in the low doubleword in little-endian
  -- mode. The guard ties that access to two words of the emitted static.
  | .lxvd2xTbl d a b name ws, s =>
    let off := (s.gpr b).toNat
    if a ≠ .r0 ∧ s.gpr a = s.syms name ∧ off % 8 = 0 ∧ off / 8 + 2 ≤ ws.length then
      some (s.writeV d (ws.getD (off / 8) 0 ++ ws.getD (off / 8 + 1) 0))
    else none
  | .stxvd2x n a b, s =>
    (addrX s a b).bind fun ea => s.store ea 16 (swapDwords (s.vpr n))
  | .mtvsrd d n, s => some { s.writeV d (s.gpr n ++ s.unknowns 0) with
      unknowns := fun i => s.unknowns (i + 1) }
  | .mfvsrd d n, s => some (s.write d (vdword (s.vpr n) 0))
  | .add d n m, s => some (s.write d (s.gpr n + s.gpr m))
  | .sub d n m, s => some (s.write d (s.gpr n - s.gpr m))
  | .mul d n m, s => some (s.write d (s.gpr n * s.gpr m))
  | .mulhu d n m, s =>
    some (s.write d (BitVec.ofNat 64 ((s.gpr n).toNat * (s.gpr m).toNat / 2 ^ 64)))
  | .addc d n m, s => some (s.writeCarry d ((s.gpr n).toNat + (s.gpr m).toNat))
  | .adde d n m, s => some (s.writeCarry d ((s.gpr n).toNat + (s.gpr m).toNat + s.ca.toNat))
  | .addze d n, s => some (s.writeCarry d ((s.gpr n).toNat + s.ca.toNat))
  -- `¬(RA) + (RB) + 1` with `RA = m` and `RB = n`: `¬m` is `2⁶⁴ - 1 - m`.
  | .subc d n m, s => some (s.writeCarry d ((s.gpr n).toNat + (2 ^ 64 - 1 - (s.gpr m).toNat) + 1))
  | .sube d n m, s =>
    some (s.writeCarry d ((s.gpr n).toNat + (2 ^ 64 - 1 - (s.gpr m).toNat) + s.ca.toNat))
  | .addi d n imm, s =>
    if n ≠ .r0 ∧ imm < 2 ^ 15 then some (s.write d (s.gpr n + BitVec.ofNat 64 imm)) else none
  | .subi d n imm, s =>
    if n ≠ .r0 ∧ imm ≤ 2 ^ 15 then some (s.write d (s.gpr n - BitVec.ofNat 64 imm)) else none
  | .li d imm, s => if imm < 2 ^ 15 then some (s.write d (BitVec.ofNat 64 imm)) else none
  | .addSp d imm, s => if imm < 2 ^ 15 then some (s.write d (s.sp + BitVec.ofNat 64 imm)) else none
  | .lis d imm, s => some (s.write d ((imm ++ (0 : BitVec 16)).signExtend 64))
  | .ori d n imm, s => some (s.write d (s.gpr n ||| imm.setWidth 64))
  | .oris d n imm, s => some (s.write d (s.gpr n ||| imm.setWidth 64 <<< 16))
  | .logic op d n m, s =>
    let a := s.gpr n
    let b := s.gpr m
    some (s.write d (match op with | .and => a &&& b | .or => a ||| b | .xor => a ^^^ b))
  | .rotr sz d n sh, s =>
    if sh < sz.bits then some (s.write d (sz.ext ((s.read sz n).rotateRight sh))) else none
  | .lsr sz d n sh, s =>
    if sh < sz.bits then some (s.write d (sz.ext (s.read sz n >>> sh))) else none
  | .lsl d n sh, s => if sh < 64 then some (s.write d (s.gpr n <<< sh)) else none
  | .load sz t n off, s =>
    (addr s sz.bytes n off).bind fun a =>
      (s.load a sz.bytes).map fun v => s.write t (v.setWidth 64)
  | .store sz t n off, s =>
    (addr s sz.bytes n off).bind fun a => s.store a sz.bytes ((s.gpr t).setWidth (8 * sz.bytes))
  | .lbz t n off, s =>
    (addr s 1 n off).bind fun a => (s.load a 1).map fun v => s.write t (v.setWidth 64)
  | .stb t n off, s =>
    (addr s 1 n off).bind fun a => s.store a 1 ((s.gpr t).setWidth 8)
  | .loadRev .w t a b, s =>
    (addrX s a b).bind fun ea => (s.load ea 4).map fun v => s.write t ((rev32 v).setWidth 64)
  | .loadRev .d t a b, s =>
    (addrX s a b).bind fun ea => (s.load ea 8).map fun v => s.write t (rev64 v)
  | .storeRev .w t a b, s =>
    (addrX s a b).bind fun ea => s.store ea 4 (rev32 (s.read .w t))
  | .storeRev .d t a b, s =>
    (addrX s a b).bind fun ea => s.store ea 8 (rev64 (s.gpr t))
  | .mflr d, s => some (s.write d s.lr)
  | .mtlr r, s => some { s with lr := s.gpr r }
  | .adrSym d name, s =>
    if d ≠ .r0 then
      some { s.write d (s.syms name) with lr := s.unknowns 0, unknowns := fun n => s.unknowns (n + 1) }
    else none
  -- Only the push and pop of a frame (`push`, `pop`).
  | .push _, _ | .pop _, _ | .alloc _, _ | .free _, _ => none

def addrs : Instr → State → List Addr
  | .lxvd2xTbl _ _ b .., s => [s.gpr b]
  | .lxvd2x _ a b, s | .stxvd2x _ a b, s => [s.gpr a + s.gpr b]
  | .load _ _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .store _ _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .lbz _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .stb _ n off, s => [s.gpr n + BitVec.ofNat 64 off]
  | .loadRev _ _ a b, s => [s.gpr a + s.gpr b]
  | .storeRev _ _ a b, s => [s.gpr a + s.gpr b]
  | .push _, s => [s.sp - 48, s.sp - 16]
  | .pop _, s => [s.sp + 32]
  | .alloc bytes, s => [s.sp - BitVec.ofNat 64 bytes]
  | _, _ => []

/-- Book I §3.3.10 "Compare Logical Immediate" (`cmplwi` is `cmpli BF, 0,
RA, UI` and `cmpldi` is `cmpli BF, 1, RA, UI`): with `UI = 0`, `CR0`'s EQ bit
is set iff `(RA)32:63` (`L = 0`), or `(RA)` (`L = 1`), is zero; §2.4 "Branch
Conditional" (`beq cr0, …` is `bc 12, 2, …` and `bne cr0, …` is `bc 4, 2,
…`): the branch is taken iff that bit is set (`beq`) or clear (`bne`). -/
def eval : Cond → State → Option Bool
  | .zero sz r, s => some (s.read sz r == 0)
  | .nonzero sz r, s => some (s.read sz r != 0)

/-- Book I §2.4, "Branch" (`bl target` is `b` with `LK = 1`): `LR ← CIA +
4` (the address of the next instruction), then the branch, possibly
through linkage code, which may change `r0`, `r11` and `r12` (ELFv2 ABI
§2.2.2.1, "Optional Function Linkage"). The return address and the values
left in `r0`, `r11` and `r12` are the next four of the state's. -/
def call (s : State) : Option State :=
  some { s with
    lr := s.unknowns 0
    gpr := fun r =>
      if r = .r0 then s.unknowns 1 else if r = .r11 then s.unknowns 2
      else if r = .r12 then s.unknowns 3 else s.gpr r
    unknowns := fun n => s.unknowns (n + 4) }

/-- Book I §2.4, "Branch Conditional to Link Register" (`blr` is `bclr 20,
0`: branch always, `NIA ← LR0:61 || 0b00`). It returns after the call
instruction if `LR` is the return address the call left (`s₁`); otherwise
the model faults. -/
def ret (s₁ s₂ : State) : Option State :=
  if s₂.lr = s₁.lr then some s₂ else none

/-- The push of a frame: Book I §3.3.3, "Store Doubleword with Update"
(`stdu r1, -48(r1)`: `EA ← (RA) + EXTS(DS || 0b00)`, `MEM(EA, 8) ← (RS)`,
`RA ← EA`, so the stack pointer moves down by 48 and the old stack pointer,
the back chain, is stored at the new one), then "Store Doubleword" (`std
RS, 32(r1)`). The frame is the minimum frame of the ELFv2 ABI (§2.2.3.1:
32 bytes, the back chain, the CR save word, a reserved word, the LR save
doubleword and the TOC pointer doubleword) followed by 16 bytes of local
variable space, which holds the register (and 8 bytes it does not write)
and becomes a writable region, at the head of `wr`. Faults if the frame
would wrap around the address space (`sp < 48`).

`alloc bytes` is "Store Doubleword with Update" alone (`stdu r1,
-bytes(r1)`, its `DS` field `-bytes / 4`): it stores the back chain at the
new stack pointer, and the `bytes - 32` bytes above the header become a
writable region, at the head of `wr`, which it does not write: like the 8
bytes of `push`'s local variable space that it does not write, they hold
what memory held there before, below the stack pointer, where the contract
says nothing of them (`Abi.reserved`). Faults unless `bytes` is a multiple
of 16 with `32 < bytes < 4096`, or if the frame would wrap around the
address space (`sp < bytes`). -/
def push : Instr → State → Option State
  | .push r, s =>
    if 48 ≤ s.sp.toNat then
      let sp := s.sp - 48
      some { s with sp := sp, mem := (s.mem.write sp 8 s.sp).write (sp + 32) 8 (s.gpr r),
                    wr := ⟨sp + 32, 16⟩ :: s.wr }
    else none
  | .alloc bytes, s =>
    if 32 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0 ∧ bytes ≤ s.sp.toNat then
      let sp := s.sp - BitVec.ofNat 64 bytes
      some { s with sp := sp, mem := s.mem.write sp 8 s.sp, wr := ⟨sp + 32, bytes - 32⟩ :: s.wr }
    else none
  | _, _ => none

/-- The pop of a frame: Book I §3.3.2, "Load Doubleword" (`ld RT, 32(r1)`:
`RT ← MEM((r1) + 32, 8)`), then "Add Immediate" (`addi r1, r1, 48`). Faults
unless the stack pointer and the writable regions are those the push left
(`s₁`), whose head is the frame's local variable space; it removes that
region. `free bytes` is "Add Immediate" alone (`addi r1, r1, bytes`: `RT ←
(RA) + EXTS(SI)`), likewise for the frame of `alloc bytes`. -/
def pop : Instr → State → State → Option State
  | .pop r, s₁, s₂ =>
    if s₂.sp = s₁.sp ∧ s₂.wr = s₁.wr ∧ s₁.wr.head? = some ⟨s₁.sp + 32, 16⟩ then
      some { s₂.write r (s₂.mem.read (s₂.sp + 32) 8) with sp := s₂.sp + 48, wr := s₂.wr.tail }
    else none
  | .free bytes, s₁, s₂ =>
    if 32 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0 ∧
        s₂.sp = s₁.sp ∧ s₂.wr = s₁.wr ∧ s₁.wr.head? = some ⟨s₁.sp + 32, bytes - 32⟩ then
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
  -- Every modelled instruction is in Power ISA 2.07 (POWER8), the baseline of
  -- `powerpc64le-unknown-linux-gnu`.
  requires _ := []

end VG.PPCWideProbe


/-!
# Printer for the 64-bit little-endian PowerPC model

**Trusted.** Emits the GNU/LLVM assembler syntax used by Rust's
`asm!`/`naked_asm!` on PowerPC, with registers written `%rN` (and `%cr0`)
so that they cannot be read as numbers. The rotates and shifts are printed
as the base instructions (`rlwinm`, `rldicl`, `rldicr`) whose operands the
model's semantics describes, not as extended mnemonics.
-/

@[expose] public section

namespace VG.PPCWideProbe

def Reg.index : Reg → Nat
  | .r0 => 0 | .r2 => 2 | .r3 => 3 | .r4 => 4 | .r5 => 5 | .r6 => 6 | .r7 => 7 | .r8 => 8
  | .r9 => 9 | .r10 => 10 | .r11 => 11 | .r12 => 12 | .r14 => 14 | .r15 => 15 | .r16 => 16
  | .r17 => 17 | .r18 => 18 | .r19 => 19 | .r20 => 20 | .r21 => 21 | .r22 => 22 | .r23 => 23
  | .r24 => 24 | .r25 => 25 | .r26 => 26 | .r27 => 27 | .r28 => 28 | .r29 => 29 | .r30 => 30
  | .r31 => 31

/-- `%r<n>`. -/
def Reg.name (r : Reg) : String := s!"%r{r.index}"

def LogicOp.name : LogicOp → String
  | .and => "and" | .or => "or" | .xor => "xor"

/-- A 16-bit immediate, as an unsigned number. -/
def imm16 (v : BitVec 16) : String := toString v.toNat

/-- VMX operands use VR numbers; VSX operands use the aliased VSR number. -/
def VReg.name (r : VReg) : String := s!"%v{r.ctorIdx}"
def VReg.vsx (r : VReg) : String := toString (r.ctorIdx + 32)

def VOp.asm : VOp → String
  | .cipher inv last d n m =>
    let op := if inv then "vncipher" else "vcipher"
    s!"{op}{if last then "last" else ""} {d.name}, {n.name}, {m.name}"
  | .sbox d n => s!"vsbox {d.name}, {n.name}"
  | .sha256 d n st six => s!"vshasigmaw {d.name}, {n.name}, {st.toNat}, {six}"
  | .sha512 d n st six => s!"vshasigmad {d.name}, {n.name}, {st.toNat}, {six}"
  | .pmsumd d n m => s!"vpmsumd {d.name}, {n.name}, {m.name}"
  | .logic op d n m =>
    let op := match op with | .and => "vand" | .or => "vor" | .xor => "vxor"
    s!"{op} {d.name}, {n.name}, {m.name}"
  | .sel d n m mask => s!"vsel {d.name}, {n.name}, {m.name}, {mask.name}"
  | .add dw d n m => s!"{if dw then "vaddudm" else "vadduwm"} {d.name}, {n.name}, {m.name}"
  | .perm d n m c => s!"vperm {d.name}, {n.name}, {m.name}, {c.name}"
  | .sldoi d n m sh => s!"vsldoi {d.name}, {n.name}, {m.name}, {sh}"

def Instr.asm : Instr → List String
  | .vop op => [op.asm]
  | .lxvd2x d a b | .lxvd2xTbl d a b .. => [s!"lxvd2x {d.vsx}, {a.name}, {b.name}"]
  | .stxvd2x n a b => [s!"stxvd2x {n.vsx}, {a.name}, {b.name}"]
  | .mtvsrd d n => [s!"mtvsrd {d.vsx}, {n.name}"]
  | .mfvsrd d n => [s!"mfvsrd {d.name}, {n.vsx}"]
  | .add d n m => [s!"add {d.name}, {n.name}, {m.name}"]
  | .sub d n m => [s!"subf {d.name}, {m.name}, {n.name}"]
  | .mul d n m => [s!"mulld {d.name}, {n.name}, {m.name}"]
  | .mulhu d n m => [s!"mulhdu {d.name}, {n.name}, {m.name}"]
  | .addc d n m => [s!"addc {d.name}, {n.name}, {m.name}"]
  | .adde d n m => [s!"adde {d.name}, {n.name}, {m.name}"]
  | .addze d n => [s!"addze {d.name}, {n.name}"]
  | .subc d n m => [s!"subfc {d.name}, {m.name}, {n.name}"]
  | .sube d n m => [s!"subfe {d.name}, {m.name}, {n.name}"]
  | .addi d n imm => [s!"addi {d.name}, {n.name}, {imm}"]
  | .subi d n imm => [s!"addi {d.name}, {n.name}, -{imm}"]
  | .li d imm => [s!"li {d.name}, {imm}"]
  -- `lis` takes a signed immediate: print the 16 bits as one.
  | .lis d imm => [s!"lis {d.name}, {imm.toInt}"]
  | .ori d n imm => [s!"ori {d.name}, {n.name}, {imm16 imm}"]
  | .oris d n imm => [s!"oris {d.name}, {n.name}, {imm16 imm}"]
  | .logic op d n m => [s!"{op.name} {d.name}, {n.name}, {m.name}"]
  | .rotr .w d n sh => [s!"rlwinm {d.name}, {n.name}, {(32 - sh) % 32}, 0, 31"]
  | .rotr .d d n sh => [s!"rldicl {d.name}, {n.name}, {(64 - sh) % 64}, 0"]
  | .lsr .w d n sh => [s!"rlwinm {d.name}, {n.name}, {(32 - sh) % 32}, {sh}, 31"]
  | .lsr .d d n sh => [s!"rldicl {d.name}, {n.name}, {(64 - sh) % 64}, {sh}"]
  | .lsl d n sh => [s!"rldicr {d.name}, {n.name}, {sh}, {63 - sh}"]
  | .load .w t n off => [s!"lwz {t.name}, {off}({n.name})"]
  | .load .d t n off => [s!"ld {t.name}, {off}({n.name})"]
  | .store .w t n off => [s!"stw {t.name}, {off}({n.name})"]
  | .store .d t n off => [s!"std {t.name}, {off}({n.name})"]
  | .lbz t n off => [s!"lbz {t.name}, {off}({n.name})"]
  | .stb t n off => [s!"stb {t.name}, {off}({n.name})"]
  | .loadRev .w t a b => [s!"lwbrx {t.name}, {a.name}, {b.name}"]
  | .loadRev .d t a b => [s!"ldbrx {t.name}, {a.name}, {b.name}"]
  | .storeRev .w t a b => [s!"stwbrx {t.name}, {a.name}, {b.name}"]
  | .storeRev .d t a b => [s!"stdbrx {t.name}, {a.name}, {b.name}"]
  | .mflr d => [s!"mflr {d.name}"]
  | .mtlr r => [s!"mtlr {r.name}"]
  | .adrSym d name => ["bcl 20, 31, 2f", "2:", s!"mflr {d.name}",
      s!"addis {d.name}, {d.name}, ({name} - 2b)@ha", s!"addi {d.name}, {d.name}, ({name} - 2b)@l"]
  | .push r => ["stdu %r1, -48(%r1)", s!"std {r.name}, 32(%r1)"]
  | .pop r => [s!"ld {r.name}, 32(%r1)", "addi %r1, %r1, 48"]
  | .alloc bytes => [s!"stdu %r1, -{bytes}(%r1)"]
  | .free bytes => [s!"addi %r1, %r1, {bytes}"]
  | .addSp d imm => [s!"addi {d.name}, %r1, {imm}"]

/-- The comparison with zero of a condition. -/
def Cond.cmp : Cond → String
  | .zero .w r | .nonzero .w r => s!"cmplwi %cr0, {r.name}, 0"
  | .zero .d r | .nonzero .d r => s!"cmpldi %cr0, {r.name}, 0"

def Cond.branch : Cond → String
  | .zero .. => "beq"
  | .nonzero .. => "bne"

def printer : Printer isa where
  instr := Instr.asm
  branch c l := [c.cmp, s!"{c.branch} %cr0, {l}"]
  jump l := s!"b {l}"
  ret := ["blr"]
  call := "bl"
  -- Label 2 is private to `adrSym`, the `mflr` after its `bcl`: structured
  -- control flow uses 20, 21, …; repeated sequences use the nearest 2b.
  symLines
    | .adrSym d name => some [.text "bcl 20, 31, 2f", .text "2:", .text s!"mflr {d.name}",
        .sym s!"addis {d.name}, {d.name}, (" .ppcHa name, .sym s!"addi {d.name}, {d.name}, (" .ppcLo name]
    | _ => none

  tables
    | .lxvd2xTbl _ _ _ name ws => [(name, ws)]
    | _ => []

end VG.PPCWideProbe


/-! # PPCWideProbe vector setup helpers -/

@[expose] public section
namespace VG.Impl.Vector.PPCWideProbe
open VG.PPCWideProbe

def const64 (d : Reg) (x : BitVec 64) : List Instr :=
  [.lis d (x.extractLsb' 48 16), .ori d d (x.extractLsb' 32 16), .lsl d d 32,
   .oris d d (x.extractLsb' 16 16), .ori d d (x.extractLsb' 0 16)]

/-- With `zero = 0`, form both halves without retaining either undefined
half produced by `mtvsrd`. The three vector registers must be distinct. -/
def pair (d tmp zero : VReg) (hi lo : Reg) : List Instr :=
  [.mtvsrd d hi, .mtvsrd tmp lo, .vop (.sldoi d zero d 8), .vop (.sldoi d d tmp 8)]


/-- A vector load followed by a byte permutation. `r0` must contain zero. -/
def loadPerm (d : VReg) (p : Reg) (control : VReg) : List Instr :=
  [.lxvd2x d p .r0, .vop (.perm d d d control)]

end VG.Impl.Vector.PPCWideProbe


/-! # POWER8 AES

Eight independent blocks share each loaded round key. The middle rounds
run in a loop, then `vcipherlast` or `vncipherlast` performs the final
round. A one-block loop handles the tail. All registers are volatile and
the scratch argument is unused.
-/

@[expose] public section
namespace VG.Impl.Aes.PPCWideProbe.Crypto
open VG.PPCWideProbe

abbrev key : VReg := .v8
abbrev data : VReg := .v9
abbrev mask : VReg := .v19
abbrev counterBase : VReg := .v10
abbrev counterWord : VReg := .v11
abbrev counterMask : VReg := .v18

def byteMask : BitVec 128 := 0x07060504030201000f0e0d0c0b0a0908

def mov (d n : Reg) : Instr := .logic .or d n n

def counterControl : BitVec 128 := 0x000102030405060708090a0b14151617

def setMask (d : VReg) (x : BitVec 128) : List Instr :=
  Impl.Vector.PPCWideProbe.const64 .r11 (x.extractLsb' 64 64) ++
  Impl.Vector.PPCWideProbe.const64 .r12 (x.extractLsb' 0 64) ++
  Impl.Vector.PPCWideProbe.pair d .v1 .v0 .r11 .r12

def setup : List Instr :=
  [.li .r0 0, .vop (.logic .xor .v0 .v0 .v0)] ++ setMask mask byteMask

/-- Register byte zero is memory byte zero, as the AES instructions require. -/
def load (v : VReg) (p : Reg) : List Instr :=
  Impl.Vector.PPCWideProbe.loadPerm v p mask

def store (v : VReg) (p : Reg) : List Instr :=
  [.vop (.perm v v v mask), .stxvd2x v p .r0]

def xorKey (rs : List VReg) : List Instr := rs.map fun v => .vop (.logic .xor v v key)

def round (inverse last : Bool) (rs : List VReg) : List Instr :=
  load key .r9 ++ rs.map fun v => .vop (.cipher inverse last v v key)

def keyStep (inverse : Bool) : Instr :=
  if inverse then .subi .r9 .r9 16 else .addi .r9 .r9 16

def keyStart (inverse : Bool) : List Instr :=
  if inverse then [.lsl .r9 .r4 4, .add .r9 .r3 .r9] else [mov .r9 .r3]

def middleBody (inverse : Bool) (rs : List VReg) : List Instr :=
  round inverse false rs ++ [keyStep inverse, .subi .r10 .r10 1]

def initialBody (inverse : Bool) (rs : List VReg) : List Instr :=
  keyStart inverse ++ load key .r9 ++ xorKey rs ++ [keyStep inverse, .subi .r10 .r4 1]

/-- AES on the state registers, with the forward schedule at `r3`, `Nr` in
`r4`, and the byte-order mask already in `mask`. -/
def aes (inverse : Bool) (rs : List VReg) : Prog isa :=
  .seq (.block (initialBody inverse rs))
    (.seq (.loop (.block (middleBody inverse rs)) (.nonzero .d .r10))
      (.block (round inverse true rs)))

/-- The same eight registers are used by encryption, decryption and CTR. -/
def breg : Nat → VReg
  | 0 => .v0 | 1 => .v1 | 2 => .v2 | 3 => .v3
  | 4 => .v4 | 5 => .v5 | 6 => .v6 | _ => .v7

def batchRegs (n : Nat) : List VReg := (List.range n).map breg

def regs : List VReg := batchRegs 8

/-- Insert the low 32 bits of the integer counter into the original
counter prefix. `vperm` selects only defined bytes of `mtvsrd`. -/
def counter (v : VReg) : List Instr :=
  [.mtvsrd counterWord .r8, .vop (.perm v counterBase counterWord counterMask), .addi .r8 .r8 1]

/-- The data pointer is advanced here; CTR's counter pointer stays fixed. -/
def readBlock (ctr : Bool) (v : VReg) : List Instr :=
  if ctr then counter v else load v .r6 ++ [.addi .r6 .r6 16]

def storeAdvance (v : VReg) : List Instr := store v .r6 ++ [.addi .r6 .r6 16]

def writeBlock (ctr : Bool) (v : VReg) : List Instr :=
  (if ctr then load data .r6 ++ [.vop (.logic .xor v v data)] else []) ++ storeAdvance v

def group (inverse ctr : Bool) (count : Nat) : Prog isa :=
  let rs := batchRegs count
  .seq (.block (rs.flatMap (readBlock ctr) ++
      (if ctr then [] else [.subi .r6 .r6 (16 * rs.length)])))
    (.seq (aes inverse rs)
      (.block (rs.flatMap (writeBlock ctr) ++ [.subi .r7 .r7 rs.length])))

def batches (inverse ctr : Bool) : Prog isa :=
  .seq (.block [.lsr .d .r12 .r7 3])
    (.seq (.ite (.zero .d .r12) (.block [])
        (.loop (.seq (group inverse ctr 8) (.block [.lsr .d .r12 .r7 3])) (.nonzero .d .r12)))
      (.ite (.zero .d .r7) (.block []) (.loop (group inverse ctr 1) (.nonzero .d .r7))))

def blocks (inverse : Bool) : Prog isa :=
  .ite (.zero .d .r6) (.block [])
    (.seq (.block ([mov .r7 .r6, mov .r6 .r5] ++ setup)) (batches inverse false))

def encryptBlocks : Prog isa := blocks false

def decryptBlocks : Prog isa := blocks true

def ctr32 : Prog isa :=
  .ite (.zero .d .r7) (.block [])
    (.seq (.block (setup ++ setMask counterMask counterControl ++
      [.li .r11 12, .loadRev .w .r8 .r5 .r11] ++ load counterBase .r5))
      (.seq (batches false true) (.block [.storeRev .w .r8 .r5 .r11])))

end VG.Impl.Aes.PPCWideProbe.Crypto
open VG VG.PPCWideProbe
open VG.Impl.Aes.PPCWideProbe.Crypto
namespace WideFolded
abbrev Y : VReg := .v10
abbrev U : VReg := .v17
abbrev T : VReg := .v18
abbrev LO : VReg := .v14
abbrev MID : VReg := .v15
abbrev HI : VReg := .v16

def reg : Nat → VReg
 | 0 => .v0 | 1 => .v1 | 2 => .v2 | 3 => .v3
 | 4 => .v4 | 5 => .v5 | 6 => .v6 | 7 => .v7
 | 8 => .v20 | 9 => .v21 | 10 => .v22 | 11 => .v23
 | 12 => .v24 | 13 => .v25 | 14 => .v26 | 15 => .v27
 | 16 => .v13 | 17 => .v29 | 18 => .v30 | _ => .v31

def rs (n : Nat) := (List.range n).map reg

def reduce (d zero poly : VReg) : List Instr :=
 [.vop (.sldoi T LO zero 8), .vop (.pmsumd T T poly),
  .vop (.sldoi LO LO LO 8), .vop (.logic .xor MID MID LO), .vop (.logic .xor MID MID T),
  .vop (.sldoi T MID zero 8), .vop (.pmsumd T T poly),
  .vop (.sldoi HI HI HI 8), .vop (.logic .xor HI HI MID),
  .vop (.sldoi T T T 8), .vop (.logic .xor d HI T)]

def mul (d a key zero poly : VReg) : List Instr :=
 [.vop (.sldoi U a zero 8), .vop (.pmsumd HI U key),
  .vop (.sldoi U zero a 8), .vop (.pmsumd LO U key), .vop (.pmsumd MID a key)] ++ reduce d zero poly

def saved : List (Reg × Nat) :=
 [(.r14,0),(.r15,8),(.r16,16),(.r18,24),(.r19,32),(.r20,40),
  (.r21,48),(.r22,56),(.r23,64),(.r24,72),(.r25,80)]

def foldSetup : List Instr :=
 [.li .r11 80, .lxvd2x .v11 .r16 .r11, .vop (.logic .or .v12 .v11 .v11),
  .li .r11 1152, .stxvd2x .v11 .r16 .r11] ++
 (List.range 9).flatMap (fun i =>
  [.vop (.sldoi .v9 .v12 .v12 8)] ++ mul .v12 .v9 .v11 .v0 .v13 ++
  [.vop (.sldoi .v12 .v12 .v12 8), .li .r11 (1152+16*(i+1)), .stxvd2x .v12 .r16 .r11]) ++
 (List.range 5).flatMap (fun j =>
  [.li .r11 (1152+16*(9-2*j)), .lxvd2x .v11 .r16 .r11,
   .li .r11 (1152+16*(8-2*j)), .lxvd2x .v12 .r16 .r11,
   .vop (.sldoi .v9 .v12 .v12 8), .vop (.sldoi T .v9 .v11 8),
   .vop (.sldoi T T T 8), .vop (.sldoi .v11 .v11 .v9 8),
   .li .r11 (128+32*j), .stxvd2x .v11 .r16 .r11,
   .li .r11 (144+32*j), .stxvd2x T .r16 .r11])

def entry : List Instr := saved.map (fun (r,o) => .store .d r .r10 o) ++
 [mov .r16 .r10, .addi .r16 .r16 128, mov .r14 .r9, mov .r15 .r6] ++ (List.range 12).flatMap (fun i => [.li .r11 (832+16*i), .stxvd2x ([VReg.v20,.v21,.v22,.v23,.v24,.v25,.v26,.v27,.v28,.v29,.v30,.v31][i]!) .r16 .r11]) ++ setup ++
 [.li .r20 16, .li .r21 48, .li .r22 64, .li .r23 32, .addi .r24 .r16 384,
  .li .r25 96, .stxvd2x .v0 .r16 .r0, .stxvd2x .v19 .r16 .r25] ++
 setMask U 1 ++ [.stxvd2x U .r16 .r20] ++
 setMask .v13 (Impl.Gcm.Clmul.poly ++ Impl.Gcm.Clmul.poly) ++
 [.stxvd2x .v13 .r16 .r23] ++
 setMask .v11 (Impl.Gcm.Clmul.xInv2Hi ++ 3#64) ++ load .v9 .r8 ++
 [.vop (.sldoi .v9 .v9 .v9 8)] ++ mul .v11 .v9 .v11 .v0 .v13 ++
 [.vop (.sldoi .v11 .v11 .v11 8), .li .r11 80, .stxvd2x .v11 .r16 .r11,
  .vop (.sldoi .v9 .v11 .v11 8)] ++ mul .v12 .v9 .v11 .v0 .v13 ++
 [.vop (.sldoi .v12 .v12 .v12 8), .vop (.sldoi .v9 .v11 .v11 8),
  .vop (.sldoi T .v9 .v12 8), .vop (.sldoi T T T 8),
  .vop (.sldoi .v11 .v12 .v9 8), .vop (.logic .or .v12 T T),
  .stxvd2x .v11 .r16 .r21, .stxvd2x .v12 .r16 .r22] ++ load Y .r14 ++
 [.loadRev .d .r18 .r5 .r0, .li .r11 8, .loadRev .w .r19 .r5 .r11, .lsl .r19 .r19 32,
  .li .r11 12, .loadRev .w .r8 .r5 .r11,
  mov .r9 .r3] ++ foldSetup ++ [mov .r11 .r24, .addi .r12 .r4 1]

def cache : Prog isa := .seq (.loop (.block (load .v8 .r9 ++
 [.stxvd2x .v8 .r11 .r0, .addi .r9 .r9 16, .addi .r11 .r11 16, .subi .r12 .r12 1]))
 (.nonzero .d .r12)) (.block [mov .r3 .r24])

def counters (n : Nat) : List Instr :=
 [.lsl .r11 .r8 32, .lsr .d .r11 .r11 32, .logic .or .r11 .r19 .r11,
  .lxvd2x U .r16 .r0] ++ Impl.Vector.PPCWideProbe.pair .v9 T U .r18 .r11 ++
 [.lxvd2x U .r16 .r20, .vop (.add false T U U),
  .vop (.logic .or .v0 .v9 .v9), .vop (.add false .v1 .v9 U)] ++
 (List.range (n-2)).map (fun i => .vop (.add false (reg (i+2)) (reg i) T)) ++ [.addi .r8 .r8 n]

def initial (n : Nat) : List Instr := keyStart false ++ [.lxvd2x .v8 .r9 .r0] ++
 (rs n).map (fun r => .vop (.logic .xor r r .v8)) ++ [keyStep false] ++ [.subi .r10 .r4 1]
def roundRaw (n : Nat) (last : Bool) : List Instr := [.lxvd2x .v8 .r9 .r0] ++
 (rs n).map (fun r => .vop (.cipher false last r r .v8))
def middle (n : Nat) : List Instr := roundRaw n false ++ [keyStep false] ++ [.subi .r10 .r10 1]

def ghPair (first last : Bool) : List Instr := [.lxvd2x .v9 .r16 .r25] ++
 Impl.Vector.PPCWideProbe.loadPerm LO .r15 .v9 ++
 (if first then [.vop (.logic .xor LO LO Y)] else []) ++ [.addi .r15 .r15 16] ++
 Impl.Vector.PPCWideProbe.loadPerm HI .r15 .v9 ++
 [.addi .r15 .r15 16, .lxvd2x .v19 .r16 .r21, .lxvd2x .v28 .r16 .r22,
  .addi .r21 .r21 32, .addi .r22 .r22 32,
  .vop (.sldoi HI HI HI 8), .vop (.sldoi T LO HI 8),
  .vop (.sldoi U HI LO 8), .vop (.sldoi U U U 8),
  .vop (.pmsumd HI U .v28), .vop (.pmsumd LO T .v19),
  .vop (.pmsumd MID U .v19), .vop (.pmsumd U T .v28), .vop (.logic .xor MID MID U)] ++
 (if first then
  [.vop (.logic .or Y LO LO), .vop (.logic .or .v11 MID MID), .vop (.logic .or .v12 HI HI)]
 else if last then
  [.vop (.logic .xor LO LO Y), .vop (.logic .xor MID MID .v11), .vop (.logic .xor HI HI .v12), .lxvd2x .v9 .r16 .r23, .lxvd2x U .r16 .r0] ++ reduce Y U .v9 ++ [.vop (.sldoi Y Y Y 8)]
 else [.vop (.logic .xor Y Y LO), .vop (.logic .xor .v11 .v11 MID), .vop (.logic .xor .v12 .v12 HI)])

def stores (n : Nat) : List Instr := [.lxvd2x .v8 .r16 .r25] ++ (rs n).flatMap (fun r =>
 Impl.Vector.PPCWideProbe.loadPerm .v9 .r6 .v8 ++
 [.vop (.logic .xor r r .v9), .vop (.perm r r r .v8), .stxvd2x r .r6 .r0, .addi .r6 .r6 16]) ++
 [.subi .r7 .r7 n]

def prime (n : Nat) : Prog isa := .seq (.block (counters n ++ initial n))
 (.seq (.loop (.block (middle n)) (.nonzero .d .r10)) (.block (roundRaw n true ++ stores n)))

def interleave : List Instr → List Instr → List Instr
 | [], ys => ys
 | xs, [] => xs
 | x::y::xs, z::zs => x::y::z::interleave xs zs
 | [x], z::zs => x::z::zs

def stitchedPair (first last : Bool) : List Instr := [.lxvd2x .v8 .r9 .r0] ++
 interleave (ghPair first last) ((rs 20).map (fun r => .vop (.cipher false false r r .v8))) ++
 [keyStep false, .subi .r10 .r10 1]

def ghStart : List Instr := [.li .r21 128, .li .r22 144]
def foldedRounds (last : Bool) : Prog isa := .seq (.block (ghStart ++ stitchedPair true false ++ [.li .r12 3]))
 (.seq (.loop (.block (stitchedPair false false ++ [.subi .r12 .r12 1])) (.nonzero .d .r12))
 (if last then .ite (.zero .d .r10) (.block (ghPair false true)) (.block (stitchedPair false true))
  else .block (stitchedPair false true)))
def piped : Prog isa := .seq (.block (counters 20 ++ initial 20))
 (.seq (foldedRounds false) (.seq (foldedRounds true)
 (.seq (.ite (.zero .d .r10) (.block []) (.loop (.block (middle 20)) (.nonzero .d .r10)))
 (.block (roundRaw 20 true ++ stores 20)))))
def drainOne : Prog isa := .seq (.block (ghStart ++ ghPair true false ++ [.li .r12 3]))
 (.seq (.loop (.block (ghPair false false ++ [.subi .r12 .r12 1])) (.nonzero .d .r12))
 (.block (ghPair false true)))
def drain : Prog isa := .seq drainOne drainOne

def exit : List Instr := [.li .r11 12, .storeRev .w .r8 .r5 .r11, .lxvd2x .v8 .r16 .r25,
 .vop (.perm Y Y Y .v8), .stxvd2x Y .r14 .r0] ++
 (List.range 12).flatMap (fun i => [.li .r11 (832+16*i), .lxvd2x ([VReg.v20,.v21,.v22,.v23,.v24,.v25,.v26,.v27,.v28,.v29,.v30,.v31][i]!) .r16 .r11]) ++ [.subi .r12 .r16 128] ++
 saved.map (fun (r,o) => .load .d r .r12 o)

def code : Prog isa := .ite (.zero .d .r7) (.block [])
 (.seq (.block entry) (.seq cache (.seq (prime 20)
 (.seq (.ite (.zero .d .r7) (.block []) (.loop piped (.nonzero .d .r7)))
 (.seq drain (.block exit))))))
end WideFolded

def nonvolatile : List VReg := [.v20,.v21,.v22,.v23,.v24,.v25,.v26,.v27,.v28,.v29,.v30,.v31]

def abiCheck : Prog isa :=
 .seq (.block ([.store .d .r31 .r10 3392, .mflr .r0, .store .d .r0 .r10 3400, mov .r31 .r10] ++
  (List.range 12).flatMap (fun i => [.li .r11 (3072+16*i), .stxvd2x nonvolatile[i]! .r31 .r11,
   .li .r11 (2560+16*i), .lxvd2x nonvolatile[i]! .r31 .r11])))
 (.seq (.call "gcm_stitched20" WideFolded.code)
 (.block ((List.range 12).flatMap (fun i => [.li .r11 (2816+16*i), .stxvd2x nonvolatile[i]! .r31 .r11,
  .li .r11 (3072+16*i), .lxvd2x nonvolatile[i]! .r31 .r11]) ++
 [.load .d .r0 .r31 3400, .mtlr .r0, mov .r12 .r31, .load .d .r31 .r12 3392])))

def main : IO Unit := do
 let mut asm := ".text\n.abiversion 2\n"
 for (name, code) in [("gcm_stitched20",WideFolded.code),("gcm_stitched20_abi",abiCheck)] do
  asm := asm ++ s!".globl {name}\n.type {name},@function\n{name}:\n"
  for line in printer.function code do
   match line with
   | .text x => asm := asm ++ x ++ "\n"
   | .call name => asm := asm ++ printer.call ++ " " ++ name ++ "\n"
   | _ => throw (IO.userError "unexpected symbol")
 IO.FS.writeFile "/workspace/scratch/gcm-stitched20.s" asm
