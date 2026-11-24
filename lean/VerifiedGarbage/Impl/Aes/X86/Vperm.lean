module

public import VerifiedGarbage.Impl.Aes.Vperm
public import VerifiedGarbage.Impl.Aes.X86.AesNi

/-!
# AES by vector permutations (SSSE3) on x86 (32-bit)

`vg_aes_encrypt_blocks_ssse3`, `vg_aes_decrypt_blocks_ssse3` and
`vg_aes_ctr32_to_ssse3`, with the arguments of the implementations in the
baseline ISA (`Blocks.lean`, `Ctr32.lean`): a block at a time, the S-box
computed with `pshufb` of sixteen-byte tables by four-bit indices, whose time
does not depend on its data, so that no secret is an address or a branch
condition. `pshufb` gives 0 for an index whose high bit is set.

How the tables give the S-box is in `AArch64/Vperm.lean`, whose `tbl` is
`pshufb` here: a byte `x` of the state is held as `L x`, in decryption as
`D x`, its nibbles `i` and `k`, the elements `io` and `jo` of the subfield
(`invert`, into `xmm2` and `xmm5`), and the round's linear layer in the
tables they select from (`Enc.mix`, `Dec.mix`).

The tables live in the scratch buffer at `edi`, vector `k` at bytes `16 k` to
`16 k + 15`: each call stores them there from immediates (`storeWords`), since
a static's address would take stack, which the functions' callers do not set
aside; those that are shuffles of others are computed (`derive`). The round
keys follow them (`slots`): through `L` for encryption, whose last one is
XORed with `0x63` in every byte; for decryption from the last key down, the
middle ones through InvMixColumns and `D` (`prep`). `core` then runs the
rounds on the block in `xmm0`, in registers: `ebx` steps over the keys and
`ecx` counts the rounds. It changes only `ebx`, `ecx` and `xmm0`–`xmm5`;
`xmm6` holds the table of `1 / ·` and `xmm7` the mask `0x0f` of every byte.

Every address is `esp` or a pointer plus a constant, or computed from the
pointers and `rounds`, and every branch depends only on those and `n`, so
only the pointers, `rounds` and `n` can affect timing.
-/

@[expose] public section

namespace VG.Impl.Aes.X86.Vperm

open VG.X86 VG.Impl.Aes.Vperm
open VG.Impl.Aes.X86.AesNi (at_ argOp)

def mv (d s : XReg) : Instr := .xop (.bin .movdqa d s)
def px (d s : XReg) : Instr := .xop (.bin .pxor d s)
def sb (d s : XReg) : Instr := .xop (.bin .pshufb d s)

/-- Vector `k` of the scratch buffer into `r`. -/
def tl (r : XReg) (k : Nat) : Instr := .movdquLoad r (at_ .edi (16 * k))

/-- `r`, its low doubleword copied to every one. -/
def splat (r : XReg) (v : BitVec 32) : List Instr :=
  [.mov .eax (.imm v), .xop (.movd r .eax), .xop (.pshufd r r 0)]

/-! ## The tables -/

/-- The words of vectors. -/
def words (l : List (BitVec 128)) : List (BitVec 32) :=
  l.flatMap fun v => (List.range 4).map fun i => v.extractLsb' (32 * i) 32

/-- `ws` stored at bytes `o` on of the scratch buffer. -/
def storeWords : Nat → List (BitVec 32) → List Instr
  | _, [] => []
  | o, w :: ws => .mov .eax (.imm w) :: .store (at_ .edi o) .eax :: storeWords (o + 4) ws

/-! ## The inversion -/

/-- The low four bits of `d`'s bytes into `d`, the high four into `t`. -/
def nibbles (d t : XReg) : List Instr :=
  [mv t d, .xop (.shift .psrld t 4), .xop (.bin .pand t .xmm7), .xop (.bin .pand d .xmm7)]

/-- `io` and `jo` of the bytes of `xmm0`, into `xmm2` and `xmm5`, with vector
`a` the table of `a / ·`. -/
def invert (a : Nat) : List Instr :=
  nibbles .xmm0 .xmm1 ++
    [tl .xmm2 a, sb .xmm2 .xmm0, px .xmm0 .xmm1, mv .xmm3 .xmm6, sb .xmm3 .xmm1, mv .xmm4 .xmm6, sb .xmm4 .xmm0,
      px .xmm3 .xmm2, px .xmm4 .xmm2, mv .xmm2 .xmm6, sb .xmm2 .xmm3, mv .xmm5 .xmm6, sb .xmm5 .xmm4,
      px .xmm2 .xmm0, px .xmm5 .xmm1]

/-! ## A direction -/

/-- What encryption and decryption differ in. -/
structure Dir where
  /-- The tables stored from immediates: vectors `0` on. -/
  tabs : List (BitVec 128)
  /-- The tables computed from them, and `xmm6` and `xmm7`. -/
  derive : List Instr
  /-- Where the round keys' slots start, after the tables. -/
  slots : Nat
  /-- The slots from the schedule (argument 0) and the rounds (argument 1). -/
  prep : Prog isa
  /-- The vector of `a / ·`. -/
  inva : Nat
  /-- The block and the first slot's key, as the state. -/
  first : List Instr
  /-- The rest of a full round after `invert`, with the slot at `ebx`. -/
  mix : List Instr
  /-- The rest of the last round after `invert`, with the slot at `ebx`. -/
  last : List Instr

namespace Dir

variable (d : Dir)

/-- Where the callee-saved registers are kept, after the slots. -/
def saved : Nat := d.slots + 240

/-- The callee-saved registers, and their offsets in the scratch buffer. -/
def savedRegs : List (Reg × Nat) :=
  [(.ebx, d.saved), (.esi, d.saved + 4), (.ebp, d.saved + 8), (.edi, d.saved + 12)]

/-- `ebx` to slot 1, and the rounds but one into `ecx`. -/
def start : List Instr :=
  [.mov .ebx (.reg .edi), .alu .add .ebx (.imm (BitVec.ofNat 32 (d.slots + 16))), .mov .ecx (.mem (argOp 1)),
    .alu .sub .ecx (.imm 1)]

/-- A full round. -/
def round : List Instr :=
  invert d.inva ++ (d.mix ++ ([.alu .add .ebx (.imm 16), .alu .sub .ecx (.imm 1)] : List Instr))

/-- The block in `xmm0` through the cipher. -/
def core : Prog isa :=
  .seq (.block (d.first ++ d.start))
    (.seq (.loop (.block d.round) .ne) (.block (invert d.inva ++ d.last)))

/-- The scratch buffer (argument `k`) into `edi`, the callee-saved registers
saved there, and the tables. -/
def setup (k : Nat) : List Instr :=
  ([.mov .eax (.mem (argOp k))] : List Instr) ++ d.savedRegs.map (fun p => .store (at_ .eax p.2) p.1) ++
    ([.mov .edi (.reg .eax)] : List Instr) ++ storeWords 0 (words d.tabs) ++ d.derive

/-- The callee-saved registers restored, `edi` last. -/
def restore : List Instr := d.savedRegs.map fun p => .mov p.1 (.mem (at_ .edi p.2))

/-- One block of the data at `esi`, and on to the next (`ZF` is set when
none is left). -/
def body : Prog isa :=
  .seq (.block [.movdquLoad .xmm0 (at_ .esi 0)])
    (.seq d.core (.block [.movdquStore (at_ .esi 0) .xmm0, .alu .add .esi (.imm 16), .alu .sub .ebp (.imm 1)]))

/-- The data pointer and the count, and the count's test. -/
def dataArgs : List Instr :=
  [.mov .esi (.mem (argOp 2)), .mov .ebp (.mem (argOp 3)), .alu .test .ebp (.reg .ebp)]

/-- The functions of whole blocks in place. -/
def blocks : Prog isa :=
  .seq (.block (d.setup 4)) (.seq d.prep (.seq (.block dataArgs)
    (.seq (.ite .e (.block []) (.loop d.body .ne)) (.block d.restore))))

end Dir

/-- `d`, `4 k` bits of `r` further on: `r := 2ᵏ r`. -/
def dbl (r : Reg) (k : Nat) : List Instr := (List.range k).map fun _ => .alu .add r (.reg r)

/-! ## Encryption -/

namespace Enc

/-- Vectors 0 to 11; `rsr` is 12 and `r3sr` 13. -/
def tabs : List (BitVec 128) :=
  [keyLo, keyHi, inv, inva, sr, rot, sb1u, sb1t, sb2u, sb2t, sbou, sbot]

def slots : Nat := 224

def derive : List Instr :=
  splat .xmm7 0x0f0f0f0f ++
    [tl .xmm0 4, tl .xmm1 5, sb .xmm0 .xmm1, .movdquStore (at_ .edi 192) .xmm0, sb .xmm0 .xmm1, sb .xmm0 .xmm1,
      .movdquStore (at_ .edi 208) .xmm0, tl .xmm6 2]

/-- `xmm0 := L xmm0 ⊕ L 0x63`, through `xmm1` and `xmm2`. -/
def keyx : List Instr :=
  nibbles .xmm0 .xmm1 ++ [tl .xmm2 0, sb .xmm2 .xmm0, tl .xmm0 1, sb .xmm0 .xmm1, px .xmm0 .xmm2]

def first : List Instr := keyx ++ [.movdquLoad .xmm1 (at_ .edi slots), px .xmm0 .xmm1]

def mix : List Instr :=
  [tl .xmm0 6, sb .xmm0 .xmm2, tl .xmm1 7, sb .xmm1 .xmm5, px .xmm0 .xmm1,
    tl .xmm3 8, sb .xmm3 .xmm2, tl .xmm4 9, sb .xmm4 .xmm5, px .xmm3 .xmm4,
    tl .xmm1 4, sb .xmm3 .xmm1, mv .xmm4 .xmm0, tl .xmm1 12, sb .xmm4 .xmm1, tl .xmm1 13, sb .xmm0 .xmm1,
    px .xmm3 .xmm4, .movdquLoad .xmm2 (at_ .ebx 0), px .xmm0 .xmm2, px .xmm0 .xmm3, tl .xmm1 5, sb .xmm3 .xmm1,
    px .xmm0 .xmm3]

def last : List Instr :=
  [tl .xmm0 10, sb .xmm0 .xmm2, tl .xmm1 11, sb .xmm1 .xmm5, px .xmm0 .xmm1, tl .xmm1 4, sb .xmm0 .xmm1,
    .movdquLoad .xmm1 (at_ .ebx 0), px .xmm0 .xmm1]

/-- The schedule into `esi`, the rounds into `ecx` and the slots into `ebx`. -/
def prepHead : List Instr :=
  [.mov .esi (.mem (argOp 0)), .mov .ecx (.mem (argOp 1)), .mov .ebx (.reg .edi),
    .alu .add .ebx (.imm (BitVec.ofNat 32 slots))]

/-- A round key through `keyx` to its slot. -/
def prepBody : List Instr :=
  ([.movdquLoad .xmm0 (at_ .esi 0)] : List Instr) ++ keyx ++
    ([.movdquStore (at_ .ebx 0) .xmm0, .alu .add .esi (.imm 16), .alu .add .ebx (.imm 16),
      .alu .sub .ecx (.imm 1)] : List Instr)

/-- The last round key, XORed with `0x63`, to its slot. -/
def prepTail : List Instr :=
  splat .xmm1 0x63636363 ++
    [.movdquLoad .xmm0 (at_ .esi 0), px .xmm0 .xmm1, .movdquStore (at_ .ebx 0) .xmm0]

def prep : Prog isa := .seq (.block prepHead) (.seq (.loop (.block prepBody) .ne) (.block prepTail))

end Enc

def enc : Dir :=
  { tabs := Enc.tabs, derive := Enc.derive, slots := Enc.slots, prep := Enc.prep, inva := 3,
    first := Enc.first, mix := Enc.mix, last := Enc.last }

/-! ## Decryption -/

namespace Dec

open VG.Impl.Aes.Vperm.Dec

/-- Vectors 0 to 23; `rot2` is 24, `rot3` 25, and `p1`, `p2` and `p3` are 26 to 28. -/
def tabs : List (BitVec 128) :=
  [inv, inva, y0l, y0h, y1l, y1h, y2l, y2h, y3l, y3h, rot, x0u, x0t, x1u, x1t, x2u, x2t, x3u, x3t, p0,
    dl, dh, dbou, dbot]

def slots : Nat := 464

def derive : List Instr :=
  splat .xmm7 0x0f0f0f0f ++
    [tl .xmm1 10, mv .xmm0 .xmm1, sb .xmm0 .xmm1, .movdquStore (at_ .edi 384) .xmm0, sb .xmm0 .xmm1,
      .movdquStore (at_ .edi 400) .xmm0, tl .xmm0 19, sb .xmm0 .xmm1, .movdquStore (at_ .edi 416) .xmm0,
      sb .xmm0 .xmm1, .movdquStore (at_ .edi 432) .xmm0, sb .xmm0 .xmm1, .movdquStore (at_ .edi 448) .xmm0,
      tl .xmm6 0]

def first : List Instr :=
  ([.movdquLoad .xmm1 (at_ .edi slots), px .xmm0 .xmm1] : List Instr) ++ nibbles .xmm0 .xmm1 ++
    ([tl .xmm2 20, sb .xmm2 .xmm0, tl .xmm0 21, sb .xmm0 .xmm1, px .xmm0 .xmm2] : List Instr)

/-- Vectors `u` at `io` and `t` at `jo`, XORed and shuffled by vector `p`,
into `d` through `e`. -/
def term (d e : XReg) (u t p : Nat) : List Instr :=
  [tl d u, sb d .xmm2, tl e t, sb e .xmm5, px d e, tl e p, sb d e]

def mix : List Instr :=
  term .xmm0 .xmm1 11 12 19 ++ term .xmm3 .xmm4 13 14 26 ++
    ([px .xmm0 .xmm3, .movdquLoad .xmm1 (at_ .ebx 0), px .xmm0 .xmm1] : List Instr) ++
    term .xmm3 .xmm4 15 16 27 ++ term .xmm1 .xmm4 17 18 28 ++ ([px .xmm3 .xmm1, px .xmm0 .xmm3] : List Instr)

def last : List Instr := term .xmm0 .xmm1 22 23 19 ++ [.movdquLoad .xmm1 (at_ .ebx 0), px .xmm0 .xmm1]

/-- A round key to its slot. -/
def copyKey : List Instr := [.movdquLoad .xmm0 (at_ .esi 0), .movdquStore (at_ .ebx 0) .xmm0]

/-- The last round key's address into `esi`, the rounds but one into `ecx`,
the slots into `ebx`, and the last round key to the first. -/
def prepHead : List Instr :=
  ([.mov .esi (.mem (argOp 0)), .mov .ecx (.mem (argOp 1)), .mov .eax (.reg .ecx)] : List Instr) ++ dbl .eax 4 ++
    ([.alu .add .esi (.reg .eax), .mov .ebx (.reg .edi), .alu .add .ebx (.imm (BitVec.ofNat 32 slots)),
      .alu .sub .ecx (.imm 1)] : List Instr) ++ copyKey

/-- To the round key before and the next slot. -/
def prepStep : List Instr := [.alu .sub .esi (.imm 16), .alu .add .ebx (.imm 16)]

/-- The products of the key (its nibbles in `xmm0` and `xmm1`) by a constant:
vectors `l` and `h`, XORed, into `d` through `xmm3`. -/
def keyTerm (d : XReg) (l h : Nat) : List Instr := [tl d l, sb d .xmm0, tl .xmm3 h, sb .xmm3 .xmm1, px d .xmm3]

/-- `keyTerm` shuffled by vector `r`, XORed into `xmm2`. -/
def keyRot (l h r : Nat) : List Instr :=
  keyTerm .xmm4 l h ++ [tl .xmm3 r, sb .xmm4 .xmm3, px .xmm2 .xmm4]

/-- `D` of InvMixColumns of the key in `xmm0`, into `xmm2`. -/
def key : List Instr :=
  nibbles .xmm0 .xmm1 ++ keyTerm .xmm2 2 3 ++ keyRot 4 5 10 ++ keyRot 6 7 24 ++ keyRot 8 9 25

def prepBody : List Instr :=
  prepStep ++ ([.movdquLoad .xmm0 (at_ .esi 0)] : List Instr) ++ key ++
    ([.movdquStore (at_ .ebx 0) .xmm2, .alu .sub .ecx (.imm 1)] : List Instr)

def prep : Prog isa :=
  .seq (.block prepHead) (.seq (.loop (.block prepBody) .ne) (.block (prepStep ++ copyKey)))

end Dec

def dec : Dir :=
  { tabs := Dec.tabs, derive := Dec.derive, slots := Dec.slots, prep := Dec.prep, inva := 1,
    first := Dec.first, mix := Dec.mix, last := Dec.last }

/-- `vg_aes_encrypt_blocks_ssse3`. -/
def encryptBlocks : Prog isa := enc.blocks

/-- `vg_aes_decrypt_blocks_ssse3`. -/
def decryptBlocks : Prog isa := dec.blocks

/-! ## Counter mode -/

namespace Ctr

/-- Where the first twelve bytes of the counter block are kept, as a vector. -/
def prefixOff : Nat := enc.saved + 16

/-- The counter block's prefix kept, its 32-bit counter in `edx`, the final
counter written back, and the data's pointers and count. -/
def args : List Instr :=
  [.mov .ecx (.mem (argOp 2)), .movdquLoad .xmm0 (at_ .ecx 0), .xop (.shift .pslldq .xmm0 4),
    .xop (.shift .psrldq .xmm0 4), .movdquStore (at_ .edi prefixOff) .xmm0, .mov .edx (.mem (at_ .ecx 12)),
    .bswap .edx, .mov .eax (.reg .edx), .alu .add .eax (.mem (argOp 4)), .bswap .eax, .store (at_ .ecx 12) .eax,
    .mov .esi (.mem (argOp 3)), .mov .eax (.mem (argOp 6)), .mov .ebp (.mem (argOp 4)), .alu .test .ebp (.reg .ebp)]

/-- The counter block, and the counter's increment. -/
def counter : List Instr :=
  [.mov .ecx (.reg .edx), .bswap .ecx, .xop (.movd .xmm0 .ecx), .xop (.shift .pslldq .xmm0 12),
    .movdquLoad .xmm1 (at_ .edi prefixOff), .xop (.bin .por .xmm0 .xmm1), .alu .add .edx (.imm 1)]

/-- The keystream block XORed into a block of the data, and on to the next. -/
def xor : List Instr :=
  [.movdquLoad .xmm1 (at_ .esi 0), px .xmm0 .xmm1, .movdquStore (at_ .eax 0) .xmm0, .alu .add .esi (.imm 16),
    .alu .add .eax (.imm 16), .alu .sub .ebp (.imm 1)]

def body : Prog isa := .seq (.block counter) (.seq enc.core (.block xor))

end Ctr

/-- `vg_aes_ctr32_to_ssse3`. -/
def ctr32To : Prog isa :=
  .seq (.block (enc.setup 5)) (.seq enc.prep (.seq (.block Ctr.args)
    (.seq (.ite .e (.block []) (.loop Ctr.body .ne)) (.block enc.restore))))

end VG.Impl.Aes.X86.Vperm
