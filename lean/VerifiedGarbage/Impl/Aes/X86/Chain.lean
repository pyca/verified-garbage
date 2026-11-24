module

public import VerifiedGarbage.Impl.Aes.X86.Vperm

/-!
# AES, one block after another, with the keys set up once (x86, 32-bit)

The serial modes (AES-CBC's encryption, AES-CMAC, AES-CFB128's encryption and
AES-OFB) encipher each block only after the one before, so that each of their
blocks would be a call of `vg_aes_encrypt_blocks` of its own, with its setup.
A `Chain` is an implementation of AES that those modes run in place instead,
with no call: its setup once for all the blocks (`prep`), then the cipher of
the block in `xmm0` (`core`), which stays there from one block to the next.

Its functions' arguments are the modes' stack arguments: `schedule`, `rounds`,
the chaining value's address, `data`, `n` and `scratch`. `prep` may change any
register but `esp`, and the first `written` bytes of `scratch`; `core` keeps
`esi`, `ebp` and `esp`, and what `prep` left for it (its `Ready` in
`Proof/Aes/X86/Chain.lean`), which is kept by changes of `esi`, `ebp`, `edx`,
`xmm0`, `xmm1` and the flags, and of the memory but `scratch`'s first
`written` bytes, the schedule and the arguments 0 and 1.

`mid` is the code of a mode around it, with the mode's own instructions before
and after the cipher of each block (`Mode`): the next block's address is in
`esi`, the blocks left are in `ebp` and the chaining value is in `xmm0`, and
`xmm1` is the mode's.
-/

@[expose] public section

namespace VG.Impl.Aes.X86

open VG.X86
open VG.Impl.Aes.X86.AesNi (at_ argOp)

/-- An implementation of AES for a chain of blocks. -/
structure Chain where
  /-- The setup, once. -/
  prep : Prog isa
  /-- The block in `xmm0` enciphered. -/
  core : Prog isa
  /-- How many bytes of the scratch buffer they write, from its start. -/
  written : Nat

namespace Chain

/-- AES-NI: the schedule in `eax` and the rounds in `ecx`, and the round keys
loaded from the schedule, through `xmm6`. -/
def aesNi : Chain :=
  { prep := .block [.mov .eax (.mem (argOp 0)), .mov .ecx (.mem (argOp 1))]
    core := AesNi.aes [.xmm0]
    written := 0 }

/-- SSSE3: vector permutations (`Vperm.lean`), with the tables and the round
keys in the scratch buffer. The setup saves no register there: the modes have
saved them. -/
def ssse3 : Chain :=
  { prep := .seq (.block ((Vperm.Enc.dir false).setup 5)) (Vperm.Enc.dir false).prep
    core := (Vperm.Enc.dir false).core
    written := 480 }

/-- The functions, of whole blocks and counter mode, by AES-NI. -/
def isAesNi (name : String) : Bool := name == "vg_aes_encrypt_blocks_aesni" || name == "vg_aes_ctr32_to_aesni"

/-- The functions, of whole blocks and counter mode, by SSSE3. -/
def isSsse3 (name : String) : Bool := name == "vg_aes_encrypt_blocks_ssse3" || name == "vg_aes_ctr32_to_ssse3"

/-- The chain that the modes run in place of calls of the function `name`, if
it has one. -/
def of (name : String) : Option Chain :=
  if isAesNi name then some aesNi else if isSsse3 name then some ssse3 else none

/-- A mode's code over the function `name`: around its chain if it has one,
otherwise `calls`. -/
def choose (name : String) (chain : Chain → Prog isa) (calls : Prog isa) : Prog isa :=
  if isAesNi name then chain aesNi else if isSsse3 name then chain ssse3 else calls

/-- What a mode does with a block, at `esi`, before and after the cipher. -/
structure Mode where
  pre : List Instr
  post : List Instr

/-- The block loaded into `xmm1`. -/
def loadBlock : Instr := .movdquLoad .xmm1 (at_ .esi 0)

/-- `xmm0` stored over the block. -/
def storeBlock : Instr := .movdquStore (at_ .esi 0) .xmm0

/-- The block XORed into the chaining value (`xmm0`), through `xmm1`. -/
def xorIn : List Instr := [loadBlock, .xop (.bin .pxor .xmm0 .xmm1)]

/-- AES-CBC's encryption: the block XORed into the chaining value, which is
enciphered and stored over the block. -/
def cbc : Mode := { pre := xorIn, post := [storeBlock] }

/-- AES-CMAC: the block XORed into the chaining value, which is enciphered. -/
def cmac : Mode := { pre := xorIn, post := [] }

/-- AES-CFB128's encryption: the chaining value enciphered, the block XORed
into it, and it stored over the block. -/
def cfb : Mode := { pre := [], post := xorIn ++ [storeBlock] }

/-- AES-OFB: the chaining value enciphered, and XORed into the block. -/
def ofb : Mode :=
  { pre := [], post := [loadBlock, .xop (.bin .pxor .xmm1 .xmm0), .movdquStore (at_ .esi 0) .xmm1] }

/-- The data's address, the number of blocks and the chaining value. -/
def load : List Instr :=
  [.mov .esi (.mem (argOp 3)), .mov .ebp (.mem (argOp 4)), .mov .edx (.mem (argOp 2)),
    .movdquLoad .xmm0 (at_ .edx 0)]

/-- On to the next block; ZF is set when none is left. -/
def next : List Instr := [.alu .add .esi (.imm 16), .alu .sub .ebp (.imm 1)]

/-- The chaining value stored. -/
def store : List Instr := [.mov .edx (.mem (argOp 2)), .movdquStore (at_ .edx 0) .xmm0]

variable (c : Chain)

/-- One block. -/
def body (m : Mode) : Prog isa := .seq (.block m.pre) (.seq c.core (.block (m.post ++ next)))

/-- The blocks, of which there is at least one, with the registers saved. -/
def mid (m : Mode) : Prog isa :=
  .seq c.prep (.seq (.block load) (.seq (.loop (c.body m) .ne) (.block store)))

end Chain

end VG.Impl.Aes.X86
