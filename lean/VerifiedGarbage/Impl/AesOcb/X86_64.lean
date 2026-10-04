import VerifiedGarbage.Impl.Aes.X86_64.Callee

/-!
# AES-OCB: x86-64 implementation

`vg_aes_ocb_init`, `vg_aes_ocb_seal` and `vg_aes_ocb_open`
(`Spec/Ocb/Contract.lean`), composed of calls of the verified
`vg_aes_expand_key`, `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`,
and generic over their implementations (`Callees`): each function is
emitted once for each.

* `init` expands the key into the key context and enciphers a zero block in
  place, at byte 240, for `L_*`.
* The whole blocks of the data are processed in three passes over the data,
  in place: XOR each block with its offset `Offset_i` (and, for `seal`, add
  it to the checksum), encipher or decipher all of them in one call, then
  XOR each with its offset again (and, for `open`, add it to the
  checksum). The offsets are recomputed in the third pass, from `Offset_0`.
* `L_{ntz(i)}` is `L_0` doubled `ntz(i)` times, computed for each block by
  a loop on the public `i`; `L_$` and `L_0` are `L_*` doubled once and
  twice.
* `HASH(K, A)` copies up to 8 blocks of the associated data at a time,
  each XORed with its offset, to `W + bufO`, and enciphers them there.
* `Offset_0` takes the bits `bottom … bottom + 127` of `Stretch` (§4.2),
  where `bottom` is the last 6 bits of the nonce, which is secret: the
  192-bit `Stretch`, in three registers, is shifted left by 1, 2, 4, 8, 16
  and 32 bits, each shift kept or not by a mask from a bit of `bottom`.
* `open` compares the tags without a branch and masks the data with
  `0 − ok`.

## The working space `W` (`work`, 2560 bytes)

`[0, 16)`: the tag (out of `seal`; the received one, for `open`); then the
offset, the checksum, the sum of `HASH`, `L_$`, `L_0`, the current
`L_{ntz(i)}`, a block for one call, the computed tag of `open`, the offset
of `HASH`, the callee-saved registers, the public arguments, `bottom`,
`Offset_0`, `Stretch`; `[384, 512)`: 8 blocks of the associated data;
`[512, 2560)`: the working space of the functions called.

`r15` holds `W` and `r14` the key context throughout; the functions called
preserve them, and `rbx`, `rbp`, `r12` and `r13`, which hold pointers and
counts across calls. Only the pointers, the lengths, `rounds` and
`tag_len` (and for `open`, whether the tag is right) affect timing.
-/

namespace VG.Impl.AesOcb.X86_64

open VG.X86_64

/-- The implementations called: AES's encryption and decryption of whole
blocks and its key expansion. -/
structure Callees where
  enc : Impl.Aes.X86_64.Blocks
  dec : Impl.Aes.X86_64.Blocks
  key : Impl.Aes.X86_64.ExpandKey

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }
def ld (r b : Reg) (d : Nat) : Instr := .mov r (.mem (at_ b d))
def st (b : Reg) (d : Nat) (r : Reg) : Instr := .store (at_ b d) r
def mvr (d s : Reg) : Instr := .mov d (.reg s)
def addi (r : Reg) (k : Nat) : Instr := .alu .add r (.imm (BitVec.ofNat 32 k))

/-! ## The working space -/

def tagO : Nat := 0
def ofsO : Nat := 16
def ckO : Nat := 32
def sumO : Nat := 48
def ldO : Nat := 64
def l0O : Nat := 80
def lO : Nat := 96
def tmpO : Nat := 112
def t2O : Nat := 128
def ohO : Nat := 144
def savO : Nat := 160
def dataO : Nat := 208
def lenO : Nat := 216
def tlO : Nat := 224
def rndO : Nat := 232
def aadO : Nat := 240
def alenO : Nat := 248
def botO : Nat := 256
def o0O : Nat := 272
def nO : Nat := 288
def nlO : Nat := 296
def bufO : Nat := 384
def scrO : Nat := 512

/-- The callee-saved registers, and where they are kept. -/
def saved : List (Reg × Nat) :=
  [(.rbx, savO), (.rbp, savO + 8), (.r12, savO + 16), (.r13, savO + 24), (.r14, savO + 32),
   (.r15, savO + 40)]

def save (b : Reg) : List Instr := saved.map fun (r, d) => st b d r
def restore : List Instr := saved.map fun (r, d) => ld r .r15 d

/-! ## Blocks of `W` -/

/-- `W + d ← 0` (16 bytes). -/
def zero16 (d : Nat) : List Instr :=
  [.alu .xor .rax (.reg .rax), st .r15 d .rax, st .r15 (d + 8) .rax]

/-- `W + d ← W + s`. -/
def copy16 (s d : Nat) : List Instr :=
  [ld .rax .r15 s, ld .rdx .r15 (s + 8), st .r15 d .rax, st .r15 (d + 8) .rdx]

/-- `W + d ← W + d ⊕ (b + s)`. -/
def xor16 (b : Reg) (s d : Nat) : List Instr :=
  [ld .rax .r15 d, ld .rdx .r15 (d + 8), .alu .xor .rax (.mem (at_ b s)),
   .alu .xor .rdx (.mem (at_ b (s + 8))), st .r15 d .rax, st .r15 (d + 8) .rdx]

/-- `W + d ← double(W + s)` (§2): the block is big-endian, so each half is
byte-reversed into `rax` (high) and `rdx` (low), shifted left by one bit,
the carry out of the high half reducing the low one by `{87}` through a
mask, and byte-reversed back. -/
def dbl (b : Reg) (s d : Nat) : List Instr :=
  [ld .rax b s, .bswap .rax, ld .rdx b (s + 8), .bswap .rdx,
   mvr .rcx .rax, .shift .shr .rcx 63, .alu .xor .r8 (.reg .r8), .alu .sub .r8 (.reg .rcx),
   .alu .and .r8 (.imm 0x87),
   mvr .rcx .rdx, .shift .shr .rcx 63, .alu .add .rax (.reg .rax), .alu .or .rax (.reg .rcx),
   .alu .add .rdx (.reg .rdx), .alu .xor .rdx (.reg .r8),
   .bswap .rax, st .r15 d .rax, .bswap .rdx, st .r15 (d + 8) .rdx]

/-- `W + lO ← L_{ntz(i)}` for `i ≥ 1` in `rbp`: `L_0` doubled while the
low bit of `r11` (from `i`, shifted right each time) is zero. -/
def lNtz : Prog isa :=
  .seq (.block (copy16 l0O lO ++ [mvr .r11 .rbp, .alu .test .r11 (.imm 1)]))
    (.ite .e (.loop (.block (dbl .r15 lO lO ++ [.shift .shr .r11 1, .alu .test .r11 (.imm 1)])) .e)
      (.block []))

/-! ## Calls -/

/-- `ENCIPHER` (`c.enc`) or `DECIPHER` (`c.dec`) of the `rcx` blocks at `rdx`
(set up by `args`), with the key context's schedule and the working space
at `W + scrO`. -/
def callBlocks (f : Impl.Aes.X86_64.Blocks) (args : List Instr) : Prog isa :=
  .seq (.block (args ++ [mvr .rdi .r14, ld .rsi .r15 rndO, mvr .r8 .r15, addi .r8 scrO]))
    (.call f.name f.code)

/-- One block of `W`, at `W + d`. -/
def oneBlock (d : Nat) : List Instr := [mvr .rdx .r15, addi .rdx d, .mov .rcx (.imm 1)]

/-! ## `L_$`, `L_0` and `Offset_0` -/

/-- `L_$` and `L_0` from `L_*` (bytes 240–255 of the key context). -/
def lsetup : List Instr := dbl .r14 240 ldO ++ dbl .r15 ldO l0O

/-- The `r12` bytes at `rbx` copied to `rsi`, from `rcx = 0` (`r12 > 0`). -/
def copyLoop : Prog isa :=
  .loop (.block [.movzx8 .rax { base := .rbx, index := some .rcx },
    .store8 { base := .rsi, index := some .rcx } .rax, addi .rcx 1, .alu .cmp .rcx (.reg .r12)]) .ne

/-- `W + d ← pad(S)` (§4.1), `S` the `r12` bytes at `rbx` (`0 < r12 < 16`):
zeros, the bytes copied, and `0x80` after them. -/
def padTo (d : Nat) : Prog isa :=
  .seq (.block (zero16 d ++ [mvr .rsi .r15, addi .rsi d, .alu .xor .rcx (.reg .rcx)]))
    (.seq copyLoop (.block [.mov .rax (.imm 0x80), .store8 { base := .rsi, index := some .rcx } .rax]))

/-- The nonce block (§4.2), `num2str(TAGLEN mod 128, 7) ‖ zeros ‖ 1 ‖ N`, at
`W + tmpO`, with `nonce`, `nonce_len` and `tag_len` in `W + nO`, `W + nlO`
and `W + tlO`: zeros, the nonce's bytes copied to the end of the block, the
1 in the byte before them, and `TAGLEN`'s bits in the top of the first
byte. Then `bottom` (its last 6 bits) to `W + botO`, and those bits
cleared. -/
def nonceBlock : Prog isa :=
  .seq (.block (zero16 tmpO ++ [ld .rbx .r15 nO, ld .r12 .r15 nlO, mvr .rsi .r15, addi .rsi (tmpO + 16),
      .alu .sub .rsi (.reg .r12), .alu .xor .rcx (.reg .rcx)]))
    (.seq copyLoop
      (.block [.mov .rax (.imm 1), .store8 { base := .rsi, disp := -1 } .rax,
        ld .rax .r15 tlO, .alu .and .rax (.imm 15), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .movzx8 .rcx (at_ .r15 tmpO), .alu .or .rcx (.reg .rax), .store8 (at_ .r15 tmpO) .rcx,
        .movzx8 .rax (at_ .r15 (tmpO + 15)), mvr .rcx .rax, .alu .and .rcx (.imm 63),
        st .r15 botO .rcx, .alu .and .rax (.imm 0xc0), .store8 (at_ .r15 (tmpO + 15)) .rax]))

/-- One stage of the shift of `Stretch` (in `rax`, `rdx`, `rcx`, high to
low): shifted left by `a` bits if bit `k` of `bottom` (in `rbx`) is set.
`r8`–`r11` are temporaries. -/
def stage (k a : Nat) : List Instr :=
  -- The mask: all ones if bit `k` is set.
  [mvr .r9 .rbx] ++ (if k = 0 then [] else [.shift .shr .r9 k]) ++
  [.alu .and .r9 (.imm 1), .alu .xor .r10 (.reg .r10), .alu .sub .r10 (.reg .r9),
   -- `r11` keeps the bits above the `a` lowest.
   .movImm64 .r11 (BitVec.allOnes 64 <<< a)] ++
  -- Each word, from the high one: `x ← x ⊕ ((x' ⊕ x) ∧ mask)`, where
  -- `x' = (x ⋘ a) ∨ (next ⋙ (64 − a))`.
  ([(Reg.rax, Reg.rdx), (.rdx, .rcx)].flatMap fun (x, y) =>
    [mvr .r8 x, .shift .ror .r8 (64 - a), .alu .and .r8 (.reg .r11),
     mvr .r9 y, .shift .shr .r9 (64 - a), .alu .or .r8 (.reg .r9),
     .alu .xor .r8 (.reg x), .alu .and .r8 (.reg .r10), .alu .xor x (.reg .r8)]) ++
  [mvr .r8 .rcx, .shift .ror .r8 (64 - a), .alu .and .r8 (.reg .r11),
   .alu .xor .r8 (.reg .rcx), .alu .and .r8 (.reg .r10), .alu .xor .rcx (.reg .r8)]

/-- `Offset_0` from `Ktop` at `W + tmpO` and `bottom` at `W + botO`, to
`W + ofsO` and `W + o0O`: `Stretch = Ktop ‖ (Ktop[1..64] ⊕ Ktop[9..72])`
in `rax`, `rdx`, `rcx`, shifted left by `bottom`, of which the high 128
bits. -/
def offset0 : List Instr :=
  [ld .rax .r15 tmpO, .bswap .rax, ld .rdx .r15 (tmpO + 8), .bswap .rdx,
   mvr .rcx .rax, .shift .ror .rcx 56, .movImm64 .r8 (BitVec.allOnes 64 <<< 8),
   .alu .and .rcx (.reg .r8), mvr .r8 .rdx, .shift .shr .r8 56, .alu .or .rcx (.reg .r8),
   .alu .xor .rcx (.reg .rax), ld .rbx .r15 botO] ++
  stage 0 1 ++ stage 1 2 ++ stage 2 4 ++ stage 3 8 ++ stage 4 16 ++ stage 5 32 ++
  [.bswap .rax, st .r15 ofsO .rax, st .r15 o0O .rax, .bswap .rdx, st .r15 (ofsO + 8) .rdx,
   st .r15 (o0O + 8) .rdx]

variable (c : Callees)

/-- `Offset_0`. -/
def nonce : Prog isa :=
  .seq nonceBlock (.seq (callBlocks c.enc (oneBlock tmpO)) (.block offset0))

/-! ## `HASH` -/

/-- One block of the associated data (at `rbx`) XORed with its offset to
`W + bufO + 16 j` (`j` in `r13`, counting up), `i` in `rbp`. -/
def hashFill : Prog isa :=
  .seq lNtz
    (.block (xor16 .r15 lO ohO ++
      [ld .rax .rbx 0, ld .rdx .rbx 8, .alu .xor .rax (.mem (at_ .r15 ohO)),
       .alu .xor .rdx (.mem (at_ .r15 (ohO + 8))),
       mvr .rcx .r13, .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
       .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .r15),
       st .rcx bufO .rax, st .rcx (bufO + 8) .rdx,
       addi .rbx 16, addi .rbp 1, addi .r13 1, .alu .cmp .r13 (.reg .r12)]))

/-- Add the `r12` blocks at `W + bufO` to the sum. -/
def hashSum : Prog isa :=
  .seq (.block [.alu .xor .r13 (.reg .r13)])
    (.loop (.block (
      [mvr .rcx .r13, .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
       .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .r15)] ++
      xor16 .rcx bufO sumO ++ [addi .r13 1, .alu .cmp .r13 (.reg .r12)])) .ne)

/-- A chunk of up to 8 blocks: `r12 ← min(8, blocks left)`, fill, encipher,
add; then on to the next (ZF set when none are left). The blocks left are
in `W + alenO` (as blocks, while hashing). -/
def hashChunk : Prog isa :=
  .seq (.block [ld .r12 .r15 alenO, .alu .cmp .r12 (.imm 8)])
    (.seq (.ite .b (.block []) (.block [.mov .r12 (.imm 8)]))
      (.seq (.block [.alu .xor .r13 (.reg .r13)])
        (.seq (.loop (hashFill) .ne)
          (.seq (callBlocks c.enc [mvr .rdx .r15, addi .rdx bufO, mvr .rcx .r12])
            (.seq hashSum
              (.block [ld .rax .r15 alenO, .alu .sub .rax (.reg .r12), st .r15 alenO .rax]))))))

/-- The rest of the associated data (`r12` bytes at `rbx`), padded, XORed
with the offset `⊕ L_*`, enciphered and added to the sum. -/
def hashRest : Prog isa :=
  .seq (.block (xor16 .r14 240 ohO))
    (.seq (padTo bufO)
      (.seq (.block (xor16 .r15 ohO bufO))
        (.seq (callBlocks c.enc (oneBlock bufO)) (.block (xor16 .r15 bufO sumO)))))

/-- `HASH(K, A)` to `W + sumO`, with `aad` and `aad_len` in `W + aadO` and
`W + alenO`. -/
def hash : Prog isa :=
  .seq (.block (zero16 sumO ++ zero16 ohO ++
      [ld .rbx .r15 aadO, ld .rax .r15 alenO, mvr .rcx .rax, .alu .and .rcx (.imm 15),
       st .r15 tmpO .rcx, .shift .shr .rax 4, st .r15 alenO .rax, .mov .rbp (.imm 1),
       .alu .test .rax (.reg .rax)]))
    (.seq (.ite .e (.block []) (.loop (hashChunk c) .ne))
      (.seq (.block [ld .r12 .r15 tmpO, .alu .test .r12 (.reg .r12)])
        (.ite .e (.block []) (hashRest c))))

/-! ## The whole blocks -/

/-- The offset of block `i` (in `rbp`): `Offset ← Offset ⊕ L_{ntz(i)}`. -/
def nextOffset : Prog isa := .seq lNtz (.block (xor16 .r15 lO ofsO))

/-- `W + ckO ⊕= (rbx)`. -/
def addCk : List Instr := xor16 .rbx 0 ckO

/-- `(rbx) ⊕= W + ofsO`. -/
def xorOfs : List Instr :=
  [ld .rax .rbx 0, ld .rdx .rbx 8, .alu .xor .rax (.mem (at_ .r15 ofsO)),
   .alu .xor .rdx (.mem (at_ .r15 (ofsO + 8))), st .rbx 0 .rax, st .rbx 8 .rdx]

/-- On to the next block (ZF set when none are left). -/
def nextBlock : List Instr := [addi .rbx 16, addi .rbp 1, .alu .sub .r12 (.imm 1)]

/-- A pass over the `r12` whole blocks of the data at `rbx` (`r12 > 0`),
with `i` from 1 in `rbp`: each block through `body` after its offset. -/
def pass (body : List Instr) : Prog isa :=
  .loop (.seq nextOffset (.block (body ++ nextBlock))) .ne

/-- The whole blocks: `pre` (the first pass), `f` on all of them, `post` (the
third pass, the offsets recomputed from `Offset_0`); `rbx` the data, `r13`
their number. -/
def whole (f : Impl.Aes.X86_64.Blocks) (pre post : List Instr) : Prog isa :=
  .seq (.block [ld .rbx .r15 dataO, mvr .r12 .r13, .mov .rbp (.imm 1)])
    (.seq (pass pre)
      (.seq (callBlocks f [ld .rdx .r15 dataO, mvr .rcx .r13])
        (.seq (.block (copy16 o0O ofsO ++ [ld .rbx .r15 dataO, mvr .r12 .r13, .mov .rbp (.imm 1)]))
          (pass post))))

/-! ## The rest of the data and the tag -/

/-- `W + t2O ← pad(P_*)`, `P_*` the `r12` bytes at `rbx` (`0 < r12 < 16`),
and add it to the checksum. -/
def padCk : Prog isa := .seq (padTo t2O) (.block (xor16 .r15 t2O ckO))

/-- The `r12` bytes at `rbx` XORed with `Pad` at `W + tmpO`. -/
def xorPad : Prog isa :=
  .seq (.block [.alu .xor .rcx (.reg .rcx)])
    (.loop (.block [.movzx8 .rax { base := .rbx, index := some .rcx },
        .movzx8 .rdx { base := .r15, index := some .rcx, disp := tmpO }, .alu .xor .rax (.reg .rdx),
        .store8 { base := .rbx, index := some .rcx } .rax, addi .rcx 1,
        .alu .cmp .rcx (.reg .r12)]) .ne)

/-- The rest of the data (`r12` bytes at `rbx`, `r12 > 0`): `Offset_* =
Offset ⊕ L_*`, `Pad = ENCIPHER(K, Offset_*)`; for `seal` (`enc`) the checksum
of the plaintext, then the XOR; for `open`, the XOR, then the checksum. -/
def rest (enc : Bool) : Prog isa :=
  .seq (.block (xor16 .r14 240 ofsO ++ copy16 ofsO tmpO))
    (.seq (callBlocks c.enc (oneBlock tmpO))
      (if enc then .seq (padCk) (xorPad) else .seq (xorPad) (padCk)))

/-- The tag, `ENCIPHER(K, Checksum ⊕ Offset ⊕ L_$) ⊕ HASH(K, A)`, to `W + d`. -/
def tag (d : Nat) : Prog isa :=
  .seq (.block (copy16 ckO tmpO ++ xor16 .r15 ofsO tmpO ++ xor16 .r15 ldO tmpO))
    (.seq (callBlocks c.enc (oneBlock tmpO))
      (.block (copy16 tmpO d ++ xor16 .r15 sumO d)))

/-! ## The functions -/

/-- The entry of `seal` and `open`: `W` from the stack, the callee-saved
registers saved, the arguments kept in `W`, `L_$` and `L_0`, the checksum
zeroed. -/
def entry : List Instr :=
  [.mov .rax (.mem (at_ .rsp 24))] ++ save .rax ++
  [mvr .r15 .rax, mvr .r14 .rdi, st .r15 rndO .rsi, st .r15 nO .rdx, st .r15 nlO .rcx,
   st .r15 aadO .r8, st .r15 alenO .r9,
   ld .rax .rsp 8, st .r15 dataO .rax, ld .rax .rsp 16, st .r15 lenO .rax, ld .rax .rsp 32,
   st .r15 tlO .rax] ++ lsetup ++ zero16 ckO

/-- The data: whole blocks, then the rest. -/
def body (enc : Bool) : Prog isa :=
  .seq (.block [ld .r13 .r15 lenO, .shift .shr .r13 4, .alu .test .r13 (.reg .r13)])
    (.seq (.ite .e (.block [])
        (if enc then whole c.enc (addCk ++ xorOfs) xorOfs else whole c.dec xorOfs (xorOfs ++ addCk)))
      (.seq (.block [ld .rbx .r15 dataO, ld .rax .r15 lenO, mvr .r12 .rax, .alu .and .r12 (.imm 15),
          .alu .sub .rax (.reg .r12), .alu .add .rbx (.reg .rax), .alu .test .r12 (.reg .r12)])
        (.ite .e (.block []) (rest c enc))))

def «seal» : Prog isa :=
  .seq (.block entry)
    (.seq (nonce c)
      (.seq (hash c) (.seq (body c true) (.seq (tag c tagO) (.block restore)))))

/-- `open`'s comparison of the first `tag_len` bytes of the tags (at `W` and
`W + t2O`), without a branch: `eax ← 1` if they are equal, else 0. -/
def cmp : Prog isa :=
  .seq (.block [.alu .xor .rdx (.reg .rdx), .alu .xor .rcx (.reg .rcx), ld .r12 .r15 tlO])
    (.seq (.loop (.block [.movzx8 .rax { base := .r15, index := some .rcx },
        .movzx8 .r8 { base := .r15, index := some .rcx, disp := t2O }, .alu .xor .rax (.reg .r8),
        .alu .or .rdx (.reg .rax), addi .rcx 1, .alu .cmp .rcx (.reg .r12)]) .ne)
      (.block [.alu .sub .rdx (.imm 1), .shift .shr .rdx 63, st .r15 tagO .rdx]))

/-- The data (`len` bytes) masked with `0 − ok`, `ok` at `W + tagO`. -/
def mask : Prog isa :=
  .seq (.block [ld .rbx .r15 dataO, ld .r12 .r15 lenO, .alu .xor .rdx (.reg .rdx),
      .alu .sub .rdx (.mem (at_ .r15 tagO)), .alu .xor .rcx (.reg .rcx), .alu .test .r12 (.reg .r12)])
    (.ite .e (.block [])
      (.loop (.block [.movzx8 .rax { base := .rbx, index := some .rcx }, .alu .and .rax (.reg .rdx),
        .store8 { base := .rbx, index := some .rcx } .rax, addi .rcx 1,
        .alu .cmp .rcx (.reg .r12)]) .ne))

def «open» : Prog isa :=
  .seq (.block entry)
    (.seq (nonce c)
      (.seq (hash c) (.seq (body c false) (.seq (tag c t2O)
        (.seq cmp (.seq mask (.block ([ld .rax .r15 tagO] ++ restore))))))))

/-! ## The key setup -/

/-- `vg_aes_ocb_init(key = rdi, key_len = rsi, ctx = rdx, scratch = rcx)`:
the callee-saved registers it uses saved in `scratch`, the key expanded into
the key context (with the working space at `scratch + scrO`), then a zero
block at byte 240 enciphered in place, for `L_*`. -/
def init : Prog isa :=
  .seq (.block ([st .rcx 0 .rbx, st .rcx 8 .rbp, st .rcx 16 .r12, mvr .rbx .rdx, mvr .rbp .rsi,
      .shift .shr .rbp 2, addi .rbp 6, mvr .r12 .rcx, addi .rcx scrO]))
    (.seq (.call c.key.name c.key.code)
      (.seq (.block [.alu .xor .rax (.reg .rax), st .rbx 240 .rax, st .rbx 248 .rax,
          mvr .rdi .rbx, mvr .rsi .rbp, mvr .rdx .rbx, addi .rdx 240, .mov .rcx (.imm 1),
          mvr .r8 .r12, addi .r8 scrO])
        (.seq (.call c.enc.name c.enc.code)
          (.block [ld .rbx .r12 0, ld .rbp .r12 8, ld .r12 .r12 16]))))

end VG.Impl.AesOcb.X86_64
