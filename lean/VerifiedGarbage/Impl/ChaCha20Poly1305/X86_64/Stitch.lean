module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64
public import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx2

/-!
# ChaCha20-Poly1305: x86-64, with Poly1305 inside the AVX2 ChaCha20 kernel

`seal` (`../X86_64.lean`) encrypts the data with one call of
`vg_chacha20_xor` and then absorbs the ciphertext with calls of
`vg_poly1305_blocks`. The AVX2 kernel (`Impl/ChaCha20/X86_64/Avx2.lean`)
keeps the vector units busy and leaves the integer units, the multiplier and
twelve general-purpose registers idle: `sealStitched` fills them with the
scalar Poly1305 (`Impl/Poly1305/X86_64.lean`), as BoringSSL's
`chacha20_poly1305_x86_64.pl` does with its own kernel. The two
computations are independent, so out-of-order cores overlap them.

With at least 512 bytes of data, `bulk` encrypts its whole chunks of 512
bytes: the first with the kernel's code (`firstChunk`), and each later one
with the kernel's code in which every double round absorbs three or four
blocks of Poly1305 (`chunk`): the 32 blocks of the chunk before it, whose
ciphertext is complete. Each block is absorbed in two pieces, the block
added and its products (`addProd`), then their carry, each after one of the
round's quarter rounds (`sround4`, `sround3`): a whole double round of
vector code and then three or four blocks of scalar code would each leave
the other's units idle for longer than the out-of-order window can cover.
`rsi` points at that chunk while the rounds run, and is advanced to the
chunk being encrypted just before the kernel's `finish` XORs the keystream
into it.

Every register but `rsp` is busy during a chunk: `rdi`, `rsi` and `rcx` are
the kernel's (the ChaCha20 state, the data and `buf`), and the other twelve
are Poly1305's (`r8`–`r10` for the key, `r11`, `rbx`, `rbp` for the
accumulator, the rest for the products). So the number of bytes left lives
in the Poly1305 state's working space (`lenOff`), which `vg_poly1305_blocks`
uses only while it runs, and `r12`–`r14` (`tag`, the length and the data,
which `seal` needs afterwards) are stashed there by `enter`. `leave`
reduces the accumulator, stores it, restores them, and leaves in `rbx`,
`rbp` the ciphertext not yet absorbed (the last chunk and the rest), and
in `rsi`, `rdx` the data not yet encrypted, for the call of
`vg_chacha20_xor` that follows. The branches are on the length only.
-/

@[expose] public section

namespace VG.Impl.ChaCha20Poly1305.X86_64.Stitch

open VG.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)

/-- Offsets in `buf` (`ctx + 128`), in the Poly1305 state's working space
(`ctx + 520 …`): `r12`, `r13`, `r14` stashed, and the bytes left. -/
def r12Off : Nat := 392
def r13Off : Nat := 400
def r14Off : Nat := 408
def lenOff : Nat := 416

/-- The accumulator's offset in `buf`: the Poly1305 state at `ctx + 448`. -/
def accOff : Nat := 320

/-- After double round `n` of a chunk, `blocks n` blocks are absorbed, from
block `firstBlock n` of the 32: four after the first two, three after the
others. -/
def blocks (n : Nat) : Nat := if n < 2 then 4 else 3
def firstBlock (n : Nat) : Nat := if n < 2 then 4 * n else 3 * n + 2

/-- The first piece of block `j` of the 512 bytes at `rsi`: the block added
to the accumulator, and the products of the sum. Its second piece is
`Poly1305.X86_64.carry`. -/
def addProd (j : Nat) : List Instr :=
  Poly1305.X86_64.addBlockAt .rsi (16 * j) 1 ++ Poly1305.X86_64.products

section
open ChaCha20.X86_64.Avx2 (quarter swap)

/-- A double round (`Avx2.doubleRound`) absorbing blocks `j` to `j + 3`, a
piece after each quarter round. -/
def sround4 (j : Nat) : Prog isa :=
  .seq (quarter 0 4 8 12) <| .seq (.block (addProd j)) <|
  .seq (quarter 1 5 9 13) <| .seq (.block Poly1305.X86_64.carry) <| .seq (swap 8 10) <|
  .seq (quarter 2 6 10 14) <| .seq (.block (addProd (j + 1))) <|
  .seq (quarter 3 7 11 15) <| .seq (.block Poly1305.X86_64.carry) <|
  .seq (quarter 0 5 10 15) <| .seq (.block (addProd (j + 2))) <|
  .seq (quarter 1 6 11 12) <| .seq (.block Poly1305.X86_64.carry) <| .seq (swap 10 8) <|
  .seq (quarter 2 7 8 13) <| .seq (.block (addProd (j + 3))) <|
  .seq (quarter 3 4 9 14) (.block Poly1305.X86_64.carry)

/-- A double round absorbing blocks `j` to `j + 2`: a piece after each
quarter round but the first of each half. -/
def sround3 (j : Nat) : Prog isa :=
  .seq (quarter 0 4 8 12) <|
  .seq (quarter 1 5 9 13) <| .seq (.block (addProd j)) <| .seq (swap 8 10) <|
  .seq (quarter 2 6 10 14) <| .seq (.block Poly1305.X86_64.carry) <|
  .seq (quarter 3 7 11 15) <| .seq (.block (addProd (j + 1))) <|
  .seq (quarter 0 5 10 15) <|
  .seq (quarter 1 6 11 12) <| .seq (.block Poly1305.X86_64.carry) <| .seq (swap 10 8) <|
  .seq (quarter 2 7 8 13) <| .seq (.block (addProd (j + 2))) <|
  .seq (quarter 3 4 9 14) (.block Poly1305.X86_64.carry)

end

/-- `n` double rounds, each absorbing its blocks. -/
def srounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (srounds n) (if n < 2 then sround4 (firstBlock n) else sround3 (firstBlock n))

/-- The counter advanced by 8 and 512 bytes fewer left; `CF` is clear if at
least 512 bytes remain. -/
def next : List Instr :=
  [.mov32 .rax (.mem (at_ .rdi 48)), .alu32 .add .rax (.imm 8), .store32 (at_ .rdi 48) .rax,
   .mov .rdx (.mem (at_ .rcx lenOff)), .alu .sub .rdx (.imm 512), .store (at_ .rcx lenOff) .rdx,
   .alu .cmp .rdx (.imm 512)]

/-- The first chunk, the kernel's (`rsi` stays at it), but for `next`. -/
def firstMain : Prog isa :=
  .seq (.block ChaCha20.X86_64.Avx2.setup)
    (.seq (ChaCha20.X86_64.Avx2.rounds 10) (.block ChaCha20.X86_64.Avx2.finish))

def firstChunk : Prog isa := .seq firstMain (.block next)

/-- A later chunk but for `next`: the 512 bytes at `rsi` (the chunk before)
absorbed during the rounds, then the next 512 encrypted. -/
def chunkMain : Prog isa :=
  .seq (.block ChaCha20.X86_64.Avx2.setup)
    (.seq (srounds 10)
      (.block (([.alu .add .rsi (.imm 512)] : List Instr) ++ ChaCha20.X86_64.Avx2.finish)))

def chunk : Prog isa := .seq chunkMain (.block next)

/-- `r12`–`r14` and the length stashed, the kernel's constants stored, and
the key and the accumulator loaded from the Poly1305 state (`ctx + 448`,
through `rdi`, which then points at the ChaCha20 state again). -/
def enter : List Instr :=
  ([.store (at_ .rcx r12Off) .r12, .store (at_ .rcx r13Off) .r13, .store (at_ .rcx r14Off) .r14,
   .store (at_ .rcx lenOff) .rdx] : List Instr) ++ ChaCha20.X86_64.Avx2.consts ++
  ([.mov .rdi (.reg .rcx), .alu .add .rdi (.imm 320)] : List Instr) ++ Poly1305.X86_64.setup ++
  ([.mov .rdi (.reg .rcx), .alu .sub .rdi (.imm 64)] : List Instr)

/-- The accumulator reduced and stored, `r12`–`r14` and `r15` (the context)
restored, `rbx`, `rbp` the ciphertext not yet absorbed and `rsi`, `rdx` the
data not yet encrypted. -/
def leave : List Instr :=
  Poly1305.X86_64.reduce ++
  ([.store (at_ .rcx accOff) .r11, .store (at_ .rcx (accOff + 8)) .rbx,
   .store (at_ .rcx (accOff + 16)) .rbp,
   .mov .rbx (.reg .rsi), .mov .rbp (.mem (at_ .rcx lenOff)), .alu .add .rbp (.imm 512),
   .mov .rdx (.mem (at_ .rcx lenOff)), .alu .add .rsi (.imm 512),
   .mov .r12 (.mem (at_ .rcx r12Off)), .mov .r13 (.mem (at_ .rcx r13Off)),
   .mov .r14 (.mem (at_ .rcx r14Off)), .mov .r15 (.reg .rcx), .alu .sub .r15 (.imm 128)] : List Instr)

/-- The whole chunks of at least 512 bytes of data. -/
def bulk : Prog isa :=
  .seq (.block enter)
  (.seq firstChunk
  (.seq (.ite .b (.block []) (.loop chunk .ae))
    (.block leave)))

/-- The data and the ciphertext to absorb when there are no whole chunks:
all of it. -/
def whole : List Instr := [.mov .rbx (.reg .r14), .mov .rbp (.reg .r13)]

/-- `crypt`, with `rbx`, `rbp` set to the ciphertext not yet absorbed: the
whole chunks are encrypted and absorbed by `bulk`, and the rest encrypted by
the implementation `x` of `vg_chacha20_xor`. -/
def cryptS (x : ChaCha20.X86_64.Callee) : Prog isa :=
  .seq (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 (x.fold + 1)))])
  (.seq (.ite .b
    (.seq (.block (ptr .rsi .r15 736 ++ ([.mov .rdx (.reg .r13)] : List Instr)))
      (.seq (xorBufX .r14) (.block (ptr .rsi .r15 128 ++ whole))))
    (.seq (.block (cryptArgs ++ ([.alu .cmp .rdx (.imm 512)] : List Instr)))
      (.seq (.ite .b (.block whole) bulk) (.call x.name x.code))))
  (.seq (.block (anchor .rsi 128))
  (.seq (foldM x.fold x.pass)
  (.seq (.block [.alu .add .rdx (.imm 64)]) zeroKs))))

/-- `seal`, with Poly1305 inside the kernel for the whole chunks. -/
def sealStitched (x : ChaCha20.X86_64.Callee) (b : Poly1305.X86_64.Blocks) : Prog isa :=
  .seq (.block entry)
  (.seq (prologue x)
  (.seq (macPad b .rbx .rbp)
  (.seq (.block lengths)
  (.seq (cryptS x)
  (.seq (macPadLengths b .rbx .rbp)
  (.seq finalizeTag
    (.block restore)))))))

/-- The `seal` an instance uses: with the AVX2 implementation of
`vg_poly1305_blocks` (whose ChaCha20 is the AVX2 kernel), `sealStitched`;
otherwise `seal`. -/
def sealFor (x : ChaCha20.X86_64.Callee) : Poly1305.X86_64.Blocks → Prog isa
  | .avx2 => sealStitched x .avx2
  | b => «seal» x b

/-! ## `open`

`open` absorbs the ciphertext before it decrypts it, so each chunk absorbs
its own 512 bytes during its rounds, before the kernel's `finish` XORs the
keystream into them: no chunk is special. `bulkO` runs them while at least
512 bytes remain; `leaveO` leaves `rbx`, `rbp` and `rsi`, `rdx` at the rest,
which `cryptO` absorbs (with the lengths block) before the call of
`vg_chacha20_xor` decrypts it. -/

/-- A chunk of `open` but for `next`: the 512 bytes at `rsi` absorbed during
the rounds, then decrypted, and `rsi` advanced past them. -/
def chunkMainO : Prog isa :=
  .seq (.block ChaCha20.X86_64.Avx2.setup)
    (.seq (srounds 10)
      (.block (ChaCha20.X86_64.Avx2.finish ++ ([.alu .add .rsi (.imm 512)] : List Instr))))

def chunkO : Prog isa := .seq chunkMainO (.block next)

/-- As `leave`, with the rest of the data both the ciphertext not yet
absorbed (`rbx`, `rbp`) and the data not yet decrypted (`rsi`, `rdx`). -/
def leaveO : List Instr :=
  Poly1305.X86_64.reduce ++
  [.store (at_ .rcx accOff) .r11, .store (at_ .rcx (accOff + 8)) .rbx,
   .store (at_ .rcx (accOff + 16)) .rbp,
   .mov .rbx (.reg .rsi), .mov .rbp (.mem (at_ .rcx lenOff)), .mov .rdx (.mem (at_ .rcx lenOff)),
   .mov .r12 (.mem (at_ .rcx r12Off)), .mov .r13 (.mem (at_ .rcx r13Off)),
   .mov .r14 (.mem (at_ .rcx r14Off)), .mov .r15 (.reg .rcx), .alu .sub .r15 (.imm 128)]

/-- The whole chunks of at least 512 bytes of data, decrypted and absorbed. -/
def bulkO : Prog isa :=
  .seq (.block enter) (.seq (.loop chunkO .ae) (.block leaveO))

/-- The arguments of the call on the rest of the data (`rbx`, `rbp`), from
the counter the chunks left. -/
def restArgs : List Instr :=
  ptr .rdi .r15 64 ++ [.mov .rsi (.reg .rbx), .mov .rdx (.reg .rbp)] ++ ptr .rcx .r15 128

/-- `open`'s `macPadLengths` and `crypt`: if the data is at most `fold`
bytes, as `open` does; otherwise the whole chunks decrypted and absorbed by
`bulkO`, then the rest absorbed and decrypted. -/
def cryptO (x : ChaCha20.X86_64.Callee) (b : Poly1305.X86_64.Blocks) : Prog isa :=
  .seq (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 (x.fold + 1)))])
  (.seq (.ite .b
    (.seq (macPadLengths b .r14 .r13)
      (.seq (.block (ptr .rsi .r15 736 ++ [.mov .rdx (.reg .r13)]))
        (.seq (xorBufX .r14) (.block (ptr .rsi .r15 128)))))
    (.seq (.block (cryptArgs ++ [.alu .cmp .rdx (.imm 512)]))
      (.seq (.ite .b (.block whole) bulkO)
      (.seq (macPadLengths b .rbx .rbp)
      (.seq (.block restArgs) (.call x.name x.code))))))
  (.seq (.block (anchor .rsi 128))
  (.seq (foldM x.fold x.pass)
  (.seq (.block [.alu .add .rdx (.imm 64)]) zeroKs))))

/-- `open`, with Poly1305 inside the kernel for the whole chunks. -/
def openStitched (x : ChaCha20.X86_64.Callee) (b : Poly1305.X86_64.Blocks) : Prog isa :=
  .seq (.block entry)
  (.seq (prologue x)
  (.seq (macPad b .rbx .rbp)
  (.seq (.block lengths)
  (.seq (cryptO x b)
  (.seq (finalizeTo 48)
    (.block (compare ++ restore)))))))

/-- The `open` an instance uses, as `sealFor`. -/
def openFor (x : ChaCha20.X86_64.Callee) : Poly1305.X86_64.Blocks → Prog isa
  | .avx2 => openStitched x .avx2
  | b => «open» x b

end VG.Impl.ChaCha20Poly1305.X86_64.Stitch
