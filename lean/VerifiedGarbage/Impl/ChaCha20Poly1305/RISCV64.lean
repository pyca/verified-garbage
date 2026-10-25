module

public import VerifiedGarbage.Impl.ChaCha20.RISCV64.Stream
public import VerifiedGarbage.Impl.Poly1305.RISCV64

/-!
# ChaCha20-Poly1305: RISC-V implementation

`vg_chacha20_poly1305_seal(key = a0, nonce = a1, aad = a2, aad_len = a3,
data = a4, len = a5, tag = a6, work = a7)` and `vg_chacha20_poly1305_open`
(the same arguments, returning `a0`), composed of calls of the verified
ChaCha20 and Poly1305 functions. `work` is the working space, which the
artifact's frame allocates on the stack (`withStackScratchWiped`).

The context is `work` rounded up to a multiple of 8, so that the registers
saved there take aligned doubleword accesses:

* `[0, 64)`: the ChaCha20 state;
* `[64, 384)`: the buffer of `vg_chacha20_block` and `vg_chacha20_xor` (the
  first 32 bytes of the block with counter 0 are the one-time Poly1305 key);
* `[384, 512)`: the Poly1305 state;
* `[512, 528)`: zeros, the padding;
* `[528, 544)`: the lengths block;
* `[544, 560)`: the tag computed by `open`;
* `[560, 608)`: our caller's `s7`–`s11` and our return address.

`a0` holds the context, or the Poly1305 state 384 bytes on, and `s7`–`s11`
the additional data, its length, the data, its length and the tag
throughout: no callee writes them, so they keep their values, and the
constant-time analysis sees them public, after every call. The MAC is
computed by `vg_poly1305_update` on the additional data, its padding, the
ciphertext, its padding and the lengths block, and `vg_poly1305_finalize`,
with the message's length so far as `count`.

Constant time: only the pointers and the lengths can affect timing (the
branches are on the lengths, in the callees, and every address is a pointer
plus a constant or a count). `open` compares the tags without a branch.
-/

@[expose] public section

namespace VG.Impl.ChaCha20Poly1305.RISCV64

open VG.RISCV64
open VG.Impl.Words.RISCV64 (copyBytes storeBytes)
open VG.Impl.ChaCha20.RISCV64.Xor (mov)

/-! ## Offsets in the context -/

def bufOff : Nat := 64
def polyOff : Nat := 384
def zeroOff : Nat := 512
def lenOff : Nat := 528
def tagOff : Nat := 544
def savOff : Nat := 560
/-- The size of the working space, in doublewords: the context and the
rounding. -/
def workWords : Nat := 77

/-! ## Entry and exit -/

/-- The context into `t0`, and our caller's `s7`–`s11` and our return
address saved there. -/
def save : List Instr :=
  [.addi .t0 .a7 7, .logicImm .and .t0 .t0 (-8), .store .d .s7 .t0 savOff,
    .store .d .s8 .t0 (savOff + 8), .store .d .s9 .t0 (savOff + 16), .store .d .s10 .t0 (savOff + 24),
    .store .d .s11 .t0 (savOff + 32), .store .d .ra .t0 (savOff + 40)]

/-- The arguments kept, into `s7`–`s11`. -/
def moves : List Instr := [mov .s7 .a2, mov .s8 .a3, mov .s9 .a4, mov .s10 .a5, mov .s11 .a6]

/-- The ChaCha20 state for counter 0 (the constants, the key at `a0`, the
counter and the nonce at `a1`), the padding and the lengths block, at `t0`;
then the context into `a0`. -/
def setup : List Instr :=
  storeBytes .t1 .t0 0 Impl.ChaCha20.RISCV64.Stream.sigmaBytes ++ copyBytes .t1 .a0 .t0 0 16 32 ++
  storeBytes .t1 .t0 48 [0, 0, 0, 0] ++ copyBytes .t1 .a1 .t0 0 52 12 ++
  ([.li .t1 0, .store .d .t1 .t0 zeroOff, .store .d .t1 .t0 (zeroOff + 8),
    .store .d .s8 .t0 lenOff, .store .d .s10 .t0 (lenOff + 8), mov .a0 .t0] : List Instr)

/-- Our caller's registers back, from the context at `t0`. -/
def restore : List Instr :=
  [.load .d .s7 .t0 savOff, .load .d .s8 .t0 (savOff + 8), .load .d .s9 .t0 (savOff + 16),
    .load .d .s10 .t0 (savOff + 24), .load .d .s11 .t0 (savOff + 32), .load .d .ra .t0 (savOff + 40)]

/-! ## The calls -/

/-- The block with counter 0 into the buffer. -/
def keyGen : Prog isa :=
  .seq (.block [.addi .a1 .a0 bufOff]) (.call "vg_chacha20_block" Impl.ChaCha20.RISCV64.block)

/-- The Poly1305 state for the one-time key, and `a0` to it. -/
def polyInit : Prog isa :=
  .seq (.block [.addi .a1 .a0 bufOff, .addi .a0 .a0 polyOff])
    (.call "vg_poly1305_init" Impl.Poly1305.RISCV64.init)

/-- `vg_poly1305_update` of the `a3` bytes at `a2`, the message so far `a1`
bytes long. -/
def update : Prog isa := .call "vg_poly1305_update" Impl.Poly1305.RISCV64.update

/-- `n` rounded up to a multiple of 16, into `d`. -/
def round16 (d n : Reg) : List Instr := [.addi d n 15, .logicImm .and d d (-16)]

/-- The padding of `n` bytes, `(16 - n mod 16) mod 16` (`-n mod 16`), into `a3`, and the zeros into `a2`. -/
def padArgs (n : Reg) : List Instr :=
  [.li .a3 0, .sub .a3 .a3 n, .logicImm .and .a3 .a3 15, .addi .a2 .a0 (zeroOff - polyOff)]

/-- The MAC of the additional data and its padding. -/
def macAad : Prog isa :=
  .seq (.block [.li .a1 0, mov .a2 .s7, mov .a3 .s8]) (.seq update
    (.seq (.block (mov .a1 .s8 :: padArgs .s8)) update))

/-- The MAC of the ciphertext, its padding and the lengths block, and the
tag to `out` (`out` sets `a2`). -/
def macData (out : Instr) : Prog isa :=
  .seq (.block (round16 .a1 .s8 ++ [mov .a2 .s9, mov .a3 .s10])) (.seq update
  (.seq (.block (round16 .a1 .s8 ++ [.add .a1 .a1 .s10] ++ padArgs .s10)) (.seq update
  (.seq (.block (round16 .a1 .s8 ++ round16 .t0 .s10 ++
    [.add .a1 .a1 .t0, .addi .a2 .a0 (lenOff - polyOff), .li .a3 16])) (.seq update
  (.seq (.block (round16 .a1 .s8 ++ round16 .t0 .s10 ++ [.add .a1 .a1 .t0, .addi .a1 .a1 16, out]))
    (.call "vg_poly1305_finalize" Impl.Poly1305.RISCV64.finalize)))))))

/-- The ChaCha20 counter set to 1, and the data encrypted or decrypted, from
`a0` at the Poly1305 state; `a0` back to it. -/
def crypt : Prog isa :=
  .seq (.block [.addi .a0 .a0 (-(polyOff : Int)), .li .t0 1, .store .b .t0 .a0 48, mov .a1 .s9,
    mov .a2 .s10, .addi .a3 .a0 bufOff])
  (.seq (.call "vg_chacha20_xor" Impl.ChaCha20.RISCV64.Xor.xor)
    (.block [.addi .a0 .a0 polyOff]))

/-! ## Seal -/

def «seal» : Prog isa :=
  .seq (.block (save ++ moves ++ setup))
  (.seq keyGen
  (.seq polyInit
  (.seq macAad
  (.seq crypt
  (.seq (macData (mov .a2 .s11))
    (.block (.addi .t0 .a0 (-(polyOff : Int)) :: restore)))))))

/-! ## Open -/

/-- `t1 = 1` if the tag computed (at `a0 - 384 + 544`) is the one received
(at `s11`), else 0, without a branch: the OR of the XORs of their bytes is
less than 1. -/
def compare : List Instr :=
  [.addi .t0 .a0 (-(polyOff : Int)), .li .t1 0] ++
    (List.range 16).flatMap (fun i => [.load .b .t2 .t0 (tagOff + i), .load .b .t3 .s11 i,
      .logic .xor .t2 .t2 .t3, .logic .or .t1 .t1 .t2]) ++
    [.li .t2 1, .sltu .t1 .t1 .t2]

def «open» : Prog isa :=
  .seq (.block (save ++ moves ++ setup))
  (.seq keyGen
  (.seq polyInit
  (.seq macAad
  (.seq (macData (.addi .a2 .a0 (tagOff - polyOff)))
  (.seq crypt
    (.block (compare ++ restore ++ [mov .a0 .t1])))))))

end VG.Impl.ChaCha20Poly1305.RISCV64
