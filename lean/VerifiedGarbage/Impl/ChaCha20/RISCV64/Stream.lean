module

public import VerifiedGarbage.Impl.ChaCha20.RISCV64.Xor
public import VerifiedGarbage.Impl.Words.RISCV64.Bytes
public import VerifiedGarbage.Spec.ChaCha20

/-!
# Streaming ChaCha20: RISC-V implementation

`vg_chacha20_init(state = a0, key = a1, nonce = a2)`,
`vg_chacha20_set_nonce(state = a0, nonce = a1)` and
`vg_chacha20_apply(state = a0, data = a1, len = a2) -> a0`, on the streaming
state of `VG.Spec.ChaCha20.restAt` (768 bytes), laid out as on PPC64LE
(`VG.Impl.ChaCha20.PPC64LE.Stream`):

* `[0, 64)`: the 16-word state, `[64, 128)`: the buffered block,
  `[128, 136)`: the number of bytes of keystream left;
* `[192, 256)`: the copy of the 16-word state that `vg_chacha20_xor` is
  given (it leaves its state unspecified), `[256, 576)`: its working space;
* from `state + 576` rounded up to a multiple of 8: our caller's `s5`–`s8`
  and our return address (which each call replaces), as doublewords.

The state is an argument buffer, whose alignment the contract does not
state, so it is read and written a byte at a time
(`Impl/Words/RISCV64/Bytes.lean`), but for the saved registers, at an
address rounded up.

`set_nonce` writes the nonce (words 12–15), the constants and the number of
bytes left, 64 × (2³² − c) for the initial block counter `c`; `init` also
copies the key, then does the same.

`apply` compares the number of bytes left with `len`, and those left in the
buffered block (the last `left % 64`) with `len`, first (`sltu`). If fewer
than `len` bytes are left it returns 0 at once. Otherwise it XORs the bytes
left in the buffered block (as many as `len` asks for), then the whole
blocks that follow with `vg_chacha20_xor`, advancing the counter, and
finally, if bytes remain, computes the next block into the buffer with
`vg_chacha20_block`, advances the counter and XORs its first bytes. `s5`
holds the state, `s6` the data not yet processed, `s7` its length and `s8`
the number of bytes left after `apply` throughout: neither callee writes
them, and the block function overwrites `[64, 320)`, so the number left is
stored last. A call stores nothing in memory, so no stack is used.

The branches are on the length and the number of bytes left only, and every
address is a pointer plus a constant, or advances by one: only the
pointers, the length and the number of bytes left (which the contract lets
`apply` leak) can affect timing.
-/

@[expose] public section

namespace VG.Impl.ChaCha20.RISCV64.Stream

open VG.RISCV64
open VG.Impl.Words.RISCV64
open VG.Impl.ChaCha20.RISCV64 (block)
open VG.Impl.ChaCha20.RISCV64.Xor (mov xor)

/-- The bytes of the constants (`VG.Spec.ChaCha20.constants`), little-endian. -/
def sigmaBytes : List Nat :=
  (List.range 16).map fun i =>
    ((Spec.ChaCha20.constants.getD (i / 4) 0).extractLsb' (8 * (i % 4)) 8).toNat

/-- The nonce at `a1`, the constants and the number of bytes left, into the
state at `a0`. -/
def setNonceInstrs : List Instr :=
  copyBytes .t1 .a1 .a0 0 48 16 ++ storeBytes .t1 .a0 0 sigmaBytes ++
  loadLE32 .t1 .t2 .a1 0 ++
  [.li .t2 1, .shift .sll .d .t2 .t2 32, .sub .t2 .t2 .t1, .shift .sll .d .t2 .t2 6] ++
  storeLE64 .t2 .t1 .t3 .a0 128

def setNonce : Prog isa := .block setNonceInstrs

/-- The key at `a1` into words 4–11, and the nonce pointer into `a1`. -/
def keyInstrs : List Instr := copyBytes .t1 .a1 .a0 0 16 32 ++ [mov .a1 .a2]

def init : Prog isa := .block (keyInstrs ++ setNonceInstrs)

/-! ## `apply` -/

/-- `t1` = the bytes left, `t3` = those in the buffered block, `t4` = 1 iff
fewer than `len` are left, `t5` = 1 iff the buffered block has fewer than
`len`. -/
def check : List Instr :=
  loadLE64 .t1 .t2 .t3 .a0 128 ++ [.logicImm .and .t3 .t1 63, .sltu .t4 .t1 .a2, .sltu .t5 .t3 .a2]

/-- `t0 :=` `n + 576` rounded up to a multiple of 8 (`(n + 583) & -8`). -/
def savePtr (n : Reg) : List Instr := [.addi .t0 n 583, .logicImm .and .t0 .t0 (-8)]

/-- Saves our caller's registers and our return address, and moves the
arguments where they are kept, with the bytes left after `apply` in `s8`. -/
def start : List Instr :=
  savePtr .a0 ++
  [.store .d .ra .t0 0, .store .d .s5 .t0 8, .store .d .s6 .t0 16, .store .d .s7 .t0 24,
   .store .d .s8 .t0 32, mov .s5 .a0, mov .s6 .a1, mov .s7 .a2, .sub .s8 .t1 .a2]

/-- XORs the `a2` bytes at `t2` into the data (`s6`), advancing both, and
counting them off `s7`. -/
def xorBytes : Prog isa :=
  .ite (.zero .a2) (.block [])
    (.loop (.block [.load .b .t3 .s6 0, .load .b .t4 .t2 0, .logic .xor .t3 .t3 .t4,
      .store .b .t3 .s6 0, .addi .s6 .s6 1, .addi .t2 .t2 1, .addi .a2 .a2 (-1),
      .addi .s7 .s7 (-1)]) (.nonzero .a2))

/-- Everything up to the call of `vg_chacha20_xor`: the bytes left in the
buffered block, `a2 = min(t3, len)` of them, from `s5 + 128 - t3`; then
`a2` = the bytes of the whole blocks that follow (`s7` rounded down to a
multiple of 64). -/
def part1 : Prog isa :=
  .seq (.block start)
  (.seq (.ite (.nonzero .t5) (.block [mov .a2 .t3]) (.block []))
  (.seq (.block [.addi .t2 .s5 128, .sub .t2 .t2 .t3])
  (.seq xorBytes
    (.block [.shift .srl .d .a2 .s7 6, .shift .sll .d .a2 .a2 6]))))

/-- The whole blocks: the state copied and the counter advanced (word 12),
then `vg_chacha20_xor` on the copy. -/
def blocksArgs : List Instr :=
  copyBytes .t1 .s5 .s5 0 192 64 ++ [.shift .srl .d .t4 .a2 6] ++ loadLE32 .t1 .t3 .s5 48 ++
  [.add .t1 .t1 .t4] ++ storeLE32 .t1 .t3 .s5 48 ++
  [.addi .a0 .s5 192, mov .a1 .s6, .addi .a3 .s5 256, .add .s6 .s6 .a2, .sub .s7 .s7 .a2]

def part2 : Prog isa :=
  .ite (.zero .a2) (.block []) (.seq (.block blocksArgs) (.call "vg_chacha20_xor" xor))

/-- The arguments of the block function: the state and the buffer. -/
def tailArgs : List Instr := [mov .a0 .s5, .addi .a1 .s5 64]

/-- The counter advanced (word 12). -/
def incr : List Instr := loadLE32 .t1 .t3 .s5 48 ++ [.addi .t1 .t1 1] ++ storeLE32 .t1 .t3 .s5 48

/-- After the block function: the counter advanced, and `s7` bytes of the
block XORed. -/
def tailXor : Prog isa := .seq (.block (incr ++ [.addi .t2 .s5 64, mov .a2 .s7])) xorBytes

/-- The last bytes, if any: the next block into the buffer, the counter
advanced, and `s7` bytes of the block XORed. -/
def part3 : Prog isa :=
  .ite (.zero .s7) (.block [])
    (.seq (.block tailArgs) (.seq (.call "vg_chacha20_block" block) tailXor))

/-- The bytes left stored, our caller's registers and our return address
restored, and 1 returned. -/
def finish : List Instr :=
  storeLE64 .s8 .t1 .t2 .s5 128 ++ savePtr .s5 ++
  [.load .d .ra .t0 0, .load .d .s6 .t0 16, .load .d .s7 .t0 24, .load .d .s8 .t0 32,
   .load .d .s5 .t0 8, .li .a0 1]

def apply : Prog isa :=
  .seq (.block check)
  (.ite (.nonzero .t4) (.block [.li .a0 0])
    (.seq part1 (.seq part2 (.seq part3 (.block finish)))))

end VG.Impl.ChaCha20.RISCV64.Stream
