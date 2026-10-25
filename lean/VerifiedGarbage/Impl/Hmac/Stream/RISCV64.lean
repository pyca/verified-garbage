module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# HMAC over any streaming hash function: RISC-V implementation

One implementation of HMAC's `init` and `finalize` for every Merkle–Damgård
hash function with verified RISC-V streaming functions, which only calls
them: a `Hash` is a hash function's streaming `init`, `update` and
`finalize`, with their names and the sizes the code needs (the block `B`,
the hash value at the start of the streaming state `N`, the digest `D`,
which its `finalize` writes, and the bytes of stack `F` its `update` and
`finalize` use below the stack pointer, in frames of their own).

* `init(inner = a0, outer = a1, key = a2, key_len = a3)`, for a key of any
  length: a key longer than a block is first hashed with the streaming
  functions into a streaming state in our frame, and its digest used as the
  key. Then it sets each state's hash value with the streaming `init`; writes
  `K₀ ⊕ ipad` into the outer state's buffer (which a state representing the
  empty message does not use) and absorbs it into the inner state with
  `update`; then writes `K₀ ⊕ opad` into the inner state's buffer (which a
  state representing a whole block does not use) and absorbs it into the
  outer state. Each block is the key's bytes XORed with the pad byte, then
  the pad byte up to `B` bytes. Last, it zeroes the part of its frame that
  held the long key's streaming state and digest.
* `finalize(inner = a0, outer = a1, count = a2, out = a3)` finalizes the
  inner state into its frame, copies the outer state's hash value over the
  inner one's (the inner state then represents the outer block, whose
  buffer is empty), absorbs the inner digest with `update`, and finalizes
  again into `out`.

Each runs in a frame of its own (`alloc`), which holds the return address
and our caller's `s7`–`s11`. The functions we call save and restore the
callee-saved registers they use, `s0`–`s6`, and a register restored from
memory is secret to the analysis of constant time, so our variables live in
`s7`–`s11`, which none of them writes: `s7` = `inner`, `s8` = the frame,
`s9` = `outer`, and `s10` and `s11` the key and its length (`init`) or `s10`
= `out` (`finalize`). The states, the key and `out` are argument buffers,
whose alignment the contracts do not state, so they are accessed a byte at
a time. Every address and branch depends only on the pointers and the
lengths.
-/

@[expose] public section

namespace VG.Impl.Hmac.Stream.RISCV64

open VG.RISCV64

/-- `mv d, n` (`addi d, n, 0`). -/
def mov (d n : Reg) : Instr := .addi d n 0

/-- A streaming hash function's RISC-V functions, as HMAC calls them: the
block size `B = 2 ^ b`, the size `N` of the hash value at the start of the
streaming state (whose buffer follows it), the size `D` of the digest (which
`finalize` writes), the bytes `F` of stack below the stack pointer that
`update` and `finalize` use, and the three functions with their names. -/
structure Hash where
  b : Nat
  N : Nat
  D : Nat
  F : Nat
  initN : String
  initC : Prog isa
  updN : String
  updC : Prog isa
  finN : String
  finC : Prog isa

namespace Hash

variable (H : Hash)

/-- The block size. -/
abbrev B : Nat := 2 ^ H.b

/-- The size of the streaming state. -/
abbrev S : Nat := H.N + H.B

/-- The registers we save, and where, at `so` in the frame. -/
def savedAt (so : Nat) : List (Reg × Nat) :=
  [(.ra, so), (.s7, so + 8), (.s8, so + 16), (.s9, so + 24), (.s10, so + 32), (.s11, so + 40)]

/-- Save them, with the frame's address left in `t0`. -/
def saveAt (so : Nat) : List Instr := .addSp .t0 0 :: (savedAt so).map fun (r, d) => .store .d r .t0 d

/-- Restore them from the frame at `s8` (`s8`, the base, last). -/
def restoreAt (so : Nat) : List Instr :=
  [.load .d .ra .s8 so, .load .d .s7 .s8 (so + 8), .load .d .s9 .s8 (so + 24),
    .load .d .s10 .s8 (so + 32), .load .d .s11 .s8 (so + 40), .load .d .s8 .s8 (so + 16)]

/-- A call of the streaming `init`. -/
def callInit : Prog isa := .call H.initN H.initC

/-- A call of the streaming `update`. -/
def callUpd : Prog isa := .call H.updN H.updC

/-- A call of the streaming `finalize`. -/
def callFin : Prog isa := .call H.finN H.finC

/-! ## `init` -/

/-- Where `init` keeps our caller's registers in its frame (8-byte aligned),
after the long key's streaming state and digest. -/
def iso : Nat := (H.S + H.D + 7) / 8 * 8

/-- The bytes of `init`'s frame (16-byte aligned). -/
def ibytes : Nat := (H.iso + 48 + 15) / 16 * 16

/-- The key bytes (`t2` points at the next, `t3` counts those left), XORed
with the pad byte `t5`, into the buffer of the state at `dst` (byte `t6` at
`N(t4)`, `t4 = dst + t6`). -/
def keyLoop (dst : Reg) : Prog isa :=
  .loop (.block [.load .b .t1 .t2 0, .logic .xor .t1 .t1 .t5, .add .t4 dst .t6, .store .b .t1 .t4 H.N,
    .addi .t2 .t2 1, .addi .t6 .t6 1, .addi .t3 .t3 (-1)]) (.nonzero .t3)

/-- The pad byte into the rest of the buffer (`t3` bytes). -/
def padLoop (dst : Reg) : Prog isa :=
  .loop (.block [.add .t4 dst .t6, .store .b .t5 .t4 H.N, .addi .t6 .t6 1, .addi .t3 .t3 (-1)])
    (.nonzero .t3)

/-- `K₀ ⊕ c` into the buffer of the state at `dst`: the key's bytes (at
`s10`, `s11` of them) XORed with `c`, then `c` up to a block. -/
def padKey (dst : Reg) (c : Nat) : Prog isa :=
  .seq (.block [.li .t5 c, .li .t6 0, mov .t2 .s10, mov .t3 .s11])
  (.seq (.ite (.zero .t3) (.block []) (H.keyLoop dst))
  (.seq (.block [.li .t3 H.B, .sub .t3 .t3 .t6])
    (.ite (.zero .t3) (.block []) (H.padLoop dst))))

/-- `update` of the state at `st` with the block in the buffer of the one at
`src`, from a `count` of 0. -/
def updBlock (st src : Reg) : Prog isa :=
  .seq (.block [mov .a0 st, .li .a1 0, .addi .a2 src H.N, .li .a3 H.B]) H.callUpd

/-- Sets `t1` to a nonzero value exactly when `key_len` (`a3`) is more than
`B = 2 ^ b`: `key_len >> (b + 1)` (nonzero from `2 B`) plus
`((key_len & (2 B - 1)) + B - 1) >> (b + 1)` (1 from `B + 1` to `2 B - 1`).
It writes only `t1` and `t2`. -/
def entryCmp : List Instr :=
  [.shift .srl .d .t1 .a3 (H.b + 1), .logicImm .and .t2 .a3 (2 ^ (H.b + 1) - 1),
    .addi .t2 .t2 (2 ^ H.b - 1), .shift .srl .d .t2 .t2 (H.b + 1), .add .t1 .t1 .t2]

/-- A key longer than a block: hashed into the streaming state at the start
of the frame, and its digest, after it, made the key. -/
def longKey : Prog isa :=
  .seq (.block [mov .a0 .s8]) (.seq H.callInit
  (.seq (.block [mov .a0 .s8, .li .a1 0, mov .a2 .s10, mov .a3 .s11]) (.seq H.callUpd
  (.seq (.block [mov .a0 .s8, mov .a1 .s11, .addi .a2 .s8 H.S]) (.seq H.callFin
    (.block [.addi .s10 .s8 H.S, .li .s11 H.D]))))))

/-- Zero the first `iso` bytes of the frame (the long key's streaming state
and digest), a doubleword at a time. -/
def wipe : List Instr := .li .t1 0 :: (List.range (H.iso / 8)).map fun k => .store .d .t1 .s8 (8 * k)

/-- `init`, in its frame. -/
def initMain : Prog isa :=
  .seq (.block (saveAt H.iso ++ [mov .s7 .a0, mov .s8 .t0, mov .s9 .a1, mov .s10 .a2, mov .s11 .a3] ++
      H.entryCmp))
  (.seq (.ite (.zero .t1) (.block []) H.longKey)
  (.seq (.block [mov .a0 .s7])
  (.seq H.callInit
  (.seq (.block [mov .a0 .s9])
  (.seq H.callInit
  (.seq (H.padKey .s9 0x36)
  (.seq (H.updBlock .s7 .s9)
  (.seq (H.padKey .s7 0x5c)
  (.seq (H.updBlock .s9 .s7)
    (.block (H.wipe ++ restoreAt H.iso)))))))))))

/-- HMAC's `init`, for a key of any length. -/
def init : Prog isa := .frame (.alloc H.ibytes) H.initMain (.free H.ibytes)

/-! ## `finalize` -/

/-- Where `finalize` keeps our caller's registers in its frame (8-byte
aligned), after the inner digest. -/
def fso : Nat := (H.D + 7) / 8 * 8

/-- The bytes of `finalize`'s frame (16-byte aligned). -/
def fbytes : Nat := (H.fso + 48 + 15) / 16 * 16

/-- The outer state's hash value over the inner one's, a byte at a time. -/
def copyHV : List Instr :=
  (List.range H.N).flatMap fun k => [.load .b .t1 .s9 k, .store .b .t1 .s7 k]

/-- `finalize`, in its frame. -/
def finalizeMain : Prog isa :=
  .seq (.block (saveAt H.fso ++ [mov .s7 .a0, mov .s8 .t0, mov .s9 .a1, mov .s10 .a3, mov .a1 .a2,
      mov .a2 .t0]))
  (.seq H.callFin
  (.seq (.block (H.copyHV ++ [mov .a0 .s7, .li .a1 H.B, mov .a2 .s8, .li .a3 H.D]))
  (.seq H.callUpd
  (.seq (.block [mov .a0 .s7, .li .a1 (H.B + H.D), mov .a2 .s10])
  (.seq H.callFin
    (.block (restoreAt H.fso)))))))

/-- HMAC's `finalize`. -/
def finalize : Prog isa := .frame (.alloc H.fbytes) H.finalizeMain (.free H.fbytes)

end Hash

end VG.Impl.Hmac.Stream.RISCV64
