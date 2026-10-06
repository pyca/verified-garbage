import VerifiedGarbage.Impl.ChaCha20.X86_64.Callee
import VerifiedGarbage.Impl.Poly1305.X86_64.Callee
import VerifiedGarbage.Impl.ChaCha20.X86_64.XorBuf

/-!
# ChaCha20-Poly1305: x86-64 implementation

`vg_chacha20_poly1305_seal(key = rdi, nonce = rsi, aad = rdx, aad_len = rcx, data = r8,
len = r9, tag = [rsp + 8], work = [rsp + 16])` and `vg_chacha20_poly1305_open` (the same
arguments, returning `eax`), composed of calls of the verified ChaCha20 and
Poly1305 functions. `work` is the working space, which the artifact's frame
allocates on the stack (`withStackArgScratchWiped`). They are generic
over the implementations of `vg_chacha20_xor` (`Callee`) and
`vg_poly1305_blocks` (`Blocks`) they call: each of them is emitted once for
each implementation of `vg_chacha20_xor`, which comes with the one of
`vg_poly1305_blocks` for the same CPUs (e.g. `vg_chacha20_poly1305_seal`
calls `vg_chacha20_xor` and `vg_poly1305_blocks`, and
`vg_chacha20_poly1305_seal_avx2` calls `vg_chacha20_xor_avx2` and
`vg_poly1305_blocks_avx2`).

The working space (`workLen` = 1696 bytes, called the context below):

* `[0, 48)`: our caller's `rbx, rbp, r13, r14, r15, r12`;
* `[48, 64)`: the tag computed by `open`;
* `[64, 128)`: the ChaCha20 state, built from the key and the nonce;
* `[128, 448)`: the working space of `vg_chacha20_xor`;
* `[448, 576)`: the Poly1305 state;
* `[576, 592)`: the padded last block of the additional data or the data;
* `[592, 608)`: the lengths block;
* `[608, 672)`: a copy of the ChaCha20 state, for the first call of
  `vg_chacha20_xor`, which may change it;
* `[672, 1696)`: the keystream from block counter 0: its first 32 bytes are
  the one-time Poly1305 key, and the next `m` bytes the keystream for the
  first `m` bytes of the data.

`m` is the length of the data if it is at most the implementation's `fold`
(`Callee.fold`), and 0 otherwise. The prologue zeros the first `64 + m`
bytes of `ctx[672, 1696)` and XORs the keystream from counter 0 into them
(one call of `vg_chacha20_xor`, which computes them in one pass): the block
with counter 0, whose first 32 bytes are the one-time key, and the keystream
of the first `m` bytes of the data. `crypt` XORs those into the data
(`XorBuf.xorBuf`), and the rest of the data (none, or all of it) by a second
call of `vg_chacha20_xor`, from counter 1. Then it zeros those `64 + m`
bytes again, as the wrapper zeroes only `ctx[0, 672)`, and nothing else is
written after it.

The entry loads `work` and `tag` from the stack (`entry`). `r15` holds the
context, `r14` the data, `r13` its length and `r12` the tag, which
`vg_chacha20_xor` never writes; `rbx` and `rbp` hold the additional data and
its length, which are only needed before the second call of
`vg_chacha20_xor`. The lengths block is stored before that call. `seal` passes `tag` to
`vg_poly1305_finalize_scratch` as its `out`; after `open`'s call of it only
`rdi` (its argument, the Poly1305 state), `rcx` (which it returns set to its
argument `out`, the tag computed) and `r12` (the tag received) are used, to
compare the tags and to restore the registers.

After each call, `r15` is recomputed from a pointer argument the callee never
writes (`rsi`, into the context, for the ChaCha20 functions; `rdi` for the
Poly1305 ones). Its value does not change, but this way the constant-time
analysis knows it for the context's address, which it cannot know of a value
the callee restored from memory.

Only the pointers and the lengths can affect timing: the branches are on the
lengths, and the tags are compared without a branch.
-/

namespace VG.Impl.ChaCha20Poly1305.X86_64

open VG.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)

/-- `r + d` into `d'`. -/
def ptr (d' r : Reg) (k : Nat) : List Instr := [.mov d' (.reg r), .alu .add d' (.imm (BitVec.ofNat 32 k))]

/-- The context's address into `r15`, from `r = r15 + k`. -/
def anchor (r : Reg) (k : Nat) : List Instr := [.mov .r15 (.reg r), .alu .sub .r15 (.imm (BitVec.ofNat 32 k))]

/-- The size of the working space, in bytes. -/
def workLen : Nat := 1696

def saved : List (Reg × Nat) :=
  [(.rbx, 0), (.rbp, 8), (.r13, 16), (.r14, 24), (.r15, 32), (.r12, 40)]

/-- `work` into `rax` and `tag` into `r11`, from the stack. -/
def entry : List Instr := [.mov .rax (.mem (at_ .rsp 16)), .mov .r11 (.mem (at_ .rsp 8))]

/-- Saves the registers, with the context in `rax`. -/
def save : List Instr := saved.map fun (r, d) => .store (at_ .rax d) r
/-- Loads the saved registers through `r15`, the context (`r15` last). -/
def restoreLoads : List Instr :=
  [(.rbx, 0), (.rbp, 8), (.r13, 16), (.r14, 24), (.r12, 40), (.r15, 32)].map fun (r, d) =>
    .mov r (.mem (at_ .r15 d))

/-- Restores the registers, with `rdi` pointing at the Poly1305 state: the
context's address into `r15` (`anchor`), and the loads. -/
def restore : List Instr := anchor .rdi 448 ++ restoreLoads

/-- Where word `k` of the ChaCha20 state for counter 0 comes from: a constant
(0–3), the key (4–11, at `rdi`), the counter (12) or the nonce (13–15, at
`rsi`). -/
def stSrc (k : Nat) : Src :=
  if k < 4 then .imm ([0x61707865, 0x3320646e, 0x79622d32, 0x6b206574].getD k 0)
  else if k < 12 then .mem (at_ .rdi (4 * (k - 4)))
  else if k = 12 then .imm 0
  else .mem (at_ .rsi (4 * (k - 13)))

/-- Word `k` of the ChaCha20 state, at `r15 + o + 4k`. -/
def stW (o k : Nat) : List Instr := [.mov32 .rax (stSrc k), .store32 (at_ .r15 (o + 4 * k)) .rax]

/-- The ChaCha20 state for counter 0, at `r15 + o`. -/
def initState (o : Nat) : List Instr := (List.range 16).flatMap (stW o)

/-- The arguments moved to where they are kept. -/
def moves : List Instr :=
  [.mov .r15 (.reg .rax), .mov .r12 (.reg .r11), .mov .rbx (.reg .rdx), .mov .rbp (.reg .rcx),
    .mov .r14 (.reg .r8), .mov .r13 (.reg .r9)]

/-- `rdx = m`: the length of the data (in `r13`) if it is at most `fold`,
else 0. -/
def foldM (fold : Nat) : Prog isa :=
  .seq (.block [.mov32 .rdx (.imm 0), .alu .cmp .r13 (.imm (BitVec.ofNat 32 (fold + 1)))])
    (.ite .b (.block [.mov .rdx (.reg .r13)]) (.block []))

/-- `[r15 + rcx + 672]`. -/
def zeroQ : MemOp := { base := .r15, index := some .rcx, disp := 672 }

/-- Zeros the quadwords of `ctx[672, 1696)` from the first, while fewer
than `rdx` bytes are zeroed (at least one). -/
def zeroKs : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0), .mov32 .rcx (.imm 0)])
    (.loop (.block [.store zeroQ .rax, .alu .add .rcx (.imm 8), .alu .cmp .rcx (.reg .rdx)]) .b)

/-- The prologue up to the call of `vg_chacha20_xor`: saves the registers,
moves the arguments, builds the ChaCha20 state twice (the copy for the call), zeros the first
`64 + m` bytes of `ctx[672, 1696)` (rounded up to quadwords) and sets up the
call's arguments, the copy of the state and those bytes. -/
def prologueA (fold : Nat) : Prog isa :=
  .seq (.block (save ++ moves ++ initState 64 ++ initState 608))
  (.seq (foldM fold)
  (.seq (.block [.alu .add .rdx (.imm 64)])
  (.seq zeroKs
    (.block (ptr .rdi .r15 608 ++ ptr .rsi .r15 672 ++ ptr .rcx .r15 128)))))

/-- After the call of `vg_chacha20_xor`: the Poly1305 state for the one-time
key, the first 32 bytes of `ctx[672, 1696)`. -/
def prologueB : Prog isa :=
  .seq (.block (anchor .rsi 128 ++ ptr .rdi .r15 448 ++ ptr .rsi .r15 672))
  (.seq (.call "vg_poly1305_init" Impl.Poly1305.X86_64.init)
    (.block (anchor .rdi 448)))

/-- After `entry`: the keystream from counter 0 XORed into `64 + m` zero
bytes by the implementation `x` of `vg_chacha20_xor`, and the Poly1305 state
for the one-time key. -/
def prologue (x : ChaCha20.X86_64.Callee) : Prog isa :=
  .seq (prologueA x.fold) (.seq (.call x.name x.code) prologueB)

/-- `[rsi + rcx]` and `[r15 + rcx + 576]`. -/
def tailByte : MemOp := { base := .rsi, index := some .rcx }
def padByte : MemOp := { base := .r15, index := some .rcx, disp := 576 }

/-- The last `rdx` bytes (1 to 15) at `rsi`, padded with zeros, absorbed. -/
def padTail (b : Poly1305.X86_64.Blocks) : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0), .store (at_ .r15 576) .rax, .store (at_ .r15 584) .rax,
    .mov32 .rcx (.imm 0)])
  (.seq (.loop (.block [.movzx8 .rax tailByte, .store8 padByte .rax, .alu .add .rcx (.imm 1),
    .alu .cmp .rcx (.reg .rdx)]) .ne)
  (.seq (.block (ptr .rdi .r15 448 ++ ptr .rsi .r15 576 ++ [.mov32 .rdx (.imm 1)]))
  (.seq (.call b.name b.code)
    (.block (anchor .rdi 448)))))

/-- The `n` bytes at `p`, padded with zeros to a multiple of 16, absorbed. -/
def macPad (b : Poly1305.X86_64.Blocks) (p n : Reg) : Prog isa :=
  .seq (.block (ptr .rdi .r15 448 ++ [.mov .rsi (.reg p), .mov .rdx (.reg n), .shift .shr .rdx 4]))
  (.seq (.call b.name b.code)
  (.seq (.block (anchor .rdi 448 ++ [.mov .rdx (.reg n), .alu .and .rdx (.imm 15)]))
    (.ite .e (.block []) (.seq (.block [.mov .rsi (.reg n), .alu .sub .rsi (.reg .rdx),
      .alu .add .rsi (.reg p)]) (padTail b)))))

/-- The arguments of the second call of `vg_chacha20_xor`: the ChaCha20
state with the counter set to 1, and the data. -/
def cryptArgs : List Instr :=
  [.mov32 .rax (.imm 1), .store32 (at_ .r15 112) .rax] ++ ptr .rdi .r15 64 ++
    [.mov .rsi (.reg .r14), .mov .rdx (.reg .r13)] ++ ptr .rcx .r15 128

/-- The data encrypted or decrypted, then the keystream wiped. If its length
is at most `fold`, by XORing the keystream in `ctx[736, 736 + len)` into it;
otherwise by the implementation `x` of `vg_chacha20_xor`, from counter 1.
Either way `rsi` then points at `ctx + 128`. -/
def crypt (x : ChaCha20.X86_64.Callee) : Prog isa :=
  .seq (.block [.alu .cmp .r13 (.imm (BitVec.ofNat 32 (x.fold + 1)))])
  (.seq (.ite .b
    (.seq (.block (ptr .rsi .r15 736 ++ [.mov .rdx (.reg .r13)]))
      (.seq (ChaCha20.X86_64.XorBuf.xorBuf .r14 .rsi) (.block (ptr .rsi .r15 128))))
    (.seq (.block cryptArgs) (.call x.name x.code)))
  (.seq (.block (anchor .rsi 128))
  (.seq (foldM x.fold)
  (.seq (.block [.alu .add .rdx (.imm 64)]) zeroKs))))

/-- The lengths block. -/
def lengths : List Instr := [.store (at_ .r15 592) .rbp, .store (at_ .r15 600) .r13]

/-- The lengths block absorbed. -/
def absorbLengths (b : Poly1305.X86_64.Blocks) : Prog isa :=
  .seq (.block (ptr .rdi .r15 448 ++ ptr .rsi .r15 592 ++ [.mov32 .rdx (.imm 1)]))
  (.seq (.call b.name b.code)
    (.block (anchor .rdi 448)))

/-- The tag written to `out`, whose address `outPtr` puts in `rdx`: the
message is whole blocks, so its length (`count`) is 0 modulo 16, and nothing
is buffered. -/
def finalizeWith (outPtr : List Instr) : Prog isa :=
  .seq (.block (ptr .rdi .r15 448 ++ [.mov32 .rsi (.imm 0)] ++ outPtr))
    (.call "vg_poly1305_finalize_scratch" Impl.Poly1305.X86_64.finalize)

/-- The tag written to `r15 + out`. -/
def finalizeTo (out : Nat) : Prog isa := finalizeWith (ptr .rdx .r15 out)

/-- The tag written to `tag` (in `r12`). -/
def finalizeTag : Prog isa := finalizeWith [.mov .rdx (.reg .r12)]

def «seal» (x : ChaCha20.X86_64.Callee) (b : Poly1305.X86_64.Blocks) : Prog isa :=
  .seq (.block entry)
  (.seq (prologue x)
  (.seq (macPad b .rbx .rbp)
  (.seq (.block lengths)
  (.seq (crypt x)
  (.seq (macPad b .r14 .r13)
  (.seq (absorbLengths b)
  (.seq finalizeTag
    (.block restore))))))))

/-- `eax = 1` if the computed tag (at `rcx`) is the received one (at `r12`),
else 0, without a branch. -/
def compare : List Instr :=
  [.mov .rax (.mem (at_ .rcx 0)), .alu .xor .rax (.mem (at_ .r12 0)),
   .mov .rdx (.mem (at_ .rcx 8)), .alu .xor .rdx (.mem (at_ .r12 8)),
   .alu .or .rax (.reg .rdx), .alu .cmp .rax (.imm 1), .mov32 .rax (.imm 0), .alu32 .adc .rax (.imm 0)]

def «open» (x : ChaCha20.X86_64.Callee) (b : Poly1305.X86_64.Blocks) : Prog isa :=
  .seq (.block entry)
  (.seq (prologue x)
  (.seq (macPad b .rbx .rbp)
  (.seq (macPad b .r14 .r13)
  (.seq (.block lengths)
  (.seq (absorbLengths b)
  (.seq (crypt x)
  (.seq (finalizeTo 48)
    (.block (compare ++ restore)))))))))

end VG.Impl.ChaCha20Poly1305.X86_64
