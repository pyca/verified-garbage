import VerifiedGarbage.Impl.ChaCha20.X86_64.Callee
import VerifiedGarbage.Impl.Poly1305.X86_64.Callee

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

The working space (`workLen` = 608 bytes, called the context below):

* `[0, 48)`: our caller's `rbx, rbp, r13, r14, r15, r12`;
* `[48, 64)`: the tag computed by `open`;
* `[64, 128)`: the ChaCha20 state, built from the key and the nonce;
* `[128, 448)`: the working space of `vg_chacha20_xor` (the first 32 bytes of
  the block with counter 0 are the one-time Poly1305 key);
* `[448, 576)`: the Poly1305 state;
* `[576, 592)`: the padded last block of the additional data or the data;
* `[592, 608)`: the lengths block.

The entry loads `work` and `tag` from the stack (`entry`). `r15` holds the
context, `r14` the data, `r13` its length and `r12` the tag, which
`vg_chacha20_xor` never writes; `rbx` and `rbp` hold the additional data and
its length, which are only needed before the call of `vg_chacha20_xor`. The
lengths block is stored before that call. `seal` passes `tag` to
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
def workLen : Nat := 608

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

/-- Word `k` of the ChaCha20 state, at `r15 + 64 + 4k`. -/
def stW (k : Nat) : List Instr := [.mov32 .rax (stSrc k), .store32 (at_ .r15 (64 + 4 * k)) .rax]

/-- The ChaCha20 state for counter 0. -/
def initState : List Instr := (List.range 16).flatMap stW

/-- The arguments moved to where they are kept. -/
def moves : List Instr :=
  [.mov .r15 (.reg .rax), .mov .r12 (.reg .r11), .mov .rbx (.reg .rdx), .mov .rbp (.reg .rcx),
    .mov .r14 (.reg .r8), .mov .r13 (.reg .r9)]

/-- After `entry`: saves the registers, moves the arguments, and computes the
one-time key and the Poly1305 state for it. -/
def prologue : Prog isa :=
  .seq (.block (save ++ moves ++ initState ++ ptr .rdi .r15 64 ++ ptr .rsi .r15 128))
  (.seq (.call "vg_chacha20_block" Impl.ChaCha20.X86_64.block)
  (.seq (.block (anchor .rsi 128 ++ ptr .rdi .r15 448 ++ ptr .rsi .r15 128))
  (.seq (.call "vg_poly1305_init" Impl.Poly1305.X86_64.init)
    (.block (anchor .rdi 448)))))

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

/-- The arguments of `vg_chacha20_xor`, with the ChaCha20 counter set to 1. -/
def cryptArgs : List Instr :=
  [.mov32 .rax (.imm 1), .store32 (at_ .r15 112) .rax] ++ ptr .rdi .r15 64 ++
    [.mov .rsi (.reg .r14), .mov .rdx (.reg .r13)] ++ ptr .rcx .r15 128

/-- The data encrypted or decrypted by the implementation `x` of
`vg_chacha20_xor`. -/
def crypt (x : ChaCha20.X86_64.Callee) : Prog isa :=
  .seq (.block cryptArgs) (.seq (.call x.name x.code) (.block (anchor .rsi 128)))

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
  (.seq prologue
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
  (.seq prologue
  (.seq (macPad b .rbx .rbp)
  (.seq (macPad b .r14 .r13)
  (.seq (.block lengths)
  (.seq (absorbLengths b)
  (.seq (crypt x)
  (.seq (finalizeTo 48)
    (.block (compare ++ restore)))))))))

end VG.Impl.ChaCha20Poly1305.X86_64
