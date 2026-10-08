import VerifiedGarbage.Impl.AesGcm.X86_64
import VerifiedGarbage.Impl.Poly1305.X86_64.Callee

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices: x86-64 implementation

`vg_chacha20_poly1305_seal_gather(key = rdi, nonce = rsi, aad = rdx,
aad_len = rcx, src = r8, src_count = r9, dst = [rsp + 8], len = [rsp + 16],
tag = [rsp + 24])` copies the slices `src` lists, one after the other, to
`dst`, and encrypts them there in place with a call of
`vg_chacha20_poly1305_seal(key, nonce, aad, aad_len, dst, len, tag)`
(`name`, `code`: an instance of it).

Its frame pushes the six argument registers: `key`, `nonce`, `aad` and
`aad_len` wait there for the call, and the stack pointer stays a multiple of
16 at the call, with `tag` pushed for it. Our stack arguments are then at
`rsp + 56` … `rsp + 72`. The copy has `r11` at the next descriptor, `r9` the
number of slices left and `rdi` where the next slice goes; each slice is
copied from `rsi`, its length in `rcx` (`copyBytes`), with the index in
`r10`: as many bytes as possible at a time through `xmm0`, as wide as the
CPUs of the implementation of `vg_chacha20_poly1305_seal` called have
(`Width`: 16 bytes with SSE2's `movdqu`, 32 with AVX's `vmovdqu` of `ymm0`,
64 with AVX-512's `vmovdqu32` of `zmm0`); then, after a wider copy, 16
bytes at a time with AVX's `vmovdqu` of `xmm0` (not SSE2's, which would pay
for the dirty upper half of the register) and `vzeroupper`; then the last
`len mod 16` bytes one at a time. Every register the function writes is
caller-saved, and the branches are on `src_count` and the slices' lengths
alone.
-/

namespace VG.Impl.ChaCha20Poly1305.X86_64.SealGather

open VG.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm srcB dstB)

/-- How many bytes at a time `copyBytes` copies first. -/
inductive Width where
  /-- 16, with SSE2's `movdqu`. -/
  | x16
  /-- 32, with AVX's `vmovdqu` of `ymm0`. -/
  | y32
  /-- 64, with AVX-512's `vmovdqu32` of `zmm0`. -/
  | z64

/-- The widest copy the CPUs of an implementation of `vg_poly1305_blocks`
have: the instance of `vg_chacha20_poly1305_seal` called runs on the CPUs of
the implementation of `vg_poly1305_blocks` it calls. -/
def Width.ofBlocks : Impl.Poly1305.X86_64.Blocks → Width
  | .scalar => .x16
  | .avx2 => .y32
  | .avx512 => .z64

/-- The number of bytes, a power of two. -/
def Width.log : Width → Nat
  | .x16 => 4
  | .y32 => 5
  | .z64 => 6

/-- The loop's body: `2 ^ w.log` bytes from `[rsi + r10]` to `[rdi + r10]`
through `xmm0`, and the index advanced. -/
def wideBody : Width → List Instr
  | .x16 => [.movdquLoad .xmm0 srcB, .movdquStore dstB .xmm0, .alu .add .r10 (imm 16),
      .alu .cmp .r10 (.reg .r8)]
  | .y32 => [.vmovdquLoad .l256 .xmm0 srcB, .vmovdquStore .l256 dstB .xmm0, .alu .add .r10 (imm 32),
      .alu .cmp .r10 (.reg .r8)]
  | .z64 => [.vmovdqu32Load .xmm0 srcB, .vmovdqu32Store dstB .xmm0, .alu .add .r10 (imm 64),
      .alu .cmp .r10 (.reg .r8)]

/-- After a wider copy: 16 bytes at a time with AVX's `vmovdqu`, from `r10`
to `r8 = 16 ⌊rcx / 16⌋`. -/
def vex16Body : List Instr :=
  [.vmovdquLoad .l128 .xmm0 srcB, .vmovdquStore .l128 dstB .xmm0, .alu .add .r10 (imm 16),
    .alu .cmp .r10 (.reg .r8)]

/-- The last bytes, one at a time, from `r10` to `rcx`. -/
def copyTail : Prog isa :=
  .seq (.block [.alu .cmp .r10 (.reg .rcx)])
    (.ite .e (.block [])
      (.loop (.block [.movzx8 .rax srcB, .store8 dstB .rax, .alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .rcx)])
        .ne))

/-- Copies the `rcx` bytes at `rsi` to `rdi`: `2 ^ w.log` at a time (to
`r8 = 2 ^ w.log ⌊rcx / 2 ^ w.log⌋`, through `xmm0`), then, after a wider
copy, 16 at a time with AVX and `vzeroupper`, then one at a time, from
`r10 = 0`. -/
def copyBytes (w : Width) : Prog isa :=
  .seq (.block [.mov32 .r10 (imm 0), .mov .r8 (.reg .rcx), .shift .shr .r8 w.log, .shift .shl .r8 w.log,
    .alu .cmp .r8 (imm 0)])
  (.seq (.ite .e (.block []) (.loop (.block (wideBody w)) .ne))
  (match w with
    | .x16 => copyTail
    | _ => .seq (.block [.mov .r8 (.reg .rcx), .shift .shr .r8 4, .shift .shl .r8 4, .alu .cmp .r10 (.reg .r8)])
        (.seq (.ite .e (.block []) (.loop (.block vex16Body) .ne))
        (.seq (.block [.vop .vzeroupper]) copyTail))))

/-- The next descriptor: the slice's address in `rsi` and length in `rcx`. -/
def next : List Instr := [.mov .rsi (.mem (at_ .r11 0)), .mov .rcx (.mem (at_ .r11 8)), .alu .add .r11 (imm 16)]

/-- Past the slice in the output, and one slice fewer. -/
def advance : List Instr := [.alu .add .rdi (.reg .rcx), .alu .sub .r9 (imm 1)]

/-- Copies the `r9` (at least 1) slices that the descriptors at `r11` list
to `rdi`, one after the other. -/
def gatherLoop (w : Width) : Prog isa := .loop (.seq (.block next) (.seq (copyBytes w) (.block advance))) .ne

/-- Copies the `r9` slices that the descriptors at `r11` list to `rdi`. -/
def gather (w : Width) : Prog isa := .seq (.block [.alu .cmp .r9 (imm 0)]) (.ite .e (.block []) (gatherLoop w))

/-- The descriptors in `r11`, and `dst` in `rdi`. -/
def entry : List Instr := [.mov .r11 (.reg .r8), .mov .rdi (.mem (at_ .rsp 56))]

/-- The call's arguments: `key`, `nonce`, `aad` and `aad_len` back from the
frame, `dst` and `len`, and `tag` in `rax`, to push. -/
def callArgs : List Instr :=
  [.mov .rdi (.mem (at_ .rsp 40)), .mov .rsi (.mem (at_ .rsp 32)), .mov .rdx (.mem (at_ .rsp 24)),
    .mov .rcx (.mem (at_ .rsp 16)), .mov .r8 (.mem (at_ .rsp 56)), .mov .r9 (.mem (at_ .rsp 64)),
    .mov .rax (.mem (at_ .rsp 72))]

/-- `vg_chacha20_poly1305_seal_gather`, copying `2 ^ w.log` bytes at a time
and calling `vg_chacha20_poly1305_seal` (`name`, `code`). -/
def sealGather (w : Width) (name : String) (code : Prog isa) : Prog isa :=
  .frame (.push [.rdi, .rsi, .rdx, .rcx, .r8, .r9])
    (.seq (.block entry)
    (.seq (gather w)
    (.seq (.block callArgs)
      (.frame (.push [.rax]) (.call name code) (.pop .rax 1)))))
    (.pop .rax 6)

end VG.Impl.ChaCha20Poly1305.X86_64.SealGather
