import VerifiedGarbage.Impl.AesGcm.X86_64

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
copied from `rsi`, its length in `rcx`, 16 bytes at a time through `xmm0`,
then its last `len mod 16` bytes one at a time (`copyBytes`), with the index
in `r10`. Every register the function writes is caller-saved, and the
branches are on `src_count` and the slices' lengths alone.
-/

namespace VG.Impl.ChaCha20Poly1305.X86_64.SealGather

open VG.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm srcB dstB)

/-- Copies the `rcx` bytes at `rsi` to `rdi`: 16 at a time (to
`r8 = 16 ⌊rcx / 16⌋`, through `xmm0`), then one at a time, from `r10 = 0`. -/
def copyBytes : Prog isa :=
  .seq (.block [.mov32 .r10 (imm 0), .mov .r8 (.reg .rcx), .shift .shr .r8 4, .shift .shl .r8 4,
    .alu .cmp .r8 (imm 0)])
  (.seq (.ite .e (.block [])
      (.loop (.block [.movdquLoad .xmm0 srcB, .movdquStore dstB .xmm0, .alu .add .r10 (imm 16),
        .alu .cmp .r10 (.reg .r8)]) .ne))
  (.seq (.block [.alu .cmp .r10 (.reg .rcx)])
    (.ite .e (.block [])
      (.loop (.block [.movzx8 .rax srcB, .store8 dstB .rax, .alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .rcx)])
        .ne))))

/-- The next descriptor: the slice's address in `rsi` and length in `rcx`. -/
def next : List Instr := [.mov .rsi (.mem (at_ .r11 0)), .mov .rcx (.mem (at_ .r11 8)), .alu .add .r11 (imm 16)]

/-- Past the slice in the output, and one slice fewer. -/
def advance : List Instr := [.alu .add .rdi (.reg .rcx), .alu .sub .r9 (imm 1)]

/-- Copies the `r9` (at least 1) slices that the descriptors at `r11` list
to `rdi`, one after the other. -/
def gatherLoop : Prog isa := .loop (.seq (.block next) (.seq copyBytes (.block advance))) .ne

/-- Copies the `r9` slices that the descriptors at `r11` list to `rdi`. -/
def gather : Prog isa := .seq (.block [.alu .cmp .r9 (imm 0)]) (.ite .e (.block []) gatherLoop)

/-- The descriptors in `r11`, and `dst` in `rdi`. -/
def entry : List Instr := [.mov .r11 (.reg .r8), .mov .rdi (.mem (at_ .rsp 56))]

/-- The call's arguments: `key`, `nonce`, `aad` and `aad_len` back from the
frame, `dst` and `len`, and `tag` in `rax`, to push. -/
def callArgs : List Instr :=
  [.mov .rdi (.mem (at_ .rsp 40)), .mov .rsi (.mem (at_ .rsp 32)), .mov .rdx (.mem (at_ .rsp 24)),
    .mov .rcx (.mem (at_ .rsp 16)), .mov .r8 (.mem (at_ .rsp 56)), .mov .r9 (.mem (at_ .rsp 64)),
    .mov .rax (.mem (at_ .rsp 72))]

/-- `vg_chacha20_poly1305_seal_gather`, calling `vg_chacha20_poly1305_seal`
(`name`, `code`). -/
def sealGather (name : String) (code : Prog isa) : Prog isa :=
  .frame (.push [.rdi, .rsi, .rdx, .rcx, .r8, .r9])
    (.seq (.block entry)
    (.seq gather
    (.seq (.block callArgs)
      (.frame (.push [.rax]) (.call name code) (.pop .rax 1)))))
    (.pop .rax 6)

end VG.Impl.ChaCha20Poly1305.X86_64.SealGather
