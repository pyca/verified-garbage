import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx512
import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealGather

/-!
# ChaCha20 keystream XOR out of place: x86-64 implementation with AVX-512

`vg_chacha20_xor_to_avx512(state = rdi, src = rsi, len = rdx, dst = rcx,
dst_len = r8, buf = r9)`, with the contract of `vg_chacha20_xor_to`, for
CPUs with AVX-512F.

While at least 1024 bytes remain, the loop of `vg_chacha20_xor_avx512`
(`Avx512.body`) computes sixteen blocks of keystream and XORs them into the
next 1024 bytes of `src`, but writes the result to `dst` (`bodyTo`: its
`finish` loads the input from `r8`, the next bytes of `src`, and stores to
`rsi`, those of `dst`). The rest, fewer than 1024 bytes, is copied from
`src` to `dst` (`SealGather.copyBytes`) and XORed there in place by a call of
`vg_chacha20_xor_avx512` with the state, whose counter the loop advanced.

The branches are on the length only, and every address is a pointer plus a
constant or the length, so only the pointers and the length can affect
timing.
-/

namespace VG.Impl.ChaCha20.X86_64.Avx512

open VG.X86_64
open VG.Impl.ChaCha20.X86_64 (at_)

/-- `finish`, from the input at `r8`. -/
def finishTo : List Instr := finishFrom .r8

/-- As `next`, advancing the input too. -/
def nextTo : List Instr :=
  [.mov32 .rax (.mem (at_ .rdi 48)), .alu32 .add .rax (.imm 16), .store32 (at_ .rdi 48) .rax,
   .alu .add .rsi (.imm 1024), .alu .add .r8 (.imm 1024), .alu .sub .rdx (.imm 1024),
   .alu .cmp .rdx (.imm 1024)]

/-- Sixteen blocks, out of place. -/
def bodyTo : Prog isa := .seq (.block setup) (.seq (rounds 10) (.block (finishTo ++ nextTo)))

/-- The input in `r8`, the output in `rsi` and `buf` in `rcx`, as the loop
has them. -/
def entryTo : List Instr := [.mov .r8 (.reg .rsi), .mov .rsi (.reg .rcx), .mov .rcx (.reg .r9)]

/-- The copy's arguments: the state kept in `r11`, the output in `rdi`, the
input in `rsi` and the length in `rcx`. -/
def copyArgs : List Instr := [.mov .r11 (.reg .rdi), .mov .rdi (.reg .rsi), .mov .rsi (.reg .r8), .mov .rcx (.reg .rdx)]

/-- The call's arguments: the state, the output, the length (still in `rdx`)
and `buf`. -/
def callArgs : List Instr := [.mov .rsi (.reg .rdi), .mov .rdi (.reg .r11), .mov .rcx (.reg .r9)]

/-- The last `rdx` bytes (fewer than 1024), if any: copied, then XORed in
place. -/
def restTo : Prog isa :=
  .seq (.block [.alu .test .rdx (.reg .rdx)])
    (.ite .e (.block [.vop .vzeroupper])
      (.seq (.block copyArgs) (.seq (ChaCha20Poly1305.X86_64.SealGather.copyBytes .z64)
        (.seq (.block callArgs) (.call "vg_chacha20_xor_avx512" xor)))))

def xorTo : Prog isa :=
  .seq (.block (entryTo ++ consts ++ ([.alu .cmp .rdx (.imm 1024)] : List Instr)))
  (.seq (.ite .b (.block []) (.loop bodyTo .ae)) restTo)

end VG.Impl.ChaCha20.X86_64.Avx512
