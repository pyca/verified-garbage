module

public import VerifiedGarbage.Impl.AesGcm.X86_64
public import VerifiedGarbage.Impl.Poly1305.X86_64.Callee

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
copied from `rsi`, its length in `rcx` (`copyBytes`), as wide as the CPUs
of the implementation of `vg_chacha20_poly1305_seal` called allow (`Width`:
`c` = 16 bytes with SSE2's `movdqu`, 32 with AVX's `vmovdqu` of a `ymm`
register, 64 with AVX-512's `vmovdqu32` of a `zmm` register). With at
least `2 c` bytes, it copies the first `c`, then `2 c` at a time through
`xmm0` and `xmm1`, with the index in `r10`, from the first offset at which
the stores are aligned, while `2 c` remain, then the last `2 c`, which may
overlap what was copied before (`big`). With fewer, it copies the first and
the last `c'` bytes, overlapping, for the largest width `c'` (32, 16, 8 or 4
bytes, the last two through `rax` and `r8`) at most the length (`ladder`),
and fewer than 4 bytes one at a time. After a copy wider than 16 bytes,
`vzeroupper`. Every register the function writes is caller-saved, and the
branches are on `src_count`, the slices' lengths and the addresses in `dst`
they go to alone.
-/

@[expose] public section

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

/-- `[base + index + d]`. -/
def at2 (base index : Reg) (d : Int) : MemOp := { base := base, index := some index, disp := d }

/-- A load of `2 ^ w.log` bytes into `x`, and a store of them: SSE2's
`movdqu`, AVX's `vmovdqu` of a `ymm` register, AVX-512's `vmovdqu32` of a
`zmm` register. -/
def ldW : Width → XReg → MemOp → Instr
  | .x16, x, m => .movdquLoad x m
  | .y32, x, m => .vmovdquLoad .l256 x m
  | .z64, x, m => .vmovdqu32Load x m
def stW : Width → MemOp → XReg → Instr
  | .x16, m, x => .movdquStore m x
  | .y32, m, x => .vmovdquStore .l256 m x
  | .z64, m, x => .vmovdqu32Store m x

/-- 16 bytes: SSE2's `movdqu`, or, after a wider copy may have dirtied the
upper halves, AVX's `vmovdqu` of `xmm`. -/
def ld16 : Width → XReg → MemOp → Instr
  | .x16, x, m => .movdquLoad x m
  | _, x, m => .vmovdquLoad .l128 x m
def st16 : Width → MemOp → XReg → Instr
  | .x16, m, x => .movdquStore m x
  | _, m, x => .vmovdquStore .l128 m x

/-- Bytes `[0, c)` and `[rcx - c, rcx)` (overlapping, for `c ≤ rcx ≤ 2 c`),
`c` the width of the loads `ld` and stores `st` given, through `xmm0` and
`xmm1`. -/
def pairX (c : Nat) (ld : XReg → MemOp → Instr) (st : MemOp → XReg → Instr) : List Instr :=
  [ld .xmm0 (at_ .rsi 0), ld .xmm1 (at2 .rsi .rcx (-(c : Int))),
   st (at_ .rdi 0) .xmm0, st (at2 .rdi .rcx (-(c : Int))) .xmm1]

/-- The same for 8 bytes, through `rax` and `r8`. -/
def pair8 : List Instr :=
  [.mov .rax (.mem (at_ .rsi 0)), .mov .r8 (.mem (at2 .rsi .rcx (-8))),
   .store (at_ .rdi 0) .rax, .store (at2 .rdi .rcx (-8)) .r8]

/-- The same for 4 bytes. -/
def pair4 : List Instr :=
  [.mov32 .rax (.mem (at_ .rsi 0)), .mov32 .r8 (.mem (at2 .rsi .rcx (-4))),
   .store32 (at_ .rdi 0) .rax, .store32 (at2 .rdi .rcx (-4)) .r8]

/-- The bytes from `r10` to `rcx`, one at a time. -/
def copyTail : Prog isa :=
  .seq (.block [.alu .cmp .r10 (.reg .rcx)])
    (.ite .e (.block [])
      (.loop (.block [.movzx8 .rax srcB, .store8 dstB .rax, .alu .add .r10 (imm 1), .alu .cmp .r10 (.reg .rcx)])
        .ne))

/-- Fewer than 4 bytes, one at a time. -/
def copyFew : Prog isa := .seq (.block [.mov32 .r10 (imm 0)]) copyTail

/-- `rcx < c₂` bytes: `rcx ≥ c₁` with `pair`, else `rest`. -/
def ladderStep (c : Nat) (pair : List Instr) (rest : Prog isa) : Prog isa :=
  .seq (.block [.alu .cmp .rcx (imm c)]) (.ite .b rest (.block pair))

/-- Fewer than 16 bytes. -/
def ladder16 : Prog isa := ladderStep 8 pair8 (ladderStep 4 pair4 copyFew)

/-- Fewer than `2 ^ (w.log + 1)` bytes: two overlapping copies of the
largest width at most `rcx`. -/
def ladder32 : Prog isa :=
  ladderStep 32 (pairX 32 (ldW .y32) (stW .y32)) (ladderStep 16 (pairX 16 (ld16 .y32) (st16 .y32)) ladder16)

def ladder : Width → Prog isa
  | .x16 => ladderStep 16 (pairX 16 (ld16 .x16) (st16 .x16)) ladder16
  | .y32 => ladder32
  | .z64 => ladderStep 64 (pairX 64 (ldW .z64) (stW .z64)) ladder32

/-- Bytes `[r10 + d, r10 + d + 2 c)` from `rsi` to `rdi`, `c = 2 ^ w.log`,
through `xmm0` and `xmm1`. -/
def quadAt (w : Width) (i : Reg) (d : Int) : List Instr :=
  [ldW w .xmm0 (at2 .rsi i d), ldW w .xmm1 (at2 .rsi i (d + 2 ^ w.log)),
   stW w (at2 .rdi i d) .xmm0, stW w (at2 .rdi i (d + 2 ^ w.log)) .xmm1]

/-- At least `2 c` bytes, `c = 2 ^ w.log`: the first `c`; then `2 c` at a
time from the first offset at which the stores are aligned (`r10`, below
`c`), while `2 c` remain (to `r8 = rcx - 2 c`; `CF` clear while
`r10 ≤ r8`); then the last `2 c`. -/
def big (w : Width) : Prog isa :=
  .seq (.block [ldW w .xmm0 (at_ .rsi 0), stW w (at_ .rdi 0) .xmm0])
  (.seq (.block [.mov32 .r10 (imm 0), .alu .sub .r10 (.reg .rdi), .alu .and .r10 (imm (2 ^ w.log - 1)),
    .mov .r8 (.reg .rcx), .alu .sub .r8 (imm (2 * 2 ^ w.log)), .alu .cmp .r8 (.reg .r10)])
  (.seq (.ite .b (.block [])
    (.loop (.seq (.block (quadAt w .r10 0))
      (.block [.alu .add .r10 (imm (2 * 2 ^ w.log)), .alu .cmp .r8 (.reg .r10)])) .ae))
    (.block (quadAt w .rcx (-(2 * 2 ^ w.log : Nat))))))

/-- Copies the `rcx` bytes at `rsi` to `rdi`: with at least `2 c` bytes,
`c = 2 ^ w.log`, by `big`, else by `ladder`; every byte is stored with its
own value, some twice. After a wider copy, `vzeroupper`. -/
def copyBytes (w : Width) : Prog isa :=
  .seq (.block [.alu .cmp .rcx (imm (2 * 2 ^ w.log))])
  (.seq (.ite .b (ladder w) (big w))
    (match w with
      | .x16 => .block []
      | _ => .block [.vop .vzeroupper]))

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
