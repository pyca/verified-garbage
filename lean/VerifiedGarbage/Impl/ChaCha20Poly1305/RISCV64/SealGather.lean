module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.RISCV64
public import VerifiedGarbage.Impl.Gather.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices: RISC-V implementation

`vg_chacha20_poly1305_seal_gather(key = a0, nonce = a1, aad = a2,
aad_len = a3, src = a4, src_count = a5, dst = a6, len = a7, tag)`, its ninth
argument `tag` in memory (RISC-V psABI, "Integer Calling Convention": on the
stack, at `sp` on entry): it copies the slices `src` lists, one after the
other, to `dst` (`Impl/Gather/RISCV64.lean`, whose registers `src`,
`src_count` and `dst` already are), and encrypts them there in place with a
call of `vg_chacha20_poly1305_seal(key, nonce, aad, aad_len, dst, len, tag)`.

It saves our return address, which the call overwrites, in a frame of 16
bytes (`push`), so `tag` is then at `sp + 16`. The gathering writes only
`t0`–`t4` and `a4`–`a6`: `key`, `nonce`, `aad`, `aad_len` and `len` wait for
the call where they are, `dst` in `t6` and `tag` in `t5`.
-/

@[expose] public section

namespace VG.Impl.ChaCha20Poly1305.RISCV64.SealGather

open VG.RISCV64
open VG.Impl.ChaCha20.RISCV64.Xor (mov)

/-- `vg_chacha20_poly1305_seal`, in its frame. -/
def sealCode : Prog isa :=
  Impl.StackScratch.RISCV64.withStackScratchWiped 624 .a7 77 Impl.ChaCha20Poly1305.RISCV64.«seal»

/-- `tag` into `t5`, from the stack above our frame, and `dst` into `t6`. -/
def entry : List Instr := [.addSp .t5 16, .load .d .t5 .t5 0, mov .t6 .a6]

/-- The call's arguments: `dst`, `len` and `tag`. -/
def callArgs : List Instr := [mov .a4 .t6, mov .a5 .a7, mov .a6 .t5]

/-- `vg_chacha20_poly1305_seal_gather`. -/
def sealGather : Prog isa :=
  .frame (.push .ra)
    (.seq (.block entry)
    (.seq Gather.RISCV64.gather
    (.seq (.block callArgs)
      (.call "vg_chacha20_poly1305_seal" sealCode))))
    (.pop .ra)

end VG.Impl.ChaCha20Poly1305.RISCV64.SealGather
