module

public import VerifiedGarbage.Impl.Aes.RISCV64.Ctr32
public import VerifiedGarbage.Impl.Gcm.RISCV64
public import VerifiedGarbage.Impl.Words.RISCV64.CopyFast

/-!
# AES-GCM's bitsliced key: RISC-V implementation

`vg_aes_gcm_bitslice(ctx = a0, bk = a1, scratch = a2)`, the body that
`withStackScratch` gives a working space of 2048 bytes: the buffer of
`Spec/Gcm/Bitsliced.lean` from the key context, with the code of
`vg_aes_ctr32` and `vg_ghash` that computes it at every call.

* `vg_aes_ctr32`'s prologue (`Impl/Aes/RISCV64/Ctr32.lean`): the working
  space rounded up to a multiple of 8, our caller's `s0`–`s11` saved in
  slots 40–51, the masks of the linear layers built; then its key loop, for
  14 rounds, bitslices the 15 blocks of the key context's first 240 bytes,
  block `j` to byte `1024 + 64 j` of the working space (`keySetup`, with
  `a1 = 14`; `a3` and `a4` keep `ctx` and `bk`, which the loop does not
  write).
* Those 960 bytes are copied to `bk`, a doubleword at a time (`copyLoopW`:
  the working space, rounded, and `bk`, an array of `u64`, are both 8-byte
  aligned).
* `vg_ghash`'s `prep`, with the hash subkey at `ctx + 240` (`HP`) and its
  frame pointer (`FP`) at `bk + 960`, writes its 36 doublewords there.
* Our caller's registers are restored.

Only the pointers can affect timing: there is no branch but the loops' on
their counters, and every address is the pointers' plus a constant or a
counter.
-/

@[expose] public section

namespace VG.Impl.AesGcm.RISCV64.Bitslice

open VG.RISCV64 VG.Impl.Aes.RISCV64

/-- The working space into `a5`, rounded; our caller's registers saved; the
masks built; `ctx` and `bk` kept in `a3` and `a4`; and the key loop set up
for 14 rounds. -/
def entry : List Instr :=
  ([.addi .a5 .a2 0] : List Instr) ++ roundSb ++ saveRegs ++ maskInit ++
    ([.addi .a3 .a0 0, .addi .a4 .a1 0, .li .a1 14] : List Instr) ++ keySetup

/-- The 120 doublewords of bitsliced blocks, at byte 1024 of the working
space, to `bk`. -/
def copyArgs : List Instr := [.addi .a0 .a5 1024, .addi .a1 .a4 0, .li .a2 120]

/-- The hash subkey (`HP`) and the frame (`FP`) of `prep`. -/
def ghArgs : List Instr := [.addi .a0 .a3 240, .addi .s9 .a4 960]

def bitslice : Prog isa :=
  .seq (.block entry)
  (.seq (.loop (.block keyBody) (.nonzero .a1))
  (.seq (.block copyArgs)
  (.seq (Impl.Words.RISCV64.copyLoopW .t0 .a0 .a1 .a2)
    (.block (ghArgs ++ Impl.Gcm.RISCV64.prep ++ restoreRegs)))))

end VG.Impl.AesGcm.RISCV64.Bitslice
