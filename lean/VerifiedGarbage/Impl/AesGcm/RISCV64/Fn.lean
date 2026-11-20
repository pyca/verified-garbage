module

public import VerifiedGarbage.Impl.AesGcm.RISCV64.Bitslice
public import VerifiedGarbage.Impl.AesGcm.RISCV64.OpenTo
public import VerifiedGarbage.Impl.AesGcm.RISCV64.SealGather
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# AES-GCM on RISC-V, as emitted

Each function, on its stack scratch (`Impl.StackScratch.RISCV64`), followed
by its cleanup: `vg_aes_gcm_init` by `Impl.Scrub.RISCV64.scrub`, which zeroes
the 2560 bytes of stack its frames use, and the others by
`Impl.Scrub.RISCV64.scrubSel`, which zeroes, of the stack their frames use,
only the runs of doublewords stated here, those the residue analysis
(`RISCV64.rtaint`) finds may differ between two runs: the two frames of
2048 bytes at the top of the stack they use, and the start of the innermost
frame. Both clear the caller-saved
registers but the result's bits.
-/

@[expose] public section

namespace VG.Impl.AesGcm.RISCV64.Fn

open VG.RISCV64 VG.Impl.Scrub.RISCV64 VG.Impl.StackScratch.RISCV64

/-- `vg_aes_gcm_init`, then its cleanup. -/
def init : Prog isa := scrub 0 2560 (withStackScratch 2560 .a3 Impl.AesGcm.RISCV64.init)

/-- `vg_aes_gcm_stream_init`, then its cleanup. -/
def streamInit : Prog isa :=
  scrubSel 0 [(2048, [(0, 256)]), (2048, [(0, 256)]), (112, [(0, 14)])]
    (withStackScratch 2560 .a4 Impl.AesGcm.RISCV64.streamInit)

/-- `vg_aes_gcm_stream_aad`, then its cleanup. -/
def streamAad : Prog isa :=
  scrubSel 0 [(2048, [(0, 256)]), (2048, [(0, 256)]), (112, [(0, 14)])]
    (withStackScratch 2560 .a5 Impl.AesGcm.RISCV64.streamAad)

/-- `vg_aes_gcm_bitslice`, then its cleanup. -/
def bitslice : Prog isa :=
  scrubSel 0 [(2048, [(0, 256)])] (withStackScratch 2048 .a2 Impl.AesGcm.RISCV64.Bitslice.bitslice)

/-- `vg_aes_gcm_stream_encrypt_bitsliced`, then its cleanup. -/
def streamEncryptBs : Prog isa :=
  scrubSel 0 [(2048, [(0, 256)]), (2048, [(0, 256)]), (128, [(0, 16)])]
    (withStackScratchArgs 2576 0 Impl.AesGcm.RISCV64.streamEncryptBs)

/-- `vg_aes_gcm_stream_decrypt_bitsliced`, then its cleanup. -/
def streamDecryptBs : Prog isa :=
  scrubSel 0 [(2048, [(0, 256)]), (2048, [(0, 256)]), (128, [(0, 16)])]
    (withStackScratchArgs 2576 0 Impl.AesGcm.RISCV64.streamDecryptBs)

/-- `vg_aes_gcm_stream_finish_bitsliced`, then its cleanup. -/
def streamFinishBs : Prog isa :=
  scrubSel 0 [(2048, [(0, 256)]), (2048, [(0, 256)]), (112, [(0, 14)])]
    (withStackScratch 2560 .a7 Impl.AesGcm.RISCV64.streamFinishBs)

/-- `vg_aes_gcm_stream_verify_bitsliced`, then its cleanup. -/
def streamVerifyBs : Prog isa :=
  scrubSel 32 [(2048, [(0, 256)]), (2048, [(0, 256)]), (128, [(0, 16)])]
    (withStackScratchArgs 2576 0 Impl.AesGcm.RISCV64.streamVerifyBs)

/-- `vg_aes_gcm_seal_bitsliced`, then its cleanup. -/
def sealBs : Prog isa :=
  scrubSel 0 [(2048, [(0, 256)]), (2048, [(0, 256)]), (144, [(0, 18)])]
    (withStackScratchArgs 2592 2 Impl.AesGcm.RISCV64.sealBs)

/-- `vg_aes_gcm_open_bitsliced`, then its cleanup. -/
def openBs : Prog isa :=
  scrubSel 32 [(2048, [(0, 256)]), (2048, [(0, 256)]), (144, [(0, 18)])]
    (withStackScratchArgs 2592 3 Impl.AesGcm.RISCV64.openBs)

/-- `vg_aes_gcm_open_to_bitsliced`, then its cleanup. -/
def openToBs : Prog isa :=
  scrubSel 32 [(2048, [(0, 256)]), (2048, [(0, 256)]), (160, [(0, 20)])]
    (withStackScratchArgs 2608 5 Impl.AesGcm.RISCV64.OpenTo.openToBs)

/-- `vg_aes_gcm_seal_gather_bitsliced`, then its cleanup: the frames of its
call of `vg_aes_gcm_seal_bitsliced`'s code, 32 bytes lower, below its own. -/
def sealGatherBs : Prog isa :=
  scrubSel 0 [(2048, [(0, 256)]), (2048, [(0, 256)]), (176, [(0, 22)])]
    Impl.AesGcm.RISCV64.SealGather.sealGatherBs

end VG.Impl.AesGcm.RISCV64.Fn
