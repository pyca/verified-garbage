module

public import VerifiedGarbage.Impl.Sm4Gcm.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# SM4-GCM on RISC-V, as emitted

Each function, on its stack scratch (`Impl.StackScratch.RISCV64`),
followed by its cleanup: `vg_sm4_gcm_stream_init` and `…_stream_aad`, which
are AES-GCM's code, by `Impl.Scrub.RISCV64.scrubSel`, which zeroes, of the
stack their frames use, only the runs of doublewords stated here, those the
residue analysis (`RISCV64.rtaint`) finds may differ between two runs (the
top 4208 bytes of their 4608, in nested frames of 2048, 2048 and 112 bytes); the
others by `Impl.Scrub.RISCV64.scrubAll`, which zeroes all the stack their
frames use. Both clear the caller-saved registers but the result's bits.
-/

@[expose] public section

namespace VG.Impl.Sm4Gcm.RISCV64.Fn

open VG.RISCV64 VG.Impl.Scrub.RISCV64 VG.Impl.StackScratch.RISCV64

/-- `vg_sm4_gcm_init`, then its cleanup. -/
def init : Prog isa :=
  scrubAll 0 5808 (withStackScratch 2560 .a2 VG.Impl.Sm4Gcm.RISCV64.init)

/-- `vg_sm4_gcm_seal`, then its cleanup. -/
def «seal» : Prog isa :=
  scrubAll 0 5824 (withStackScratchArgs 2576 0 VG.Impl.Sm4Gcm.RISCV64.«seal»)

/-- `vg_sm4_gcm_open`, then its cleanup. -/
def «open» : Prog isa :=
  scrubAll 32 5824 (withStackScratchArgs 2576 1 VG.Impl.Sm4Gcm.RISCV64.«open»)

/-- `vg_sm4_gcm_stream_init`, then its cleanup. -/
def streamInit : Prog isa :=
  scrubSel 0 [(2048, [(0, 256)]), (2048, [(0, 256)]), (112, [(0, 14)])]
    (withStackScratch 2560 .a4 VG.Impl.AesGcm.RISCV64.streamInit)

/-- `vg_sm4_gcm_stream_aad`, then its cleanup. -/
def streamAad : Prog isa :=
  scrubSel 0 [(2048, [(0, 256)]), (2048, [(0, 256)]), (112, [(0, 14)])]
    (withStackScratch 2560 .a5 VG.Impl.AesGcm.RISCV64.streamAad)

/-- `vg_sm4_gcm_stream_encrypt`, then its cleanup. -/
def streamEncrypt : Prog isa :=
  scrubAll 0 5808 (withStackScratch 2560 .a6 VG.Impl.Sm4Gcm.RISCV64.streamEncrypt)

/-- `vg_sm4_gcm_stream_decrypt`, then its cleanup. -/
def streamDecrypt : Prog isa :=
  scrubAll 0 5808 (withStackScratch 2560 .a6 VG.Impl.Sm4Gcm.RISCV64.streamDecrypt)

/-- `vg_sm4_gcm_stream_finish`, then its cleanup. -/
def streamFinish : Prog isa :=
  scrubAll 0 5808 (withStackScratch 2560 .a5 VG.Impl.Sm4Gcm.RISCV64.streamFinish)

/-- `vg_sm4_gcm_stream_verify`, then its cleanup. -/
def streamVerify : Prog isa :=
  scrubAll 32 5808 (withStackScratch 2560 .a6 VG.Impl.Sm4Gcm.RISCV64.streamVerify)

end VG.Impl.Sm4Gcm.RISCV64.Fn
