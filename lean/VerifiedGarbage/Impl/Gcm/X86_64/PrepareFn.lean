module

public import VerifiedGarbage.Impl.Gcm.X86_64.Flag
public import VerifiedGarbage.Impl.Gcm.X86_64.PrepareZ
public import VerifiedGarbage.Impl.Gcm.X86_64.Prepare16
public import VerifiedGarbage.Impl.Gcm.X86_64.PrepareAvx
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-! # Preparing AES-GCM's key context on x86-64: the functions as emitted

Each implementation of `vg_aes_gcm_prepare` and `vg_aes_gcm_wipe_prepared`,
then its cleanup (`Impl.Scrub.X86_64.scrubAll v 0 0`): every vector register
at the level `v` and every caller-saved register cleared. None has stack.
-/

@[expose] public section

namespace VG.Impl.Gcm.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubAll)

/-- `vg_aes_gcm_prepare_vpclmul_avx512` as emitted. -/
def prepareZ : Prog isa := scrubAll .avx 0 0 (Impl.Gcm.X86_64.Flag.prepareFlagged 48 Impl.Gcm.X86_64.PrepareZ.prepare)

/-- `vg_aes_gcm_prepare_vpclmul` as emitted. -/
def prepare16 : Prog isa :=
  scrubAll .avx 0 0 (Impl.Gcm.X86_64.Flag.prepareFlagged 16 Impl.Gcm.X86_64.Prepare16.prepare16)

/-- `vg_aes_gcm_prepare_pclmul_avx` as emitted. -/
def prepareAvx : Prog isa :=
  scrubAll .avx 0 0 (Impl.Gcm.X86_64.Flag.prepareFlagged 16 Impl.Gcm.X86_64.PrepareAvx.prepare16)

/-- `vg_aes_gcm_prepare` as emitted. -/
def prepareAbsent : Prog isa := scrubAll .sse 0 0 Impl.Gcm.X86_64.Flag.prepareAbsent

/-- `vg_aes_gcm_wipe_prepared` as emitted, with AVX if `avx`. -/
def wipe (avx : Bool) : Prog isa := scrubAll (if avx then .avx else .sse) 0 0 (Impl.Gcm.X86_64.Flag.wipe avx)

end VG.Impl.Gcm.X86_64.Fn
