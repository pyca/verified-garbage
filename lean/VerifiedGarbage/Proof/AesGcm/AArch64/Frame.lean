import VerifiedGarbage.Proof.AesGcm.AArch64.Verified
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch

/-!
# AES-GCM's key setup and streaming start on AArch64, with their working space on the stack

`init`, `stream_init` and `stream_aad` run their code, proved with the
working space as an argument (`Verified.lean`), in a frame of 2560 bytes that
allocates it (`Verified.stackScratch`).
-/

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64

/-- A state satisfying `vg_aes_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Gcm.initContract AArch64.abi 2560).pre s := by
  implies_sat [Spec.Gcm.initContract, Spec.Gcm.initSig, Spec.Gcm.initPre, Spec.Gcm.initPost,
    AArch64.abi, AArch64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed (v : GcmImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratch 2560 .x3 (init v.callees))
      (Spec.Gcm.initContract AArch64.abi 2560) :=
  AArch64.Verified.stackScratch (sig := Spec.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.initPre AArch64.abi.ptrBits) (post := Spec.Gcm.initPost AArch64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2560) (init_verified v) (by decide) (by decide)
    initFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition, without the
working space. -/
def streamInitFrameSat : State := { streamInitSat with wr := [⟨0x3000, 80⟩] }

theorem streamInitFrameSat_pre : ∃ s, (Spec.Gcm.streamInitContract AArch64.abi 2560).pre s := by
  implies_sat [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, Spec.Gcm.streamInitPost,
    AArch64.abi, AArch64.argRegs] [streamInitFrameSat, streamInitSat] using streamInitFrameSat

theorem streamInit_framed (v : GcmImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 2560 .x4 (streamInit v.callees))
      (Spec.Gcm.streamInitContract AArch64.abi 2560) :=
  AArch64.Verified.stackScratch (sig := Spec.Gcm.streamInitSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamInitPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2560) (streamInit_verified v) (by decide) (by decide) streamInitFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition, without the
working space. -/
def streamAadFrameSat : State := { streamAadSat with wr := [⟨0x3000, 80⟩] }

theorem streamAadFrameSat_pre : ∃ s, (Spec.Gcm.streamAadContract AArch64.abi 2560).pre s := by
  implies_sat [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, Spec.Gcm.streamAadPost,
    AArch64.abi, AArch64.argRegs] [streamAadFrameSat, streamAadSat] using streamAadFrameSat

theorem streamAad_framed (v : GcmImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratch 2560 .x5 (streamAad v.callees))
      (Spec.Gcm.streamAadContract AArch64.abi 2560) :=
  AArch64.Verified.stackScratch (sig := Spec.Gcm.streamAadSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamAadPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2560) (streamAad_verified v) (by decide) (by decide) streamAadFrameSat_pre

end VG.Proof.AesGcm.AArch64
