import VerifiedGarbage.Proof.AesGcm.X86_64.Verified
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/-!
# AES-GCM's key setup and streaming start on x86-64, with their working space on the stack

`init`, `stream_init` and `stream_aad` run their code, proved with the
working space as an argument (`Verified.lean`), in a frame of 2568 bytes that
allocates it (`Verified.stackScratch`): the 2560 bytes of working space, and
8 more to keep `rsp` aligned. Their own calls use 8 bytes below it, the
return address, as `vg_aes_expand_key`, `vg_aes_ctr32` and `vg_ghash` use no
stack (`KeyImpl.noStack`, `Ctr32Impl.noStack`, `GhashImpl.noStack`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64

variable (v : GcmImpl)

theorem init_xdepth : (init v.callees).x86_64Depth ≤ 8 := by
  simp only [init, streamInit, streamAad, ghash1, absorbHead, absorbWhole, absorbTail, absorb,
    flush, lens, j0hash, j0, firstFlush, oneAad, Code.x86_64Depth, GcmImpl.callees, v.ctr.noStack,
    v.key.noStack, v.gh.noStack, Nat.max_le]
  decide +kernel

theorem streamInit_xdepth : (streamInit v.callees).x86_64Depth ≤ 8 := by
  simp only [init, streamInit, streamAad, ghash1, absorbHead, absorbWhole, absorbTail, absorb,
    flush, lens, j0hash, j0, firstFlush, oneAad, Code.x86_64Depth, GcmImpl.callees, v.ctr.noStack,
    v.key.noStack, v.gh.noStack, Nat.max_le]
  decide +kernel

theorem streamAad_xdepth : (streamAad v.callees).x86_64Depth ≤ 8 := by
  simp only [init, streamInit, streamAad, ghash1, absorbHead, absorbWhole, absorbTail, absorb,
    flush, lens, j0hash, j0, firstFlush, oneAad, Code.x86_64Depth, GcmImpl.callees, v.ctr.noStack,
    v.key.noStack, v.gh.noStack, Nat.max_le]
  decide +kernel

/-- A state satisfying `vg_aes_gcm_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Gcm.initContract X86_64.abi 2576).pre s := by
  implies_sat [Spec.Gcm.initContract, Spec.Gcm.initSig, Spec.Gcm.initPre, Spec.Gcm.initPost,
    X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (init v.callees))
      (Spec.Gcm.initContract X86_64.abi 2576) :=
  X86_64.Verified.stackScratch (sig := Spec.Gcm.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.initPre X86_64.abi.ptrBits) (post := Spec.Gcm.initPost X86_64.abi.ptrBits)
    (wa := true) (stack := 8) (bytes := 2568) (init_verified v) (by decide) (by decide)
    (by decide) (init_spSafe v) (init_xdepth v) initFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_init`'s precondition, without the
working space. -/
def streamInitFrameSat : State := { siSat with wr := [⟨0x3000, 80⟩] }

theorem streamInitFrameSat_pre : ∃ s, (Spec.Gcm.streamInitContract X86_64.abi 2576).pre s := by
  implies_sat [Spec.Gcm.streamInitContract, Spec.Gcm.streamInitSig, Spec.Gcm.streamInitPost,
    X86_64.abi, X86_64.argRegs] [streamInitFrameSat, siSat] using streamInitFrameSat

theorem streamInit_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 2568 .r8 (streamInit v.callees))
      (Spec.Gcm.streamInitContract X86_64.abi 2576) :=
  X86_64.Verified.stackScratch (sig := Spec.Gcm.streamInitSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamInitPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 2568) (streamInit_verified v) (by decide) (by decide) (by decide)
    (streamInit_spSafe v) (streamInit_xdepth v) streamInitFrameSat_pre

/-- A state satisfying `vg_aes_gcm_stream_aad`'s precondition, without the
working space. -/
def streamAadFrameSat : State := { saSat with wr := [⟨0x3000, 80⟩] }

theorem streamAadFrameSat_pre : ∃ s, (Spec.Gcm.streamAadContract X86_64.abi 2576).pre s := by
  implies_sat [Spec.Gcm.streamAadContract, Spec.Gcm.streamAadSig, Spec.Gcm.streamAadPost,
    X86_64.abi, X86_64.argRegs] [streamAadFrameSat, saSat] using streamAadFrameSat

theorem streamAad_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 2568 .r9 (streamAad v.callees))
      (Spec.Gcm.streamAadContract X86_64.abi 2576) :=
  X86_64.Verified.stackScratch (sig := Spec.Gcm.streamAadSig) (nm := "scratch") (e := .u64)
    (n := 320) (post := Spec.Gcm.streamAadPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 2568) (streamAad_verified v) (by decide) (by decide) (by decide)
    (streamAad_spSafe v) (streamAad_xdepth v) streamAadFrameSat_pre

end VG.Proof.AesGcm.X86_64
