module

public import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Verified
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.CmacAes.Stream.Scratch

/-!
# Streaming AES-CMAC on x86-64, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame of 2312 bytes that allocates it
(`Verified.stackScratch`): the 2304 bytes of working space, and 8 more to
keep `rsp` aligned. Their own calls use at most 16 bytes below it: two
return addresses, as `vg_aes_ctr32` and `vg_aes_expand_key_scratch` use no
stack (and `vg_cmac_aes_update_aesni` none at all). Over implementations of
AES that need no working space, `init` (`initF`) needs only 152 bytes of it,
in a frame of 168 (`initF_framed`). Over implementations that never touch
the first 512 bytes of the working space (the bitsliced AES, which uses 1480
bytes of its own, 512 bytes into it), the functions (`initS`, `absorbS`,
`finishS`) need 1792 bytes, in a frame of 1800 (`initS_framed`,
`absorbS_framed`, `finishS_framed`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.Impl.CmacAes.Stream.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl UpdateFree)

theorem init_xdepth (v : Ctr32Impl) : (init v.expand v.callee v.suffix).x86_64Depth ≤ 16 := by
  simp only [init, Impl.CmacAes.X86_64.subkeys, Code.x86_64Depth, ekCall_xdepth,
    Proof.CmacAes.X86_64.ctrCall_xdepth, v.noStack, v.expandNoStack]
  decide +kernel

theorem initS_xdepth (v : Ctr32Impl) : (initS v.expand v.callee v.suffix).x86_64Depth ≤ 16 := by
  have := init_xdepth v
  simp only [initS, Code.x86_64Depth, Nat.max_le]
  omega

theorem initF_xdepth (v : Ctr32Impl) : (initF ekF v.callee v.suffix).x86_64Depth ≤ 16 := by
  have h : ekF.code.x86_64Depth = 0 := Ctr32Impl.aesni.expandNoStack
  simp only [initF, init, Impl.CmacAes.X86_64.subkeys, Code.x86_64Depth, ekCall_xdepth,
    Proof.CmacAes.X86_64.ctrCall_xdepth, v.noStack, h]
  decide +kernel

theorem absorb_xdepth (v : UpdateImpl) : (absorb v.callee).x86_64Depth ≤ 16 := by
  have := v.xdepth
  simp only [absorb, absorbPre, absorbPost, held, fill, copy, chain1, chain2, Code.x86_64Depth, Nat.max_le]
  omega_using [this]

theorem absorbF_xdepth (v : UpdateImpl) : (absorbF v.callee).x86_64Depth ≤ 16 := by
  have := absorb_xdepth v
  simp only [absorbF, Code.x86_64Depth, Nat.max_le]
  omega

theorem absorbS_xdepth (v : UpdateImpl) : (absorbS v.callee).x86_64Depth ≤ 16 := by
  have := absorb_xdepth v
  simp only [absorbS, Code.x86_64Depth, Nat.max_le]
  omega

theorem finish_xdepth (v : Ctr32Impl) : (finish v.callee v.suffix).x86_64Depth ≤ 16 := by
  simp only [finish, finPre, lastLen, Impl.CmacAes.X86_64.finalize, Code.x86_64Depth,
    Proof.CmacAes.X86_64.ctrCall_xdepth, v.noStack]
  decide +kernel

theorem finishS_xdepth (v : Ctr32Impl) : (finishS v.callee v.suffix).x86_64Depth ≤ 16 := by
  have := finish_xdepth v
  simp only [finishS, Code.x86_64Depth, Nat.max_le]
  omega

theorem finishF_xdepth (v : Ctr32Impl) : (finishF v.callee v.suffix).x86_64Depth ≤ 16 := by
  simp only [finishF, finPreF, lastLen, Impl.CmacAes.X86_64.finalize, Code.x86_64Depth,
    Proof.CmacAes.X86_64.ctrCall_xdepth, v.noStack]
  decide +kernel

/-- A state satisfying `vg_cmac_aes_init`'s precondition, without the
working space. -/
def initFrameSat : State := { initSat with wr := [⟨0x1000, 304⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.aesInitContract X86_64.abi 2328).pre s := by
  implies_sat [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, Spec.Cmac.aesInitPre,
    Spec.Cmac.aesInitPost, X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem initFrameSatF_pre : ∃ s, (Spec.Cmac.aesInitContract X86_64.abi 184).pre s := by
  implies_sat [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, Spec.Cmac.aesInitPre,
    Spec.Cmac.aesInitPost, X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem initFrameSatS_pre : ∃ s, (Spec.Cmac.aesInitContract X86_64.abi 1816).pre s := by
  implies_sat [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, Spec.Cmac.aesInitPre,
    Spec.Cmac.aesInitPost, X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition, without the
working space (and with no data). -/
def absorbFrameSat : State := { absorbSat with wr := [⟨0x1000, 304⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.aesAbsorbContract X86_64.abi 2328).pre s := by
  implies_sat [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, Spec.Cmac.aesAbsorbPre,
    Spec.Cmac.aesAbsorbPost, X86_64.abi, X86_64.argRegs] [absorbFrameSat, absorbSat]
    using absorbFrameSat

theorem absorbFrameSatF_pre : ∃ s, (Spec.Cmac.aesAbsorbContract X86_64.abi 72).pre s := by
  implies_sat [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, Spec.Cmac.aesAbsorbPre,
    Spec.Cmac.aesAbsorbPost, X86_64.abi, X86_64.argRegs] [absorbFrameSat, absorbSat]
    using absorbFrameSat

theorem absorbFrameSatS_pre : ∃ s, (Spec.Cmac.aesAbsorbContract X86_64.abi 1816).pre s := by
  implies_sat [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, Spec.Cmac.aesAbsorbPre,
    Spec.Cmac.aesAbsorbPost, X86_64.abi, X86_64.argRegs] [absorbFrameSat, absorbSat]
    using absorbFrameSat

/-- A state satisfying `vg_cmac_aes_finish`'s precondition, without the
working space. -/
def finishFrameSat : State := { finishSat with wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.aesFinishContract X86_64.abi 2328).pre s := by
  implies_sat [Spec.Cmac.aesFinishContract, Spec.Cmac.aesFinishSig, Spec.Cmac.aesFinishPre,
    Spec.Cmac.aesFinishPost, X86_64.abi, X86_64.argRegs] [finishFrameSat, finishSat]
    using finishFrameSat

theorem finishFrameSatF_pre : ∃ s, (Spec.Cmac.aesFinishContract X86_64.abi 40).pre s := by
  implies_sat [Spec.Cmac.aesFinishContract, Spec.Cmac.aesFinishSig, Spec.Cmac.aesFinishPre,
    Spec.Cmac.aesFinishPost, X86_64.abi, X86_64.argRegs] [finishFrameSat, finishSat]
    using finishFrameSat

theorem finishFrameSatS_pre : ∃ s, (Spec.Cmac.aesFinishContract X86_64.abi 1816).pre s := by
  implies_sat [Spec.Cmac.aesFinishContract, Spec.Cmac.aesFinishSig, Spec.Cmac.aesFinishPre,
    Spec.Cmac.aesFinishPost, X86_64.abi, X86_64.argRegs] [finishFrameSat, finishSat]
    using finishFrameSat

theorem init_framed (v : Ctr32Impl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 2312 .rcx (init v.expand v.callee v.suffix))
      (Spec.Cmac.aesInitContract X86_64.abi 2328) :=
  X86_64.Verified.stackScratch (hpostOut := Proof.CmacAes.Stream.initPostOut_local _) (sig := Spec.Cmac.aesInitSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesInitPre X86_64.abi.ptrBits)
    (post := Spec.Cmac.aesInitPost X86_64.abi.ptrBits) (wa := false) (stack := 16) (bytes := 2312)
    (init_verified v) (by decide) (by decide) (by decide) (init_spSafe v) (init_xdepth v)
    initFrameSat_pre

/-- `init_framed`, over implementations of AES that need no working space
(`initF`): a frame of the 152 bytes from `vg_cmac_aes_subkeys`'s counter
block to the end of our saved registers, and 16 more to keep `rsp` aligned. -/
theorem initF_framed (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 168 .rcx (initF ekF v.callee v.suffix))
      (Spec.Cmac.aesInitContract X86_64.abi 184) :=
  X86_64.Verified.stackScratch (hpostOut := Proof.CmacAes.Stream.initPostOut_local _) (sig := Spec.Cmac.aesInitSig) (nm := "scratch") (e := .u64)
    (n := 19) (pre := Spec.Cmac.aesInitPre X86_64.abi.ptrBits)
    (post := Spec.Cmac.aesInitPost X86_64.abi.ptrBits) (wa := false) (stack := 16) (bytes := 168)
    (initF_verified v f) (by decide) (by decide) (by decide) (initF_spSafe v) (initF_xdepth v)
    initFrameSatF_pre

/-- `init_framed`, over an implementation of AES that never touches the
first 512 bytes of the working space (`initS`): a frame 512 bytes smaller. -/
theorem initS_framed (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Small v.callee) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 1800 .rcx (initS v.expand v.callee v.suffix))
      (Spec.Cmac.aesInitContract X86_64.abi 1816) :=
  X86_64.Verified.stackScratch (hpostOut := Proof.CmacAes.Stream.initPostOut_local _) (sig := Spec.Cmac.aesInitSig) (nm := "scratch") (e := .u64)
    (n := 224) (pre := Spec.Cmac.aesInitPre X86_64.abi.ptrBits)
    (post := Spec.Cmac.aesInitPost X86_64.abi.ptrBits) (wa := false) (stack := 16) (bytes := 1800)
    (initS_verified v f) (by decide) (by decide) (by decide) (initS_spSafe v) (initS_xdepth v)
    initFrameSatS_pre

theorem absorb_framed (v : UpdateImpl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 2312 .r9 (absorb v.callee))
      (Spec.Cmac.aesAbsorbContract X86_64.abi 2328) :=
  X86_64.Verified.stackScratch (hpostOut := Proof.CmacAes.Stream.absorbPostOut_local _) (sig := Spec.Cmac.aesAbsorbSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesAbsorbPre X86_64.abi.ptrBits)
    (post := Spec.Cmac.aesAbsorbPost X86_64.abi.ptrBits) (wa := false) (stack := 16)
    (bytes := 2312) (absorb_verified v) (by decide) (by decide) (by decide) (absorb_spSafe v)
    (absorb_xdepth v) absorbFrameSat_pre

/-- `absorb_framed`, over an implementation of `vg_cmac_aes_update` that
needs no working space (`absorbF`): a frame of the 48 bytes of the registers
saved, after the 8 that stand for the return address. -/
theorem absorbF_framed (v : UpdateImpl) (f : UpdateFree v.callee) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 56 .r9 (absorbF v.callee))
      (Spec.Cmac.aesAbsorbContract X86_64.abi 72) :=
  X86_64.Verified.stackScratch (hpostOut := Proof.CmacAes.Stream.absorbPostOut_local _) (sig := Spec.Cmac.aesAbsorbSig) (nm := "scratch") (e := .u64)
    (n := 6) (pre := Spec.Cmac.aesAbsorbPre X86_64.abi.ptrBits)
    (post := Spec.Cmac.aesAbsorbPost X86_64.abi.ptrBits) (wa := false) (stack := 16)
    (bytes := 56) (absorbF_verified v f) (by decide) (by decide) (by decide) (absorbF_spSafe v)
    (absorbF_xdepth v) absorbFrameSatF_pre

/-- `absorb_framed`, over an implementation of `vg_cmac_aes_update` that
never touches the first 512 bytes of its scratch buffer (`absorbS`): a frame
512 bytes smaller. -/
theorem absorbS_framed (v : UpdateImpl) (f : Proof.CmacAes.X86_64.UpdateSmall v.callee) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 1800 .r9 (absorbS v.callee))
      (Spec.Cmac.aesAbsorbContract X86_64.abi 1816) :=
  X86_64.Verified.stackScratch (hpostOut := Proof.CmacAes.Stream.absorbPostOut_local _) (sig := Spec.Cmac.aesAbsorbSig) (nm := "scratch") (e := .u64)
    (n := 224) (pre := Spec.Cmac.aesAbsorbPre X86_64.abi.ptrBits)
    (post := Spec.Cmac.aesAbsorbPost X86_64.abi.ptrBits) (wa := false) (stack := 16)
    (bytes := 1800) (absorbS_verified v f) (by decide) (by decide) (by decide) (absorbS_spSafe v)
    (absorbS_xdepth v) absorbFrameSatS_pre

theorem finish_framed (v : Ctr32Impl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 2312 .r8 (finish v.callee v.suffix))
      (Spec.Cmac.aesFinishContract X86_64.abi 2328) :=
  X86_64.Verified.stackScratch (hpostOut := Proof.CmacAes.Stream.finishPostOut_local _) (sig := Spec.Cmac.aesFinishSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesFinishPre X86_64.abi.ptrBits)
    (post := Spec.Cmac.aesFinishPost X86_64.abi.ptrBits) (wa := false) (stack := 16)
    (bytes := 2312) (finish_verified v) (by decide) (by decide) (by decide) (finish_spSafe v)
    (finish_xdepth v) finishFrameSat_pre

/-- `finish_framed`, over an implementation of `vg_aes_ctr32` that needs no
working space: a frame of the 16 bytes of `vg_cmac_aes_finalize`'s counter
block, after the 8 that stand for the return address. -/
theorem finishF_framed (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 24 .r8 (finishF v.callee v.suffix))
      (Spec.Cmac.aesFinishContract X86_64.abi 40) :=
  X86_64.Verified.stackScratch (hpostOut := Proof.CmacAes.Stream.finishPostOut_local _) (sig := Spec.Cmac.aesFinishSig) (nm := "scratch") (e := .u64)
    (n := 2) (pre := Spec.Cmac.aesFinishPre X86_64.abi.ptrBits)
    (post := Spec.Cmac.aesFinishPost X86_64.abi.ptrBits) (wa := false) (stack := 16)
    (bytes := 24) (finishF_verified v f) (by decide) (by decide) (by decide) (finishF_spSafe v)
    (finishF_xdepth v) finishFrameSatF_pre

/-- `finish_framed`, over an implementation of `vg_aes_ctr32` that never
touches the first 512 bytes of the working space (`finishS`): a frame 512
bytes smaller. -/
theorem finishS_framed (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Small v.callee) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 1800 .r8 (finishS v.callee v.suffix))
      (Spec.Cmac.aesFinishContract X86_64.abi 1816) :=
  X86_64.Verified.stackScratch (hpostOut := Proof.CmacAes.Stream.finishPostOut_local _) (sig := Spec.Cmac.aesFinishSig) (nm := "scratch") (e := .u64)
    (n := 224) (pre := Spec.Cmac.aesFinishPre X86_64.abi.ptrBits)
    (post := Spec.Cmac.aesFinishPost X86_64.abi.ptrBits) (wa := false) (stack := 16)
    (bytes := 1800) (finishS_verified v f) (by decide) (by decide) (by decide) (finishS_spSafe v)
    (finishS_xdepth v) finishFrameSatS_pre

end VG.Proof.CmacAes.Stream.X86_64
