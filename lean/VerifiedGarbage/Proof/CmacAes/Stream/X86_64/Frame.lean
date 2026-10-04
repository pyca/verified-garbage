import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Verified
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/-!
# Streaming AES-CMAC on x86-64, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame of 2312 bytes that allocates it
(`Verified.stackScratch`): the 2304 bytes of working space, and 8 more to
keep `rsp` aligned. Their own calls use 16 bytes below it: two return
addresses, as `vg_aes_ctr32` and `vg_aes_expand_key` use no stack.
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64 VG.Impl.CmacAes.Stream.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

theorem init_xdepth (v : Ctr32Impl) : (init v.expand v.callee v.suffix).x86_64Depth ≤ 16 := by
  simp only [init, Impl.CmacAes.X86_64.subkeys, Code.x86_64Depth, v.noStack, v.expandNoStack]
  decide +kernel

theorem absorb_xdepth (v : Ctr32Impl) : (absorb v.callee v.suffix).x86_64Depth ≤ 16 := by
  simp only [absorb, absorbPre, absorbPost, held, fill, copy, chain1, chain2,
    Impl.CmacAes.X86_64.update, Impl.CmacAes.X86_64.body, Code.x86_64Depth, v.noStack]
  decide +kernel

theorem finish_xdepth (v : Ctr32Impl) : (finish v.callee v.suffix).x86_64Depth ≤ 16 := by
  simp only [finish, finPre, lastLen, Impl.CmacAes.X86_64.finalize, Code.x86_64Depth, v.noStack]
  decide +kernel

/-- A state satisfying `vg_cmac_aes_init`'s precondition, without the
working space. -/
def initFrameSat : State := { initSat with wr := [⟨0x1000, 304⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.aesInitContract X86_64.abi 2328).pre s := by
  implies_sat [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, Spec.Cmac.aesInitPre,
    Spec.Cmac.aesInitPost, X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition, without the
working space (and with no data). -/
def absorbFrameSat : State := { absorbSat with wr := [⟨0x1000, 304⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.aesAbsorbContract X86_64.abi 2328).pre s := by
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

theorem init_framed (v : Ctr32Impl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 2312 .rcx (init v.expand v.callee v.suffix))
      (Spec.Cmac.aesInitContract X86_64.abi 2328) :=
  X86_64.Verified.stackScratch (sig := Spec.Cmac.aesInitSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesInitPre X86_64.abi.ptrBits)
    (post := Spec.Cmac.aesInitPost X86_64.abi.ptrBits) (wa := false) (stack := 16) (bytes := 2312)
    (init_verified v) (by decide) (by decide) (by decide) (init_spSafe v) (init_xdepth v)
    initFrameSat_pre

theorem absorb_framed (v : Ctr32Impl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 2312 .r9 (absorb v.callee v.suffix))
      (Spec.Cmac.aesAbsorbContract X86_64.abi 2328) :=
  X86_64.Verified.stackScratch (sig := Spec.Cmac.aesAbsorbSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesAbsorbPre X86_64.abi.ptrBits)
    (post := Spec.Cmac.aesAbsorbPost X86_64.abi.ptrBits) (wa := false) (stack := 16)
    (bytes := 2312) (absorb_verified v) (by decide) (by decide) (by decide) (absorb_spSafe v)
    (absorb_xdepth v) absorbFrameSat_pre

theorem finish_framed (v : Ctr32Impl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 2312 .r8 (finish v.callee v.suffix))
      (Spec.Cmac.aesFinishContract X86_64.abi 2328) :=
  X86_64.Verified.stackScratch (sig := Spec.Cmac.aesFinishSig) (nm := "scratch") (e := .u64)
    (n := 288) (pre := Spec.Cmac.aesFinishPre X86_64.abi.ptrBits)
    (post := Spec.Cmac.aesFinishPost X86_64.abi.ptrBits) (wa := false) (stack := 16)
    (bytes := 2312) (finish_verified v) (by decide) (by decide) (by decide) (finish_spSafe v)
    (finish_xdepth v) finishFrameSat_pre

end VG.Proof.CmacAes.Stream.X86_64
