import VerifiedGarbage.Proof.CmacAes.Stream.X86.Verified
import VerifiedGarbage.Proof.CmacAes.Stream.Scratch
import VerifiedGarbage.Proof.Framework.X86.StackScratch

/-!
# Streaming AES-CMAC on x86, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame that allocates it and copies the
arguments passed on the stack (`Verified.stackScratch`): the return address,
the copied argument slots (three for `init`, six for `absorb`, five for
`finish`) and the 2304 bytes of working space. The copies are read only
where the pre- and postconditions read the buffers
(`Proof/CmacAes/Stream/Scratch.lean`).
-/

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86

theorem noEsp_of {c : Prog isa} (h : NoSp c) :
    c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by simp [h i hi]

variable (v : Proof.Aes.X86.Ctr32Impl)

theorem init_noEsp : (init v.expand v.callee v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [init, call4, Code.allInstrs, noEsp_of v.expandNosp,
    noEsp_of (Proof.CmacAes.X86.subkeys_nosp v)]
  decide +kernel

theorem absorb_noEsp : (absorb v.callee v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [absorb, absorbPre, absorbPost, call6, countHeld, held, fill, copy, chain1, chain2,
    Code.allInstrs, noEsp_of (Proof.CmacAes.X86.update_nosp v)]
  decide +kernel

theorem finish_noEsp : (finish v.callee v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [finish, finPre, call6, countHeld, held, Code.allInstrs,
    noEsp_of (Proof.CmacAes.X86.finalize_nosp v)]
  decide +kernel

theorem init_stackUse : stackUse (init v.expand v.callee v.suffix) ≤ 48 := by
  simp only [init, call4, stackUse, v.expandStack, Proof.CmacAes.X86.subkeys_stack v]
  decide +kernel

theorem absorb_stackUse : stackUse (absorb v.callee v.suffix) ≤ 56 := by
  simp only [absorb, absorbPre, absorbPost, call6, countHeld, held, fill, copy, chain1, chain2,
    stackUse, Proof.CmacAes.X86.update_stack v]
  decide +kernel

theorem finish_stackUse : stackUse (finish v.callee v.suffix) ≤ 56 := by
  simp only [finish, finPre, call6, countHeld, held, stackUse, Proof.CmacAes.X86.finalize_stack v]
  decide +kernel

/-- A state satisfying `vg_cmac_aes_init`'s precondition, without the
working space: the state at `0x1000` and a key of 16 bytes at `0x3000`, as
stack arguments at `0x8004`. -/
def initFrameSat : State :=
  { initSat with rd := [⟨0x3000, 16⟩, ⟨0x8004, 12⟩], wr := [⟨0x1000, 304⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.aesInitContract X86.abi 2372).pre s := by
  implies_sat [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, Spec.Cmac.aesInitPre,
    Spec.Cmac.aesInitPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using initFrameSat

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition, without the
working space: as `absorbSat`. -/
def absorbFrameSat : State :=
  { absorbSat with rd := [⟨0x3000, 0⟩, ⟨0x8004, 24⟩], wr := [⟨0x1000, 304⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.aesAbsorbContract X86.abi 2392).pre s := by
  implies_sat [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, Spec.Cmac.aesAbsorbPre,
    Spec.Cmac.aesAbsorbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [absorbFrameSat, absorbSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using absorbFrameSat

/-- A state satisfying `vg_cmac_aes_finish`'s precondition, without the
working space: as `finishSat`. -/
def finishFrameSat : State :=
  { finishSat with rd := [⟨0x8004, 20⟩], wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.aesFinishContract X86.abi 2388).pre s := by
  implies_sat [Spec.Cmac.aesFinishContract, Spec.Cmac.aesFinishSig, Spec.Cmac.aesFinishPre,
    Spec.Cmac.aesFinishPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finishFrameSat, finishSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using finishFrameSat

theorem init_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2324 3 (init v.expand v.callee v.suffix))
      (Spec.Cmac.aesInitContract X86.abi 2372) :=
  X86.Verified.stackScratch (sig := Spec.Cmac.aesInitSig) (nm := "scratch") (e := .u64) (n := 288)
    (pre := Spec.Cmac.aesInitPre X86.abi.ptrBits) (post := Spec.Cmac.aesInitPost X86.abi.ptrBits)
    (wa := false) (stack := 48) (bytes := 2324) (init_verified v) (by decide) (init_noEsp v)
    (init_stackUse v) (initPre_local _) (initPost_local _) initFrameSat_pre

theorem absorb_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2336 6 (absorb v.callee v.suffix))
      (Spec.Cmac.aesAbsorbContract X86.abi 2392) :=
  X86.Verified.stackScratch (sig := Spec.Cmac.aesAbsorbSig) (nm := "scratch") (e := .u64) (n := 288)
    (pre := Spec.Cmac.aesAbsorbPre X86.abi.ptrBits) (post := Spec.Cmac.aesAbsorbPost X86.abi.ptrBits)
    (wa := false) (stack := 56) (bytes := 2336) (absorb_verified v) (by decide) (absorb_noEsp v)
    (absorb_stackUse v) (absorbPre_local _) (absorbPost_local _) absorbFrameSat_pre

theorem finish_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2332 5 (finish v.callee v.suffix))
      (Spec.Cmac.aesFinishContract X86.abi 2388) :=
  X86.Verified.stackScratch (sig := Spec.Cmac.aesFinishSig) (nm := "scratch") (e := .u64) (n := 288)
    (pre := Spec.Cmac.aesFinishPre X86.abi.ptrBits) (post := Spec.Cmac.aesFinishPost X86.abi.ptrBits)
    (wa := false) (stack := 56) (bytes := 2332) (finish_verified v) (by decide) (finish_noEsp v)
    (finish_stackUse v) (finishPre_local _) (finishPost_local _) finishFrameSat_pre

end VG.Proof.CmacAes.Stream.X86

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86

/-- The frame of `withStackScratch` keeps the stack pointer for any `c` that
does, if it does for an empty body (decided for literal sizes). -/
theorem withStackScratch_spSafe {bytes n : Nat} {c : Prog isa}
    (hf : (Impl.StackScratch.X86.withStackScratch bytes n (.block [])).all
      (fun i => !isa.writesSp i) = true)
    (h : c.all (fun i => !isa.writesSp i) = true) :
    (Impl.StackScratch.X86.withStackScratch bytes n c).all (fun i => !isa.writesSp i) = true := by
  simp only [Impl.StackScratch.X86.withStackScratch, Code.all, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at hf ⊢
  simp_all

end VG.Proof.CmacAes.Stream.X86
