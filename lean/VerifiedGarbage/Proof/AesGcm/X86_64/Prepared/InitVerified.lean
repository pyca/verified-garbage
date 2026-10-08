import VerifiedGarbage.Proof.AesGcm.X86_64.VerifiedP
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.InitCT

/-! # Prepared key setup satisfies the shared contract -/
namespace VG.Proof.AesGcm
open VG.Spec.Gcm

def initPreparedScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initPrecomputedScratchSig.contract A
    (pre := fun key keyLen ctx _scratch => initPre A.ptrBits key keyLen ctx)
    (post := fun key keyLen ctx _scratch => initPreparedPost A.ptrBits key keyLen ctx)
    (writeArgs := true) (stack := stack)
end VG.Proof.AesGcm

namespace VG.Proof.AesGcm.X86_64
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
variable (v : GcmImpl)

theorem initPrepared_mx : (Prepared.init v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  have hs : (powSteps v.callees 47).allInstrs (fun i => !loadsMxcsr i) = true := powSteps_allInstrs v (by
    simp only [powStep, Code.allInstrs, GcmImpl.callees, v.gh.mxcsr, Bool.true_and, Bool.and_true]
    decide +kernel) 47
  simp only [Prepared.init, initWith, Code.allInstrs]
  rw [hs]
  simp only [GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, Bool.true_and]
  decide +kernel

theorem initPrepared_spSafe : (Prepared.init v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  have hs : (powSteps v.callees 47).all (fun i => !X86_64.isa.writesSp i) = true := powSteps_all v (by
    simp only [powStep, Code.all, GcmImpl.callees, v.gh.spSafe, Bool.true_and]
    decide +kernel) 47
  simp only [Prepared.init, initWith, Code.all]
  rw [hs]
  simp only [GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, Bool.true_and]
  decide +kernel

theorem initPrepared_xdepth : (Prepared.init v.callees).x86_64Depth ≤ 8 := by
  have hs : (powSteps v.callees 47).x86_64Depth ≤ 8 := powSteps_xdepth v (by
    simp only [powStep, Code.x86_64Depth, GcmImpl.callees, v.gh.noStack, Nat.max_le]
    decide +kernel) 47
  simp only [Prepared.init, initWith, Code.x86_64Depth, Nat.max_le]
  refine ⟨?_, ?_, ?_, ?_, ?_, hs, ?_⟩
  all_goals first | decide +kernel | (simp only [GcmImpl.callees, v.ctr.noStack, v.key.noStack]; decide +kernel)

theorem initPrepared_correct (s : State) (hs : Proof.AesGcm.initPreparedX86_64.pre s) :
    ∃ t s', Exec isa (Prepared.init v.callees) s t s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.initPreparedX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := initPrepared_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (initPrepared_mx v) he hg, hp⟩

theorem initPrepared_verified :
    Verified X86_64.target (Prepared.init v.callees) (Proof.AesGcm.initPreparedScratchContract X86_64.abi 8) :=
  Verified.of_correct (initPrepared_correct v) (initPrepared_ct v) (by
    sig_implies [Proof.AesGcm.initPreparedScratchContract, Proof.AesGcm.initPrecomputedScratchSig,
      Spec.Gcm.initPre, Spec.Gcm.initPreparedPost, Proof.AesGcm.initPreparedX86_64, Proof.AesGcm.initX86_64,
      Proof.AesGcm.initPreL, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [initSatP, initSat] using initSatP)

theorem initFrameSatPrepared_pre : ∃ s, (Spec.Gcm.initPreparedContract X86_64.abi 2576).pre s := by
  implies_sat [Spec.Gcm.initPreparedContract, Spec.Gcm.initPreparedSig, Spec.Gcm.initPre,
    Spec.Gcm.initPreparedPost, X86_64.abi, X86_64.argRegs] [initFrameSatP, initSat] using initFrameSatP

theorem initPrepared_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (Prepared.init v.callees))
      (Spec.Gcm.initPreparedContract X86_64.abi 2576) :=
  X86_64.Verified.stackScratch (sig := Spec.Gcm.initPreparedSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.initPre X86_64.abi.ptrBits) (post := Spec.Gcm.initPreparedPost X86_64.abi.ptrBits)
    (wa := true) (stack := 8) (bytes := 2568) (initPrepared_verified v) (by decide) (by decide)
    (by decide) (initPrepared_spSafe v) (initPrepared_xdepth v) initFrameSatPrepared_pre

end VG.Proof.AesGcm.X86_64
