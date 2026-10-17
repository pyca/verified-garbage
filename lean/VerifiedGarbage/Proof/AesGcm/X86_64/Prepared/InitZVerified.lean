module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.InitVerified
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.InitZCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.X86_64.ZLaneSse

/-! # Prepared key setup on 512-bit registers satisfies the shared contract -/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
variable (v : GcmImpl)

theorem initZ_mx : (Prepared.initZ v.callees).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [Prepared.initZ, initWith, Code.allInstrs]
  simp only [GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, Bool.true_and]
  decide +kernel

theorem initZ_spSafe : (Prepared.initZ v.callees).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Prepared.initZ, initWith, Code.all]
  simp only [GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, Bool.true_and]
  decide +kernel

theorem initZ_xdepth : (Prepared.initZ v.callees).x86_64Depth ≤ 8 := by
  simp only [Prepared.initZ, initWith, Code.x86_64Depth, Nat.max_le]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals first | decide +kernel | (simp only [GcmImpl.callees, v.ctr.noStack, v.key.noStack]; decide +kernel)

theorem initZ_correct (s : State) (hs : Proof.AesGcm.initPreparedX86_64.pre s) :
    ∃ t s', Exec isa (Prepared.initZ v.callees) s t s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.initPreparedX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := initZ_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (initZ_mx v) he hg, hp⟩

theorem initZ_verified :
    Verified X86_64.target (Prepared.initZ v.callees) (Proof.AesGcm.initPreparedScratchContract X86_64.abi 8) :=
  Verified.of_correct (initZ_correct v) (initZ_ct v) (by
    sig_implies [Proof.AesGcm.initPreparedScratchContract, Proof.AesGcm.initPrecomputedScratchSig,
      Spec.Gcm.initPre, Spec.Gcm.initPreparedPost, Proof.AesGcm.initPreparedX86_64, Proof.AesGcm.initX86_64,
      Proof.AesGcm.initPreL, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [initSatP, initSat] using initSatP)

theorem initZ_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (Prepared.initZ v.callees))
      (Spec.Gcm.initPreparedContract X86_64.abi 2576) :=
  X86_64.Verified.stackScratch (sig := Spec.Gcm.initPreparedSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.initPre X86_64.abi.ptrBits) (post := Spec.Gcm.initPreparedPost X86_64.abi.ptrBits)
    (wa := true) (stack := 8) (bytes := 2568) (initZ_verified v) (by decide) (by decide)
    (by decide) (initZ_spSafe v) (initZ_xdepth v) initFrameSatPrepared_pre

end VG.Proof.AesGcm.X86_64
