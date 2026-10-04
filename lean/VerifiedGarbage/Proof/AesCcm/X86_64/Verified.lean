import VerifiedGarbage.Proof.AesCcm.X86_64.OpenCT
import VerifiedGarbage.Proof.CmacAes.X86_64.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesCcm.Scratch

/-!
# AES-CCM on x86-64: `Verified`

Correctness and constant time (for any implementation `v` of
`vg_aes_ctr32`), states satisfying the preconditions, and the shared
contracts of `Spec/Ccm/Contract.lean` with the working space as a last
argument (`Proof/AesCcm/Scratch.lean`), with 16 bytes of stack: the return
addresses of the call of `vg_cmac_aes_update` (or of `vg_aes_ctr32`) and of
its call of `vg_aes_ctr32`. `Frame.lean` allocates the working space.
-/

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.Impl.AesCcm.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (update_mx update_spSafe)

theorem seal_mx (v : Ctr32Impl) : («seal» v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [«seal», sealFront, tagOut, mac, b0, aad, aadHead, absorbPad, updBlock, tag, ctr, ctrChunk, callUpdate, callCtr,
    Code.allInstrs, update_mx v, v.mxcsr]
  decide +kernel

theorem open_mx (v : Ctr32Impl) : («open» v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [«open», openFront, mac, b0, aad, aadHead, absorbPad, updBlock, tag, ctr, ctrChunk, callUpdate, callCtr,
    Code.allInstrs, update_mx v, v.mxcsr]
  decide +kernel

theorem seal_spSafe (v : Ctr32Impl) : («seal» v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [«seal», sealFront, tagOut, mac, b0, aad, aadHead, absorbPad, updBlock, tag, ctr, ctrChunk, callUpdate, callCtr,
    Code.all, update_spSafe v, v.spSafe]
  decide +kernel

theorem open_spSafe (v : Ctr32Impl) : («open» v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [«open», openFront, mac, b0, aad, aadHead, absorbPad, updBlock, tag, ctr, ctrChunk, callUpdate, callCtr,
    Code.all, update_spSafe v, v.spSafe]
  decide +kernel

theorem seal_correct (v : Ctr32Impl) (s : State) (hs : sealX86_64.pre s) :
    ∃ t s', Exec isa («seal» v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := seal_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (seal_mx v) he hg, hp⟩

theorem open_correct (v : Ctr32Impl) (s : State) (hs : openX86_64.pre s) :
    ∃ t s', Exec isa («open» v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := open_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (open_mx v) he hg, hp⟩

theorem open_ct (v : Ctr32Impl) : ConstantTime isa openX86_64.pre openX86_64.pub («open» v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (open_rel v h₁ h₂ hq.1 _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- A state satisfying the precondition of `vg_aes_ccm_seal`: a 7-byte nonce,
no associated data, no data, a 4-byte tag at `0x3000` and `work` at 0. -/
def sealSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 7 | .r8 => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8020 then 4 else if a = 0x8019 then 0x30 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩, ⟨0x8008, 40⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0, 2560⟩]

theorem seal_verified (v : Ctr32Impl) :
    Verified X86_64.target («seal» v.callee v.suffix) (Proof.AesCcm.sealScratchContract X86_64.abi 16) :=
  Verified.of_correct (seal_correct v) (seal_ct v) (by
    sig_implies [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre,
      Spec.Ccm.sealPost, Proof.AesCcm.sealX86_64, Proof.AesCcm.sealPre, Proof.AesCcm.oneLay, Proof.AesCcm.onePub,
      X86_64.abi, Proof.AesCcm.arg, Proof.AesCcm.args, Proof.AesCcm.stk16, Proof.AesCcm.ret, Proof.AesCcm.rounds,
      X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [sealSat] using sealSat)

/-- A state satisfying the precondition of `vg_aes_ccm_open`: as `sealSat`,
with the tag read only. -/
def openSat : State := { sealSat with
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩, ⟨0x3000, 4⟩, ⟨0x8008, 40⟩]
  wr := [⟨0, 0⟩, ⟨0, 2560⟩] }

theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- `open`'s public data include its leak, from which `pub` has whether it
succeeds. -/
theorem open_verified (v : Ctr32Impl) :
    Verified X86_64.target («open» v.callee v.suffix) (Proof.AesCcm.openScratchContract X86_64.abi 16) :=
  Verified.of_correct (open_correct v) (open_ct v)
    { pre := by sig_implies_pre [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
        Spec.Ccm.openPost, Spec.Ccm.openLeak, Proof.AesCcm.openX86_64, Proof.AesCcm.openLeak, Proof.AesCcm.openPre,
        Proof.AesCcm.oneLay, Proof.AesCcm.onePub, X86_64.abi, Proof.AesCcm.arg, Proof.AesCcm.args,
        Proof.AesCcm.stk16, Proof.AesCcm.ret, Proof.AesCcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
        List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      post := by sig_implies_post [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
        Spec.Ccm.openPost, Spec.Ccm.openLeak, Proof.AesCcm.openX86_64, Proof.AesCcm.openLeak, Proof.AesCcm.openPre,
        Proof.AesCcm.oneLay, Proof.AesCcm.onePub, X86_64.abi, Proof.AesCcm.arg, Proof.AesCcm.args,
        Proof.AesCcm.stk16, Proof.AesCcm.ret, Proof.AesCcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
        List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
        Spec.Ccm.openPost, Spec.Ccm.openLeak, Proof.AesCcm.openX86_64, Proof.AesCcm.openLeak, Proof.AesCcm.openPre,
        Proof.AesCcm.oneLay, Proof.AesCcm.onePub, X86_64.abi, Proof.AesCcm.arg, Proof.AesCcm.args,
        Proof.AesCcm.stk16, Proof.AesCcm.ret, Proof.AesCcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
        List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] at h
        sig_split h
        sig_reduce [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
        Spec.Ccm.openPost, Spec.Ccm.openLeak, Proof.AesCcm.openX86_64, Proof.AesCcm.openLeak, Proof.AesCcm.openPre,
        Proof.AesCcm.oneLay, Proof.AesCcm.onePub, X86_64.abi, Proof.AesCcm.arg, Proof.AesCcm.args,
        Proof.AesCcm.stk16, Proof.AesCcm.ret, Proof.AesCcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
        List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
        sig_simp [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
        Spec.Ccm.openPost, Spec.Ccm.openLeak, Proof.AesCcm.openX86_64, Proof.AesCcm.openLeak, Proof.AesCcm.openPre,
        Proof.AesCcm.oneLay, Proof.AesCcm.onePub, X86_64.abi, Proof.AesCcm.arg, Proof.AesCcm.args,
        Proof.AesCcm.stk16, Proof.AesCcm.ret, Proof.AesCcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
        List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by sig_implies_sat [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
        Spec.Ccm.openPost, Spec.Ccm.openLeak, Proof.AesCcm.openX86_64, Proof.AesCcm.openLeak, Proof.AesCcm.openPre,
        Proof.AesCcm.oneLay, Proof.AesCcm.onePub, X86_64.abi, Proof.AesCcm.arg, Proof.AesCcm.args,
        Proof.AesCcm.stk16, Proof.AesCcm.ret, Proof.AesCcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
        List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [openSat, sealSat] using openSat }

end VG.Proof.AesCcm.X86_64
