module

public import VerifiedGarbage.Proof.AesGcmSiv.Scratch
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Reg.Env
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Reg.Polyval
public import VerifiedGarbage.Impl.AesGcmSiv.X86_64Reg
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Reg.LoopsCT
public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Loops
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Reg.Fn
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Impl.AesGcmSiv.X86_64Reg
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# AES-GCM-SIV in registers on x86-64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, states satisfying the preconditions, and the shared contracts of
`Spec/GcmSiv/Contract.lean` with the working space (93 words) as a last
argument (`Proof/AesGcmSiv/Scratch.lean`), which the code, calling nothing,
uses no stack below (the contracts allow it the 8 bytes its layout keeps apart);
then in a frame of 776 bytes that allocates it.
-/

-- separate module: the contracts, apart from the proofs they are from

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSivReg.X86_64

open VG VG.X86_64

theorem seal_mx : Impl.AesGcmSiv.X86_64Reg.seal.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem open_mx : Impl.AesGcmSiv.X86_64Reg.open.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide

theorem seal_spSafe : Impl.AesGcmSiv.X86_64Reg.seal.all (fun i => !X86_64.isa.writesSp i) = true :=
  Code.all_of_spTest (by lit_decide)

theorem open_spSafe : Impl.AesGcmSiv.X86_64Reg.open.all (fun i => !X86_64.isa.writesSp i) = true :=
  Code.all_of_spTest (by lit_decide)

theorem seal_xdepth : Impl.AesGcmSiv.X86_64Reg.seal.x86_64Depth ≤ 8 := by lit_decide

theorem open_xdepth : Impl.AesGcmSiv.X86_64Reg.open.x86_64Depth ≤ 8 := by lit_decide

theorem seal_correct (F : MulFacts) (s : State) (hs : sealX86_64.pre s) :
    ∃ t s', Exec isa Impl.AesGcmSiv.X86_64Reg.seal s t s' ∧ abiPreserved s s' ∧ sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp, -, -⟩ := seal_wp F hs
  exact ⟨t, s', he, abiPreserved_of_exec seal_mx he hg, hp⟩

theorem open_correct (F : MulFacts) (s : State) (hs : openX86_64.pre s) :
    ∃ t s', Exec isa Impl.AesGcmSiv.X86_64Reg.open s t s' ∧ abiPreserved s s' ∧ openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp, -, -⟩ := open_wp F hs
  exact ⟨t, s', he, abiPreserved_of_exec open_mx he hg, hp⟩

theorem seal_ct (F : MulFacts) : ConstantTime isa sealX86_64.pre sealX86_64.pub Impl.AesGcmSiv.X86_64Reg.seal :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (seal_rel F h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem open_ct (F : MulFacts) : ConstantTime isa openX86_64.pre openX86_64.pub Impl.AesGcmSiv.X86_64Reg.open :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (open_rel F h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- A state satisfying the precondition of `vg_aes_gcm_siv_seal`: no
additional data, no data, the tag at `0x3000` and `work` at 0. -/
def sealSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8011 then 0x30 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x2100, 0⟩, ⟨0x8008, 24⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 16⟩, ⟨0, 744⟩]

theorem seal_impl : Proof.AesGcmSivReg.sealX86_64.Implies (Proof.AesGcmSiv.sealScratchContract X86_64.abi 93 8) := by
    sig_implies [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig, Spec.GcmSiv.sealPre,
      Proof.AesGcmSiv.sealRoundsPost, Proof.AesGcmSivReg.sealX86_64, Proof.AesGcmSivReg.sealPre, Proof.AesGcmSivReg.oneLay,
      Proof.AesGcmSivReg.onePub, X86_64.abi, Proof.AesGcmSivReg.arg, Proof.AesGcmSivReg.args, Proof.AesGcmSivReg.stk8,
      Proof.AesGcmSivReg.ret, Proof.AesGcmSivReg.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range,
      List.range.loop, VG.X86_64.below, X86_64.argRegs] [sealSat] using sealSat

theorem seal_verified (F : MulFacts) :
    Verified X86_64.target Impl.AesGcmSiv.X86_64Reg.seal (Proof.AesGcmSiv.sealScratchContract X86_64.abi 93 8) :=
  Verified.of_correct (seal_correct F) (seal_ct F) seal_impl

/-- A state satisfying the precondition of `vg_aes_gcm_siv_open`: as
`sealSat`, with the tag read only. -/
def openSat : State := { sealSat with
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x2100, 0⟩, ⟨0x3000, 16⟩, ⟨0x8008, 24⟩]
  wr := [⟨0, 0⟩, ⟨0, 744⟩] }

theorem open_impl : Proof.AesGcmSivReg.openX86_64.Implies (Proof.AesGcmSiv.openScratchContract X86_64.abi 93 8) :=
    { pre := by sig_implies_pre [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, Proof.AesGcmSivReg.openX86_64,
        Proof.AesGcmSivReg.openLeak, Proof.AesGcmSivReg.openResult, Proof.AesGcmSivReg.openPost, Proof.AesGcmSivReg.openPre,
        Proof.AesGcmSivReg.oneLay, Proof.AesGcmSivReg.onePub, X86_64.abi, Proof.AesGcmSivReg.arg, Proof.AesGcmSivReg.args,
        Proof.AesGcmSivReg.stk8, Proof.AesGcmSivReg.ret, Proof.AesGcmSivReg.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      -- `h` and the goal match on the same outcome of `decryptWith` with
      -- different matchers (`openPost`'s and `openPost`'s of the contract):
      -- split on it rather than have `exact h` unfold both to unify them.
      post := by
        intro s s' hs h
        sig_post [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, Proof.AesGcmSivReg.openX86_64,
        Proof.AesGcmSivReg.openLeak, Proof.AesGcmSivReg.openResult, Proof.AesGcmSivReg.openPost, Proof.AesGcmSivReg.openPre,
        Proof.AesGcmSivReg.oneLay, Proof.AesGcmSivReg.onePub, X86_64.abi, Proof.AesGcmSivReg.arg, Proof.AesGcmSivReg.args,
        Proof.AesGcmSivReg.stk8, Proof.AesGcmSivReg.ret, Proof.AesGcmSivReg.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
        sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, Proof.AesGcmSivReg.openX86_64,
        Proof.AesGcmSivReg.openLeak, Proof.AesGcmSivReg.openResult, Proof.AesGcmSivReg.openPost, Proof.AesGcmSivReg.openPre,
        Proof.AesGcmSivReg.oneLay, Proof.AesGcmSivReg.onePub, X86_64.abi, Proof.AesGcmSivReg.arg, Proof.AesGcmSivReg.args,
        Proof.AesGcmSivReg.stk8, Proof.AesGcmSivReg.ret, Proof.AesGcmSivReg.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] at h
        sig_simp [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, Proof.AesGcmSivReg.openX86_64,
        Proof.AesGcmSivReg.openLeak, Proof.AesGcmSivReg.openResult, Proof.AesGcmSivReg.openPost, Proof.AesGcmSivReg.openPre,
        Proof.AesGcmSivReg.oneLay, Proof.AesGcmSivReg.onePub, X86_64.abi, Proof.AesGcmSivReg.arg, Proof.AesGcmSivReg.args,
        Proof.AesGcmSivReg.stk8, Proof.AesGcmSivReg.ret, Proof.AesGcmSivReg.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [] at h
        intro _
        split at h <;> rename_i heq <;> rw [heq] <;> exact h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, Proof.AesGcmSivReg.openX86_64,
        Proof.AesGcmSivReg.openLeak, Proof.AesGcmSivReg.openResult, Proof.AesGcmSivReg.openPost, Proof.AesGcmSivReg.openPre,
        Proof.AesGcmSivReg.oneLay, Proof.AesGcmSivReg.onePub, X86_64.abi, Proof.AesGcmSivReg.arg, Proof.AesGcmSivReg.args,
        Proof.AesGcmSivReg.stk8, Proof.AesGcmSivReg.ret, Proof.AesGcmSivReg.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] at h
        sig_split h
        sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, Proof.AesGcmSivReg.openX86_64,
        Proof.AesGcmSivReg.openLeak, Proof.AesGcmSivReg.openResult, Proof.AesGcmSivReg.openPost, Proof.AesGcmSivReg.openPre,
        Proof.AesGcmSivReg.oneLay, Proof.AesGcmSivReg.onePub, X86_64.abi, Proof.AesGcmSivReg.arg, Proof.AesGcmSivReg.args,
        Proof.AesGcmSivReg.stk8, Proof.AesGcmSivReg.ret, Proof.AesGcmSivReg.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
        sig_simp [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, Proof.AesGcmSivReg.openX86_64,
        Proof.AesGcmSivReg.openLeak, Proof.AesGcmSivReg.openResult, Proof.AesGcmSivReg.openPost, Proof.AesGcmSivReg.openPre,
        Proof.AesGcmSivReg.oneLay, Proof.AesGcmSivReg.onePub, X86_64.abi, Proof.AesGcmSivReg.arg, Proof.AesGcmSivReg.args,
        Proof.AesGcmSivReg.stk8, Proof.AesGcmSivReg.ret, Proof.AesGcmSivReg.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by sig_implies_sat [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, Proof.AesGcmSivReg.openX86_64,
        Proof.AesGcmSivReg.openLeak, Proof.AesGcmSivReg.openResult, Proof.AesGcmSivReg.openPost, Proof.AesGcmSivReg.openPre,
        Proof.AesGcmSivReg.oneLay, Proof.AesGcmSivReg.onePub, X86_64.abi, Proof.AesGcmSivReg.arg, Proof.AesGcmSivReg.args,
        Proof.AesGcmSivReg.stk8, Proof.AesGcmSivReg.ret, Proof.AesGcmSivReg.rounds, X86_64.stackArg, X86_64.stackArgAddr,
        List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [openSat, sealSat] using openSat }

/-- `open`'s public data include its leak, from which `pub` has whether it
succeeds. -/
theorem open_verified (F : MulFacts) :
    Verified X86_64.target Impl.AesGcmSiv.X86_64Reg.open (Proof.AesGcmSiv.openScratchContract X86_64.abi 93 8) :=
  Verified.of_correct (open_correct F) (open_ct F) open_impl

/-- A state satisfying `vg_aes_gcm_siv_seal`'s precondition, without the
working space. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x2100, 0⟩, ⟨0x8008, 16⟩], wr := [⟨0, 0⟩, ⟨0x3000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesGcmSiv.sealRoundsContract X86_64.abi 784).pre s := by
  implies_sat [Proof.AesGcmSiv.sealRoundsContract, Spec.GcmSiv.sealSig, Spec.GcmSiv.sealPre, Proof.AesGcmSiv.sealRoundsPost,
    X86_64.abi, X86_64.argRegs] [sealFrameSat, sealSat] using sealFrameSat

theorem seal_framed (F : MulFacts) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 776 2 Impl.AesGcmSiv.X86_64Reg.seal)
      (Proof.AesGcmSiv.sealRoundsContract X86_64.abi 784) :=
  X86_64.Verified.stackArgScratch (hpostOut := Proof.AesGcmSiv.sealPostOut_local _) (sig := Spec.GcmSiv.sealSig) (nm := "work") (e := .u64)
    (n := 93) (pre := Spec.GcmSiv.sealPre X86_64.abi.ptrBits)
    (post := Proof.AesGcmSiv.sealRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 776) (seal_verified F) (by decide) (by decide) (by decide)
    seal_spSafe seal_xdepth (Proof.AesGcmSiv.sealPre_local _) (Proof.AesGcmSiv.sealPost_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_gcm_siv_open`'s precondition, without the
working space. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x2100, 0⟩, ⟨0x3000, 16⟩, ⟨0x8008, 16⟩], wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesGcmSiv.openRoundsContract X86_64.abi 784).pre s := by
  implies_sat [Proof.AesGcmSiv.openRoundsContract, Spec.GcmSiv.openSig, Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost,
    Spec.GcmSiv.openLeak, X86_64.abi, X86_64.argRegs] [openFrameSat, sealSat] using openFrameSat

theorem open_framed (F : MulFacts) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 776 2 Impl.AesGcmSiv.X86_64Reg.open)
      (Proof.AesGcmSiv.openRoundsContract X86_64.abi 784) :=
  X86_64.Verified.stackArgScratch (hpostOut := Proof.AesGcmSiv.openPostOut_local _) (sig := Spec.GcmSiv.openSig) (nm := "work") (e := .u64)
    (n := 93) (pre := Spec.GcmSiv.openPre X86_64.abi.ptrBits)
    (post := Proof.AesGcmSiv.openRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (leak := some (Spec.GcmSiv.openLeak X86_64.abi.ptrBits)) (bytes := 776)
    (Proof.AesGcmSiv.Verified.of_openScratch (open_verified F))
    (by decide) (by decide) (by decide) open_spSafe open_xdepth (Proof.AesGcmSiv.openPre_local _)
    (Proof.AesGcmSiv.openPost_local _) openFrameSat_pre (hleak := Proof.AesGcmSiv.openLeak_local _)


/-! ## With the loops

`sealL` and `openL`, for any loops that meet their contracts, pass the taint
analysis and use no stack: against the same contracts, in the same frame. -/

section
open VG.Impl.AesGcmSiv.X86_64Reg
open VG.Impl.AesGcmSiv.X86_64Stitch (Loops)
open VG.Proof.AesGcmSiv.X86_64.Stitch (LoopsOk LoopsCode)

variable {lp : Loops}

theorem sealL_mx (hcode : LoopsCode lp) : (sealL lp).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [sealL, polyvalL, cryptL, hashFront, ctrFront, Code.allInstrs, hcode.hashMx, hcode.ctrMx, Bool.true_and,
    Bool.and_true]
  lit_decide

theorem openL_mx (hcode : LoopsCode lp) : (openL lp).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [openL, openHead, decL, decFront, Code.allInstrs, hcode.decMx, Bool.true_and, Bool.and_true]
  lit_decide

theorem sealL_spSafe (hcode : LoopsCode lp) : (sealL lp).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [sealL, polyvalL, cryptL, hashFront, ctrFront, Code.all, hcode.hashSp, hcode.ctrSp, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem openL_spSafe (hcode : LoopsCode lp) : (openL lp).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [openL, openHead, decL, decFront, Code.all, hcode.decSp, Bool.true_and, Bool.and_true]
  decide +kernel

theorem sealL_xdepth (hcode : LoopsCode lp) : (sealL lp).x86_64Depth ≤ 8 := by
  simp only [sealL, polyvalL, cryptL, hashFront, ctrFront, Code.x86_64Depth, hcode.hashDepth, hcode.ctrDepth]
  lit_decide

theorem openL_xdepth (hcode : LoopsCode lp) : (openL lp).x86_64Depth ≤ 8 := by
  simp only [openL, openHead, decL, decFront, Code.x86_64Depth, hcode.decDepth]
  lit_decide

theorem sealL_ct (F : MulFacts) (hlp : LoopsOk lp) (hct : LoopsCT lp) :
    ConstantTime isa sealX86_64.pre sealX86_64.pub (sealL lp) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (sealL_rel F hlp hct h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem openL_ct (F : MulFacts) (hlp : LoopsOk lp) (hct : LoopsCT lp) :
    ConstantTime isa openX86_64.pre openX86_64.pub (openL lp) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (openL_rel F hlp hct h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem sealL_verified (F : MulFacts) (hlp : LoopsOk lp) (hcode : LoopsCode lp) (hct : LoopsCT lp) :
    Verified X86_64.target (sealL lp) (Proof.AesGcmSiv.sealScratchContract X86_64.abi 93 8) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hp, -, -⟩ := sealL_wp F hlp hs
      exact ⟨t, s', he, abiPreserved_of_exec (sealL_mx hcode) he hg, hp⟩)
    (sealL_ct F hlp hct) seal_impl

theorem openL_verified (F : MulFacts) (hlp : LoopsOk lp) (hcode : LoopsCode lp) (hct : LoopsCT lp) :
    Verified X86_64.target (openL lp) (Proof.AesGcmSiv.openScratchContract X86_64.abi 93 8) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hp, -, -⟩ := openL_wp F hlp hs
      exact ⟨t, s', he, abiPreserved_of_exec (openL_mx hcode) he hg, hp⟩)
    (openL_ct F hlp hct) open_impl

theorem sealL_framed (F : MulFacts) (hlp : LoopsOk lp) (hcode : LoopsCode lp) (hct : LoopsCT lp) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 776 2 (sealL lp))
      (Proof.AesGcmSiv.sealRoundsContract X86_64.abi 784) :=
  X86_64.Verified.stackArgScratch (hpostOut := Proof.AesGcmSiv.sealPostOut_local _) (sig := Spec.GcmSiv.sealSig) (nm := "work") (e := .u64)
    (n := 93) (pre := Spec.GcmSiv.sealPre X86_64.abi.ptrBits)
    (post := Proof.AesGcmSiv.sealRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 776) (sealL_verified F hlp hcode hct) (by decide) (by decide) (by decide)
    (sealL_spSafe hcode) (sealL_xdepth hcode) (Proof.AesGcmSiv.sealPre_local _) (Proof.AesGcmSiv.sealPost_local _)
    sealFrameSat_pre

theorem openL_framed (F : MulFacts) (hlp : LoopsOk lp) (hcode : LoopsCode lp) (hct : LoopsCT lp) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackArgScratch 776 2 (openL lp))
      (Proof.AesGcmSiv.openRoundsContract X86_64.abi 784) :=
  X86_64.Verified.stackArgScratch (hpostOut := Proof.AesGcmSiv.openPostOut_local _) (sig := Spec.GcmSiv.openSig) (nm := "work") (e := .u64)
    (n := 93) (pre := Spec.GcmSiv.openPre X86_64.abi.ptrBits)
    (post := Proof.AesGcmSiv.openRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (leak := some (Spec.GcmSiv.openLeak X86_64.abi.ptrBits)) (bytes := 776)
    (Proof.AesGcmSiv.Verified.of_openScratch (openL_verified F hlp hcode hct))
    (by decide) (by decide) (by decide) (openL_spSafe hcode) (openL_xdepth hcode) (Proof.AesGcmSiv.openPre_local _)
    (Proof.AesGcmSiv.openPost_local _) openFrameSat_pre (hleak := Proof.AesGcmSiv.openLeak_local _)

end

end VG.Proof.AesGcmSivReg.X86_64
