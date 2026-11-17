module

public import VerifiedGarbage.Proof.AesOcb.X86_64.AesNi.CT
public import VerifiedGarbage.Proof.AesOcb.X86_64.Frame
public import VerifiedGarbage.Proof.AesOcb.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChunks
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesCcm.X86_64.Callee
-- separate module: it builds alongside `Scrub`, which the variants of `seal` and `open` also import

/-!
# One-pass AES-OCB with AES-NI on x86-64: `Verified`

Correctness (`seal_wp'`, `open_wp'`) and constant time (`seal_rel`,
`open_rel`) for a state satisfying each precondition with 640 bytes of
working space for `seal` and 848 for `open` (`sealW`, `openW`), and the
shared contracts of `Spec/Ocb/Contract.lean` with the working space as a last
argument (`Proof/AesOcb/Scratch.lean`), with the 8 bytes of stack of the
functions over the AES block functions, which the preconditions they share
include (this code calls nothing). In a frame that allocates the working space (`seal_framed`,
`open_framed`: the working space and the 48 bytes of
`Verified.stackArgScratchKept`), which holds the offsets, the checksum, the
table `C`, the blocks of the data XORed with offsets and, for `open`, the
round keys through `aesimc`, so it is wiped whole on return (`sealReg`,
`openReg`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64.AesNi

open VG VG.X86_64
open VG.Proof.AesOcb.X86_64 (sealArgs_of openArgs_of ofNat_toNat64 TwoN sealSat openSat sealFrameSat openFrameSat)
open VG.Proof.AesOcb (sealPre_local sealPost_local openPre_local openPost_local openLeak_local)

/-- `vg_aes_ocb_seal` with 640 bytes of working space. -/
def sealW : Contract isa := { Proof.AesOcb.sealX86_64 with pre := fun s => Proof.AesOcb.sealPreX s 640 }

/-- `vg_aes_ocb_open` with 848 bytes of working space. -/
def openW : Contract isa := { Proof.AesOcb.openX86_64 with pre := fun s => Proof.AesOcb.openPreX s 848 }

theorem seal_wp {s : State} (h : Proof.AesOcb.sealPreX s 640) :
    WP isa Impl.AesOcb.X86_64AesNi.seal s fun s' => gprPreserved s s' ∧ sealW.post s s' :=
  seal_wp' (sealArgs_of h) (Proof.AesCcm.X86_64.covers_of_mem (by rw [h.2.1]; simp)) rfl rfl
    (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl
    (ofNat_toNat64 _).symm

theorem open_wp {s : State} (h : Proof.AesOcb.openPreX s 848) :
    WP isa Impl.AesOcb.X86_64AesNi.open s fun s' => gprPreserved s s' ∧ openW.post s s' :=
  open_wp' (openArgs_of h) rfl rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl rfl (ofNat_toNat64 _).symm
    rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm

theorem seal_mx : Impl.AesOcb.X86_64AesNi.seal.allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel

theorem open_mx : Impl.AesOcb.X86_64AesNi.open.allInstrs (fun i => !loadsMxcsr i) = true := by
  decide +kernel

theorem seal_spSafe : Impl.AesOcb.X86_64AesNi.seal.all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel

theorem open_spSafe : Impl.AesOcb.X86_64AesNi.open.all (fun i => !X86_64.isa.writesSp i) = true := by
  decide +kernel

theorem seal_xdepth : Impl.AesOcb.X86_64AesNi.seal.x86_64Depth ≤ 8 := by decide +kernel

theorem open_xdepth : Impl.AesOcb.X86_64AesNi.open.x86_64Depth ≤ 8 := by decide +kernel

theorem seal_correct (s : State) (hs : sealW.pre s) :
    ∃ t s', Exec isa Impl.AesOcb.X86_64AesNi.seal s t s' ∧ abiPreserved s s' ∧ sealW.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := seal_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec seal_mx he hg, hp⟩

theorem open_correct (s : State) (hs : openW.pre s) :
    ∃ t s', Exec isa Impl.AesOcb.X86_64AesNi.open s t s' ∧ abiPreserved s s' ∧ openW.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := open_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec open_mx he hg, hp⟩

theorem seal_ct : ConstantTime isa sealW.pre sealW.pub Impl.AesOcb.X86_64AesNi.seal :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hq e₁ e₂ => by
    have T := TwoN.of hq (sealArgs_of h₁) (sealArgs_of h₂)
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := hq
    have hw₂ : s₂.wr = [⟨Proof.AesOcb.arg s₁ 0, (Proof.AesOcb.arg s₁ 1).toNat⟩,
        ⟨Proof.AesOcb.arg s₁ 2, (Proof.AesOcb.arg s₁ 3).toNat⟩, ⟨Proof.AesOcb.arg s₁ 4, 640⟩] := by
      rw [h₂.2.1, q8 0 (by decide), q8 1 (by decide), q8 2 (by decide), q8 3 (by decide), q8 4 (by decide)]
    exact (seal_rel T h₁.2.1 hw₂ _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem open_ct : ConstantTime isa openW.pre openW.pub Impl.AesOcb.X86_64AesNi.open :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hq e₁ e₂ => by
    have T := TwoN.of hq.1 (openArgs_of h₁) (openArgs_of h₂)
    obtain ⟨⟨q1, q2, q3, q4, q5, q6, q7, q8⟩, -⟩ := hq
    have hw₂ : s₂.wr = [⟨Proof.AesOcb.arg s₁ 0, (Proof.AesOcb.arg s₁ 1).toNat⟩,
        ⟨Proof.AesOcb.arg s₁ 4, 848⟩] := by
      rw [h₂.2.1, q8 0 (by decide), q8 1 (by decide), q8 4 (by decide)]
    exact (open_rel T h₁.2.1 hw₂ _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- A state satisfying `sealW`'s precondition: as `sealSat`, with 640 bytes
of working space. -/
def sealSatF : State := { sealSat with wr := [⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0, 640⟩] }

/-- A state satisfying `openW`'s precondition: as `openSat`, with 848 bytes
of working space. -/
def openSatF : State := { openSat with wr := [⟨0, 0⟩, ⟨0, 848⟩] }

theorem seal_verified :
    Verified X86_64.target Impl.AesOcb.X86_64AesNi.seal (Proof.AesOcb.sealWorkContract X86_64.abi 80 8) :=
  Verified.of_correct seal_correct seal_ct (by
    sig_implies [Proof.AesOcb.sealWorkContract, Proof.AesOcb.sealWorkSig, Spec.Ocb.sealPre,
      Proof.AesOcb.sealRoundsPost, sealW, Proof.AesOcb.sealX86_64, Proof.AesOcb.sealPreX, Proof.AesOcb.oneFacts,
      Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad, Proof.AesOcb.aData, Proof.AesOcb.aTag,
      Proof.AesOcb.aWork, Proof.AesOcb.onePub, X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8,
      Proof.AesOcb.ret, Proof.AesOcb.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range,
      List.range.loop, VG.X86_64.below, X86_64.argRegs] [sealSatF, sealSat] using sealSatF)

/-- `open`'s public data include its leak, from which `pub` has whether it
succeeds. -/
theorem open_verified :
    Verified X86_64.target Impl.AesOcb.X86_64AesNi.open (Proof.AesOcb.openWorkContract X86_64.abi 106 8) :=
  Verified.of_correct open_correct open_ct
    { pre := by sig_implies_pre [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openW, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs]
      post := by sig_implies_post [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openW, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openW, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs] at h
        sig_split h
        sig_reduce [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openW, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs]
        sig_simp [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openW, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by sig_implies_sat [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openW, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs] [openSatF, openSat, sealSat] using openSatF }

/-! ## In a frame that allocates the working space -/

theorem sealFrameSatF_pre : ∃ s, (Proof.AesOcb.sealRoundsContract X86_64.abi 696).pre s := by
  implies_sat [Proof.AesOcb.sealRoundsContract, Spec.Ocb.sealSig, Spec.Ocb.sealPre, Proof.AesOcb.sealRoundsPost,
    X86_64.abi, X86_64.argRegs] [sealFrameSat, sealSat] using sealFrameSat

theorem seal_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 688 4 Impl.AesOcb.X86_64AesNi.seal)
      (Proof.AesOcb.sealRoundsContract X86_64.abi 696) :=
  X86_64.Verified.stackArgScratchKept (sig := Spec.Ocb.sealSig) (nm := "work") (e := .u64)
    (n := 80) (pre := Spec.Ocb.sealPre X86_64.abi.ptrBits)
    (post := Proof.AesOcb.sealRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 688) seal_verified (by decide) (by decide) (by decide)
    seal_spSafe seal_xdepth (sealPre_local _) (sealPost_local _) sealFrameSatF_pre

theorem openFrameSatF_pre : ∃ s, (Proof.AesOcb.openRoundsContract X86_64.abi 904).pre s := by
  implies_sat [Proof.AesOcb.openRoundsContract, Spec.Ocb.openSig, Spec.Ocb.openPre, Proof.AesOcb.openRoundsPost,
    Spec.Ocb.openLeak, X86_64.abi, X86_64.argRegs] [openFrameSat, sealSat] using openFrameSat

theorem open_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 896 4 Impl.AesOcb.X86_64AesNi.open)
      (Proof.AesOcb.openRoundsContract X86_64.abi 904) :=
  X86_64.Verified.stackArgScratchKept (sig := Spec.Ocb.openSig) (nm := "work") (e := .u64)
    (n := 106) (pre := Spec.Ocb.openPre X86_64.abi.ptrBits)
    (post := Proof.AesOcb.openRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (leak := some (Spec.Ocb.openLeak X86_64.abi.ptrBits)) (bytes := 896) open_verified
    (by decide) (by decide) (by decide) open_spSafe open_xdepth (openPre_local _)
    (openPost_local _) openFrameSatF_pre (hleak := openLeak_local _)

/-! ## Registrations -/

open VG.X86_64.RScrub in
/-- `vg_aes_ocb_seal_aesni`: its frame, wiped whole on return, in 16-byte
stores that are all aligned (the chunks `[8, 688]`). -/
def sealReg : Registration Spec.Ocb.sealApi X86_64.target :=
  withScrubAllC {
    suffix := "_aesni"
    code := Impl.StackScratch.X86_64.withStackArgScratch 688 4 Impl.AesOcb.X86_64AesNi.seal
    verified := Proof.AesOcb.seal_keyed seal_framed
    spSafe := VG.X86_64.withStackArgScratch_spSafe seal_spSafe }
    (Proof.AesOcb.X86_64.Scrub.sealOut _) [8, 688]

open VG.X86_64.RScrub in
/-- `vg_aes_ocb_open_aesni`: its frame, wiped whole on return, in 16-byte
stores that are all aligned (the chunks `[8, 896]`). -/
def openReg : Registration Spec.Ocb.openApi X86_64.target :=
  withScrubAllC {
    suffix := "_aesni"
    code := Impl.StackScratch.X86_64.withStackArgScratch 896 4 Impl.AesOcb.X86_64AesNi.open
    verified := Proof.AesOcb.open_keyed open_framed
    spSafe := VG.X86_64.withStackArgScratch_spSafe open_spSafe }
    (Proof.AesOcb.X86_64.Scrub.openOut _) [8, 896]

end VG.Proof.AesOcb.X86_64.AesNi
