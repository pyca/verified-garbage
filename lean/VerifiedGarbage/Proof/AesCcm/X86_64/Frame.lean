module

public import VerifiedGarbage.Impl.AesCcm.X86_64.Fn
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.AesCcm.Scratch
import VerifiedGarbage.Proof.AesCcm.X86_64.OpenCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.AesCcm.X86_64
public import VerifiedGarbage.Proof.AesCcm.X86_64.Contract
public import VerifiedGarbage.Proof.CmacAes.X86_64.Variant
import VerifiedGarbage.Proof.AesCcm.X86_64.Seal
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChunks
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubPaths
import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.AesCcm.X86_64.Args
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Spec.Ccm.Contract
meta import VerifiedGarbage.Proof.AesCcm.X86_64.Args
meta import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Framework.X86_64.ScrubPart
import VerifiedGarbage.Proof.Framework.X86_64.Frame

/-! ### `AesCcm.X86_64.Verified`, which only this module used -/

section

/-!
# AES-CCM on x86-64: `Verified`

Correctness and constant time (for any implementation `v` of
`vg_cmac_aes_update`, and the implementation of `vg_aes_ctr32` that goes with
it), states satisfying the preconditions, and the shared
contracts of `Spec/Ccm/Contract.lean` with the working space as a last
argument (`Proof/AesCcm/Scratch.lean`), with 16 bytes of stack: the return
addresses of the call of `vg_cmac_aes_update` (or of `vg_aes_ctr32`) and of
its call of `vg_aes_ctr32`, if it makes one. `Frame.lean` allocates the working space.
-/

@[expose] public section

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.Impl.AesCcm.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

theorem seal_mx (v : UpdateImpl) : («seal» v.callee v.ctr.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [«seal», sealFront, tagOut, mac, b0, aad, aadHead, absorbPad, updBlock, tag, ctr, ctrChunk, callUpdate, callCtr,
    Code.allInstrs, v.mxcsr, v.ctr.mxcsr]
  decide +kernel

theorem open_mx (v : UpdateImpl) : («open» v.callee v.ctr.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [«open», openFront, mac, b0, aad, aadHead, absorbPad, updBlock, tag, ctr, ctrChunk, callUpdate, callCtr,
    Code.allInstrs, v.mxcsr, v.ctr.mxcsr]
  decide +kernel

theorem seal_spSafe (v : UpdateImpl) : («seal» v.callee v.ctr.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [«seal», sealFront, tagOut, mac, b0, aad, aadHead, absorbPad, updBlock, tag, ctr, ctrChunk, callUpdate, callCtr,
    Code.all, v.spSafe, v.ctr.spSafe]
  decide +kernel

theorem open_spSafe (v : UpdateImpl) : («open» v.callee v.ctr.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [«open», openFront, mac, b0, aad, aadHead, absorbPad, updBlock, tag, ctr, ctrChunk, callUpdate, callCtr,
    Code.all, v.spSafe, v.ctr.spSafe]
  decide +kernel

theorem seal_correct (v : UpdateImpl) (s : State) (hs : sealX86_64.pre s) :
    ∃ t s', Exec isa («seal» v.callee v.ctr.callee) s t s' ∧ abiPreserved s s' ∧ sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := seal_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (seal_mx v) he hg, hp⟩

theorem open_correct (v : UpdateImpl) (s : State) (hs : openX86_64.pre s) :
    ∃ t s', Exec isa («open» v.callee v.ctr.callee) s t s' ∧ abiPreserved s s' ∧ openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := open_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (open_mx v) he hg, hp⟩

theorem open_ct (v : UpdateImpl) : ConstantTime isa openX86_64.pre openX86_64.pub («open» v.callee v.ctr.callee) :=
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

theorem seal_verified (v : UpdateImpl) :
    Verified X86_64.target («seal» v.callee v.ctr.callee) (Proof.AesCcm.sealScratchContract X86_64.abi 16) :=
  Verified.of_correct (seal_correct v) (seal_ct v) (by
    sig_implies [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre,
      Proof.AesCcm.sealRoundsPost, Proof.AesCcm.sealX86_64, Proof.AesCcm.sealPre, Proof.AesCcm.oneLay, Proof.AesCcm.onePub,
      X86_64.abi, Proof.AesCcm.arg, Proof.AesCcm.args, Proof.AesCcm.stk16, Proof.AesCcm.ret, Proof.AesCcm.rounds,
      X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [sealSat] using sealSat)

/-- A state satisfying the precondition of `vg_aes_ccm_open`: as `sealSat`,
with the tag read only. -/
def openSat : State := { sealSat with
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩, ⟨0x3000, 4⟩, ⟨0x8008, 40⟩]
  wr := [⟨0, 0⟩, ⟨0, 2560⟩] }

/-- `open`'s public data include its leak, from which `pub` has whether it
succeeds. -/
theorem open_verified (v : UpdateImpl) :
    Verified X86_64.target («open» v.callee v.ctr.callee) (Proof.AesCcm.openScratchContract X86_64.abi 16) :=
  Verified.of_correct (open_correct v) (open_ct v)
    { pre := by sig_implies_pre [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
        Proof.AesCcm.openRoundsPost, Spec.Ccm.openLeak, Proof.AesCcm.openX86_64, Proof.AesCcm.openLeak, Proof.AesCcm.openPre,
        Proof.AesCcm.oneLay, Proof.AesCcm.onePub, X86_64.abi, Proof.AesCcm.arg, Proof.AesCcm.args,
        Proof.AesCcm.stk16, Proof.AesCcm.ret, Proof.AesCcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
        List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      post := by sig_implies_post [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
        Proof.AesCcm.openRoundsPost, Spec.Ccm.openLeak, Proof.AesCcm.openX86_64, Proof.AesCcm.openLeak, Proof.AesCcm.openPre,
        Proof.AesCcm.oneLay, Proof.AesCcm.onePub, X86_64.abi, Proof.AesCcm.arg, Proof.AesCcm.args,
        Proof.AesCcm.stk16, Proof.AesCcm.ret, Proof.AesCcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
        List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
        Proof.AesCcm.openRoundsPost, Spec.Ccm.openLeak, Proof.AesCcm.openX86_64, Proof.AesCcm.openLeak, Proof.AesCcm.openPre,
        Proof.AesCcm.oneLay, Proof.AesCcm.onePub, X86_64.abi, Proof.AesCcm.arg, Proof.AesCcm.args,
        Proof.AesCcm.stk16, Proof.AesCcm.ret, Proof.AesCcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
        List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] at h
        sig_split h
        sig_reduce [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
        Proof.AesCcm.openRoundsPost, Spec.Ccm.openLeak, Proof.AesCcm.openX86_64, Proof.AesCcm.openLeak, Proof.AesCcm.openPre,
        Proof.AesCcm.oneLay, Proof.AesCcm.onePub, X86_64.abi, Proof.AesCcm.arg, Proof.AesCcm.args,
        Proof.AesCcm.stk16, Proof.AesCcm.ret, Proof.AesCcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
        List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
        sig_simp [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
        Proof.AesCcm.openRoundsPost, Spec.Ccm.openLeak, Proof.AesCcm.openX86_64, Proof.AesCcm.openLeak, Proof.AesCcm.openPre,
        Proof.AesCcm.oneLay, Proof.AesCcm.onePub, X86_64.abi, Proof.AesCcm.arg, Proof.AesCcm.args,
        Proof.AesCcm.stk16, Proof.AesCcm.ret, Proof.AesCcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
        List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by sig_implies_sat [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
        Proof.AesCcm.openRoundsPost, Spec.Ccm.openLeak, Proof.AesCcm.openX86_64, Proof.AesCcm.openLeak, Proof.AesCcm.openPre,
        Proof.AesCcm.oneLay, Proof.AesCcm.onePub, X86_64.abi, Proof.AesCcm.arg, Proof.AesCcm.args,
        Proof.AesCcm.stk16, Proof.AesCcm.ret, Proof.AesCcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
        List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [openSat, sealSat] using openSat }

end VG.Proof.AesCcm.X86_64

end

end

/-!
# AES-CCM on x86-64, with its working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackArgScratch`): their working space is passed on the stack
after the six argument registers and four other stack arguments (`data`,
`len`, `tag` and `tag_len`), so the frame of 2608 bytes holds the 2560 bytes
of working space, a copy of those four arguments, the word that stands for
the return address and the address of the working space. The code's own
calls use 16 bytes below it: the return addresses of the call of
`vg_cmac_aes_update` (or of `vg_aes_ctr32`) and of its call of
`vg_aes_ctr32`, if it makes one (`UpdateImpl.xdepth`), which uses no stack
(`Ctr32Impl.noStack`). `open`'s leak,
whether it succeeds, reads only its buffers (`openLeak_local`).

Over an implementation of AES that needs working space (`Ctr32Impl.free` is
`none`), that frame is the working space of the functions called, wiped
whole on return (`X86_64.Scrub.withScrubAll`, `sealReg`, `openReg`): their
postconditions read the memory on return only within the data and the tag
(`sealOut`, `openOut`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.Impl.AesCcm.X86_64
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

variable (v : UpdateImpl)

theorem seal_xdepth : («seal» v.callee v.ctr.callee).x86_64Depth ≤ 16 := by
  have := v.xdepth
  simp only [«seal», sealFront, tagOut, mac, b0, aad, aadHead, absorbPad, updBlock, tag, ctr, ctrChunk, callUpdate,
    callCtr, Code.x86_64Depth, v.ctr.noStack]
  generalize v.callee.code.x86_64Depth = d at this ⊢
  revert d
  decide +kernel

theorem open_xdepth : («open» v.callee v.ctr.callee).x86_64Depth ≤ 16 := by
  have := v.xdepth
  simp only [«open», openFront, mac, b0, aad, aadHead, absorbPad, updBlock, tag, ctr, ctrChunk, callUpdate, callCtr,
    Code.x86_64Depth, v.ctr.noStack]
  generalize v.callee.code.x86_64Depth = d at this ⊢
  revert d
  decide +kernel

/-- A state satisfying `vg_aes_ccm_seal`'s precondition, without the working
space. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩, ⟨0x8008, 32⟩], wr := [⟨0, 0⟩, ⟨0x3000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesCcm.sealRoundsContract X86_64.abi 2624).pre s := by
  implies_sat [Proof.AesCcm.sealRoundsContract, Spec.Ccm.sealSig, Spec.Ccm.sealPre, Proof.AesCcm.sealRoundsPost,
    X86_64.abi, X86_64.argRegs] [sealFrameSat, sealSat] using sealFrameSat

theorem seal_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 («seal» v.callee v.ctr.callee))
      (Proof.AesCcm.sealRoundsContract X86_64.abi 2624) :=
  X86_64.Verified.stackArgScratchPre (hpostOut := sealPostOut_local _) (sig := Spec.Ccm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.sealPre X86_64.abi.ptrBits)
    (post := Proof.AesCcm.sealRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 2608) (seal_verified v) (by decide) (by decide) (by decide)
    (seal_spSafe v) (seal_xdepth v) (sealPre_local _) (sealPost_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_ccm_open`'s precondition, without the working
space. -/
def openFrameSat : State :=
  { openSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩, ⟨0x3000, 4⟩, ⟨0x8008, 32⟩], wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesCcm.openRoundsContract X86_64.abi 2624).pre s := by
  implies_sat [Proof.AesCcm.openRoundsContract, Spec.Ccm.openSig, Spec.Ccm.openPre, Proof.AesCcm.openRoundsPost,
    Spec.Ccm.openLeak, X86_64.abi, X86_64.argRegs] [openFrameSat, openSat, sealSat] using openFrameSat

theorem open_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 («open» v.callee v.ctr.callee))
      (Proof.AesCcm.openRoundsContract X86_64.abi 2624) :=
  X86_64.Verified.stackArgScratchPre (hpostOut := openPostOut_local _) (sig := Spec.Ccm.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.openPre X86_64.abi.ptrBits)
    (post := Proof.AesCcm.openRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 16)
    (leak := some (Spec.Ccm.openLeak X86_64.abi.ptrBits)) (bytes := 2608) (open_verified v)
    (by decide) (by decide) (by decide) (open_spSafe v) (open_xdepth v) (openPre_local _)
    (openPost_local _) openFrameSat_pre (hleak := openLeak_local _)

/-! ## Without secret residue -/

section
open VG.X86_64.Scrub

omit v

/-- The bytes of a buffer on which two memories agree. -/
theorem bytesAt_of {m₁ m₂ : Mem} {p : Addr} {L : Nat} (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a)
    {n : Nat} (hn : n ≤ L) : Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => (h _ (Region.contains_ofNat p (by have := List.mem_range.mp hi; omega))).symm

theorem sealOut (stack : Nat) :
    PostOut (Spec.Ccm.sealContract X86_64.abi stack) (Spec.Ccm.sealSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ccm.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ccm.sealPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ccm.sealPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ccm.sealPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [h key hk, bytesAt_of hb.2.2.2.1 (by simp), bytesAt_of hb.2.2.2.2 (by simp)]

theorem openOut (stack : Nat) :
    PostOut (Spec.Ccm.openContract X86_64.abi stack) (Spec.Ccm.openSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ccm.openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ccm.openPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ccm.openPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ccm.openPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [bytesAt_of hb.2.2.2.1 (by simp)]
      exact h key hk

section Selective

open VG.X86_64 VG.X86_64.Scrub VG.X86_64.RScrub VG.X86_64.RTaint

/-- The small regions the tight functional frame permits to change. -/
def tightChunks : List Nat := [2624]
def tightKs : List Nat := [0, 64, 80, 96, 112, 128, 144, 160, 272, 288, 304, 320]

def setupFramed : Prog isa := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 entryRestore

theorem setup_sp : setupFramed.all (fun i => !isa.writesSp i) = true :=
  X86_64.withStackArgScratch_spSafe (by decide +kernel)

local instance tightFootprint : Footprint := ⟨true⟩

/-- Every mutable workspace byte in the tight frame is wiped. -/
theorem tight_cov {p x : Addr} (hx : (⟨p - 2624, 2624⟩ : Region).Contains x 1)
    (hn : ¬ WCov tightKs tightChunks p x) {D T : Addr} {n tl : Nat}
    (hD : (⟨p - 2624, 2624⟩ : Region).Disjoint ⟨D, n⟩)
    (hT : (⟨p - 2624, 2624⟩ : Region).Disjoint ⟨T, tl⟩) :
    ∀ r ∈ mutR (p - 2560) (p - 2608) D n ++ [⟨T, tl⟩], ¬ r.Contains x 1 := by
  -- Each of the four ranges on its own: the kernel then evaluates `cov` at their 176 bytes, not at all 2624.
  have hchk : ∀ d k, (d = 0 ∧ k = 16 ∨ d = 64 ∧ k = 112 ∨ d = 280 ∧ k = 16 ∨ d = 304 ∧ k = 32) →
      ∀ i < k, cov tightKs tightChunks (d + i) = true := by
    rintro d k (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> decide +kernel
  have hj : (x - (p - 2624)).toNat < 2624 := by have := hx; simp only [Region.Contains] at this; omega
  have hc {d k : Nat} (hfit : d + k ≤ 2624)
      (hc : d = 0 ∧ k = 16 ∨ d = 64 ∧ k = 112 ∨ d = 280 ∧ k = 16 ∨ d = 304 ∧ k = 32)
      (hr : (⟨p - 2624 + BitVec.ofNat 64 d, k⟩ : Region).Contains x 1) : False := by
    have hr' : (x - (p - 2624 + BitVec.ofNat 64 d)).toNat < k := by
      simp only [Region.Contains] at hr; omega
    obtain ⟨hl, hu⟩ := (Offset.lt_iff x (p - 2624) (by omega_using [hfit])).mp hr'
    apply hn
    change (⟨p - 2624, 2624⟩ : Region).Contains x 1 ∧ cov tightKs tightChunks (x - (p - 2624)).toNat = true
    obtain h := hchk d k hc ((x - (p - 2624)).toNat - d) (by omega)
    rw [Nat.add_sub_cancel' hl] at h
    exact ⟨hx, h⟩
  intro r hr hx'
  simp only [mutR, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl | rfl) | rfl
  · apply hc (d := 64) (k := 112) (by decide) (by simp)
    change (⟨p - BitVec.ofNat 64 2624 + BitVec.ofNat 64 64, 112⟩ : Region).Contains x 1
    rw [X86_64.sub_add_ofNat p (show 64 ≤ 2624 by decide)]
    exact hx'
  · apply hc (d := 280) (k := 16) (by decide) (by simp)
    change (⟨p - BitVec.ofNat 64 2624 + BitVec.ofNat 64 280, 16⟩ : Region).Contains x 1
    change (⟨p - BitVec.ofNat 64 2560 + BitVec.ofNat 64 216, 16⟩ : Region).Contains x 1 at hx'
    rw [X86_64.sub_add_ofNat p (show 280 ≤ 2624 by decide)]
    rw [X86_64.sub_add_ofNat p (show 216 ≤ 2560 by decide)] at hx'
    exact hx'
  · apply hc (d := 304) (k := 32) (by decide) (by simp)
    change (⟨p - BitVec.ofNat 64 2624 + BitVec.ofNat 64 304, 32⟩ : Region).Contains x 1
    change (⟨p - BitVec.ofNat 64 2560 + BitVec.ofNat 64 240, 32⟩ : Region).Contains x 1 at hx'
    rw [X86_64.sub_add_ofNat p (show 304 ≤ 2624 by decide)]
    rw [X86_64.sub_add_ofNat p (show 240 ≤ 2560 by decide)] at hx'
    exact hx'
  · exact hc (d := 0) (k := 16) (by decide) (by simp)
      (by simpa [below, BitVec.sub_sub] using hx')
  · exact hD x hx hx'
  · exact hT x hx hx'

/-- Lift the body's footprint into its allocated stack frame. -/
theorem frame_entry {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
    {c : Prog isa} (hk : 6 ≤ (sig.words abi.ptrBits).length) (hns : X86_64.nStack sig = 4)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hbody : ∀ s, (Sig.scratchContract abi sig "work" .u64 320 pre post true 16 leak).pre s →
      ∃ t u, Exec isa c s t u ∧ abiPreserved s u ∧
        EntryFrame s u (stackArg s 4) (s.gpr .rsp) (stackArg s 0) (stackArg s 1).toNat
          (stackArg s 2) (stackArg s 3).toNat)
    (hc : c.all (fun i => !isa.writesSp i) = true) (hd : c.x86_64Depth ≤ 16)
    (hb : ∀ s, ∃ wd wt, (⟨stackArg s 0, (stackArg s 1).toNat⟩, wd) ∈ allRegions sig s ∧
      (⟨stackArg s 2, (stackArg s 3).toNat⟩, wt) ∈ allRegions sig s)
    {s u : State} {t : List Leak} (hs : (sig.contract abi pre post true 2624 leak).pre s)
    (he : Exec isa (Impl.StackScratch.X86_64.withStackArgScratch 2608 4 c) s t u) :
    ∃ tb ub tp pb, Exec isa c (narrowS sig .u64 320 2608 s) tb ub ∧
      Exec isa entryRestore (narrowS sig .u64 320 2608 s) tp pb ∧
      abiPreserved (narrowS sig .u64 320 2608 s) pb ∧
      u.mem = lose ub.mem (s.gpr .rsp - BitVec.ofNat 64 2608) 2608 ub.unknowns ∧
      ∀ x, (⟨s.gpr .rsp - 2624, 2624⟩ : Region).Contains x 1 →
        ¬ WCov tightKs tightChunks (s.gpr .rsp) x → ub.mem x = pb.mem x := by
  have hb' : 16 + 8 * X86_64.nStack sig + 320 * Elem.size .u64 ≤ 2608 := by rw [hns]; decide
  have hp := narrowS_pre (nm := "work") (e := .u64) (n := 320) (bytes := 2608) (stack := 16) hk hb' (by decide)
    (fun vs m₁ m₂ hl hb _ => hpre vs m₁ m₂ hl hb) hs
  obtain ⟨tb, ub, eb, ab, tp, p, ep, ap, hf⟩ := hbody _ hp
  obtain ⟨e, _, hm, _⟩ := withStackArgScratch_runMem hk ⟨hb', by decide, by decide⟩ (by decide)
    (SpSafe.of_all hc) hd hs eb ab
  rw [hns] at e
  obtain ⟨_, rfl⟩ := Exec.det he e
  refine ⟨_, _, _, _, eb, ep, ap, hm, fun x hx hn => ?_⟩
  have ha := narrowS_args (e := .u64) (n := 320) (bytes := 2608) (stack := 16) hk hb' (by decide) hs
  have hsp := (narrowS_facts (nm := "work") (e := .u64) (n := 320) (bytes := 2608) (stack := 16) hk hb' (by decide) hs).1
  have ha' := ha.2.1
  rw [hns] at ha'
  have hwork := ha.2.2.1
  rw [hns] at hwork
  simp only [show 16 + 8 * 4 = 48 from rfl, X86_64.sub_add_ofNat _ (show 48 ≤ 2608 by decide)] at hwork
  rw [hwork, hsp, ha' 0 (by decide), ha' 1 (by decide), ha' 2 (by decide), ha' 3 (by decide)] at hf
  have hr := (pre_args hk).mp hs
  obtain ⟨wd, wt, hD, hT⟩ := hb s
  have hd' := hr.2.2.2.2.1 ⟨s.gpr .rsp - 2624, 2624⟩ (by simp [stackBelow]) _ hD
  have ht' := hr.2.2.2.2.1 ⟨s.gpr .rsp - 2624, 2624⟩ (by simp [stackBelow]) _ hT
  exact hf x (tight_cov hx hn hd' ht')

private theorem overlay_empty (m : Mem) : overlay ⟨0, 0⟩ (fun _ => 0) m = m :=
  funext fun x => by simp [overlay, Region.Contains]

private theorem clear_empty (q : State) : Clear ⟨0, 0⟩ q := fun _ _ _ _ h => by simp [Region.Contains] at h

/-- `narrowS` from a state with no unknowns is `narrowS` with none. -/
theorem narrowS_zero (sig : Sig) (e : Elem) (n bytes : Nat) (s : State) :
    narrowS sig e n bytes { s with unknowns := fun _ => 0 } =
      { narrowS sig e n bytes s with unknowns := fun _ => 0 } := by
  have hG := execBlock_F (H := ⟨0, 0⟩) (F := fun q => q.patch ⟨0, 0⟩ (fun _ => 0) (fun _ => 0))
    (l := Impl.StackScratch.X86_64.setArgs bytes (X86_64.nStack sig)) (fun i _ q hc => ⟨exec_patch hc i, addrs_patch i⟩)
    (s := allocState bytes s) (clear_empty _)
  simp only [State.patch, overlay_empty] at hG
  unfold narrowS setArgsState
  rw [show allocState bytes { s with unknowns := fun _ => 0 } =
    { allocState bytes s with unknowns := fun _ => 0 } from rfl, hG]
  cases execBlock isa (Impl.StackScratch.X86_64.setArgs bytes (X86_64.nStack sig)) (allocState bytes s) <;> rfl

/-- The public setup's run from `s` with no unknowns (`lose` then keeps
every byte): its memory is that of `entryRestore`'s run from `narrowS s`. -/
theorem setup_zero {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
    (hk : 6 ≤ (sig.words abi.ptrBits).length) (hns : X86_64.nStack sig = 4) {s : State}
    (hs' : (sig.contract abi pre post true 2624 leak).pre { s with unknowns := fun _ => 0 })
    {tp : List Leak} {pb : State}
    (ep : Exec isa entryRestore (narrowS sig .u64 320 2608 s) tp pb)
    (ap : abiPreserved (narrowS sig .u64 320 2608 s) pb) :
    ∃ t' u', Exec isa setupFramed { s with unknowns := fun _ => 0 } t' u' ∧ u'.mem = pb.mem := by
  have hb' : 16 + 8 * X86_64.nStack sig + 320 * Elem.size .u64 ≤ 2608 := by rw [hns]; decide
  have ep' := Exec.F (H := ⟨0, 0⟩) (F := fun q => q.patch ⟨0, 0⟩ (fun _ => 0) (fun _ => 0))
    (c := entryRestore) (by decide) (fun i _ q hc => ⟨exec_patch hc i, addrs_patch i⟩)
    (fun k _ => eval_patch k) ep (clear_empty _)
  simp only [State.patch, overlay_empty] at ep'
  replace ep' : Exec isa entryRestore (narrowS sig .u64 320 2608 { s with unknowns := fun _ => 0 }) tp
      { pb with unknowns := fun _ => 0 } := by
    rw [narrowS_zero]; exact ep'
  obtain ⟨e', -, hm', -⟩ := withStackArgScratch_runMem (c := entryRestore) hk ⟨hb', by decide, by decide⟩
    (by decide) (SpSafe.of_all (by decide +kernel : entryRestore.all (fun i => !isa.writesSp i) = true))
    (by decide : entryRestore.x86_64Depth ≤ 16) hs' ep' (by rw [narrowS_zero]; unfold abiPreserved; dsimp only; exact ap)
  rw [hns] at e'
  refine ⟨_, _, e', ?_⟩
  rw [hm']
  funext x
  simp [lose]

theorem seal_scratch_pre : ∀ s, (Proof.AesCcm.sealScratchContract abi 16).pre s → sealX86_64.pre s := by
  sig_implies_pre [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre,
        Proof.AesCcm.sealRoundsPost, Proof.AesCcm.sealX86_64, Proof.AesCcm.sealPre,
        Proof.AesCcm.oneLay, Proof.AesCcm.onePub, X86_64.abi, Proof.AesCcm.arg, Proof.AesCcm.args,
        Proof.AesCcm.stk16, Proof.AesCcm.ret, Proof.AesCcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
        List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]

theorem seal_bufs (s : State) : ∃ wd wt,
    (⟨stackArg s 0, (stackArg s 1).toNat⟩, wd) ∈ allRegions Spec.Ccm.sealSig s ∧
    (⟨stackArg s 2, (stackArg s 3).toNat⟩, wt) ∈ allRegions Spec.Ccm.sealSig s := by
  refine ⟨true, true, ?_, ?_⟩ <;>
    simp [allRegions, bufRegions, allArgs, Spec.Ccm.sealSig, Sig.bufs, Sig.words, Param.words,
      argRegs, abi, List.range, List.range.loop, Elem.size]

theorem open_scratch_pre : ∀ s, (Proof.AesCcm.openScratchContract abi 16).pre s → openX86_64.pre s := by
  sig_implies_pre [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
        Proof.AesCcm.openRoundsPost, Proof.AesCcm.openX86_64, Proof.AesCcm.openPre,
        Proof.AesCcm.oneLay, Proof.AesCcm.onePub, X86_64.abi, Proof.AesCcm.arg, Proof.AesCcm.args,
        Proof.AesCcm.stk16, Proof.AesCcm.ret, Proof.AesCcm.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD,
        List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs, Spec.Ccm.openLeak, Proof.AesCcm.openLeak]

theorem open_bufs (s : State) : ∃ wd wt,
    (⟨stackArg s 0, (stackArg s 1).toNat⟩, wd) ∈ allRegions Spec.Ccm.openSig s ∧
    (⟨stackArg s 2, (stackArg s 3).toNat⟩, wt) ∈ allRegions Spec.Ccm.openSig s := by
  refine ⟨true, false, ?_, ?_⟩ <;>
    simp [allRegions, bufRegions, allArgs, Spec.Ccm.openSig, Sig.bufs, Sig.words, Param.words,
      argRegs, abi, List.range, List.range.loop, Elem.size]

end Selective

/-- `Spec.Ccm.sealApi`'s function over `v`, as emitted (`Impl.AesCcm.X86_64.Fn.«seal»`), its frame wiped
whole on return, meets its contract in constant time and returns without
secret residue: its code is its code over a stub, with `v`'s where it calls
them (`Fill`). -/
theorem seal_scrubbed (v : UpdateImpl) :
    VerifiedScrubbed target (Impl.AesCcm.X86_64.Fn.«seal» (v.level.join v.ctr.level) v.callee v.ctr.callee)
      (Spec.Ccm.sealApi.contract X86_64.abi 2624) 0 := by
  have := X86_64.Scrub.calleeSide_mono (X86_64.Scrub.level_join_left v.level v.ctr.level) (Nat.le_refl _) v.side
  have := X86_64.Scrub.calleeSide_mono (n' := 8) (X86_64.Scrub.level_join_right v.level v.ctr.level) (Nat.zero_le _) v.ctr.side
  exact X86_64.Scrub.verifiedScrubbedAllFill (api := Spec.Ccm.sealApi) (ks := 0) (n := fun s => if s = "u" then 8 else 8)
    (a := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 («seal» ⟨"u", .block []⟩ ⟨"", .block [], v.ctr.callee.scrOff⟩))
    { suffix := v.suffix
      code := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 («seal» v.callee v.ctr.callee)
      stack := 2624
      verified := Proof.AesCcm.seal_keyed (seal_framed v)
      spSafe := X86_64.withStackArgScratch_spSafe (seal_spSafe v) }
    _ (sealOut _) (by fill_calls) (Nat.zero_le _) (Nat.le_refl _)
    (ha := by rcases v.ctr.scrOk with h | h <;> rw [h] <;> lit_decide)

theorem seal_spSafeFn (v : UpdateImpl) :
    (Impl.AesCcm.X86_64.Fn.«seal» (v.level.join v.ctr.level) v.callee v.ctr.callee).all (fun i => !X86_64.isa.writesSp i) = true :=
  X86_64.Scrub.scrubKs_spSafe (X86_64.withStackArgScratch_spSafe (seal_spSafe v))

/-- `Spec.Ccm.openApi`'s function over `v`, as emitted (`Impl.AesCcm.X86_64.Fn.«open»`), its frame wiped
whole on return, meets its contract in constant time and returns without
secret residue: its code is its code over a stub, with `v`'s where it calls
them (`Fill`). -/
theorem open_scrubbed (v : UpdateImpl) :
    VerifiedScrubbed target (Impl.AesCcm.X86_64.Fn.«open» (v.level.join v.ctr.level) v.callee v.ctr.callee)
      (Spec.Ccm.openApi.contract X86_64.abi 2624) 32 := by
  have := X86_64.Scrub.calleeSide_mono (X86_64.Scrub.level_join_left v.level v.ctr.level) (Nat.le_refl _) v.side
  have := X86_64.Scrub.calleeSide_mono (n' := 8) (X86_64.Scrub.level_join_right v.level v.ctr.level) (Nat.zero_le _) v.ctr.side
  exact X86_64.Scrub.verifiedScrubbedAllFill (api := Spec.Ccm.openApi) (ks := 0) (n := fun s => if s = "u" then 8 else 8)
    (a := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 («open» ⟨"u", .block []⟩ ⟨"", .block [], v.ctr.callee.scrOff⟩))
    { suffix := v.suffix
      code := Impl.StackScratch.X86_64.withStackArgScratch 2608 4 («open» v.callee v.ctr.callee)
      stack := 2624
      verified := Proof.AesCcm.open_keyed (open_framed v)
      spSafe := X86_64.withStackArgScratch_spSafe (open_spSafe v) }
    _ (openOut _) (by fill_calls) (Nat.zero_le _) (Nat.le_refl _)
    (ha := by rcases v.ctr.scrOk with h | h <;> rw [h] <;> lit_decide)

theorem open_spSafeFn (v : UpdateImpl) :
    (Impl.AesCcm.X86_64.Fn.«open» (v.level.join v.ctr.level) v.callee v.ctr.callee).all (fun i => !X86_64.isa.writesSp i) = true :=
  X86_64.Scrub.scrubKs_spSafe (X86_64.withStackArgScratch_spSafe (open_spSafe v))

end

end VG.Proof.AesCcm.X86_64
