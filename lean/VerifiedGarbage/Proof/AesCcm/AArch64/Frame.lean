module

public import VerifiedGarbage.Proof.AesCcm.Scratch
import VerifiedGarbage.Proof.AesCcm.AArch64.OpenCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.AesCcm.AArch64
public import VerifiedGarbage.Proof.AesCcm.AArch64.Env
public import VerifiedGarbage.Proof.CmacAes.AArch64.Variant
import VerifiedGarbage.Proof.AesCcm.AArch64.Open
import VerifiedGarbage.Proof.AesCcm.AArch64.Seal
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.AesCcm.AArch64.CtrCT
import VerifiedGarbage.Proof.AesCcm.AArch64.Rel
import VerifiedGarbage.Proof.AesCcm.AArch64.Crypt
import VerifiedGarbage.Proof.AesCcm.AArch64.Tag
import VerifiedGarbage.Proof.AesCcm.AArch64.Mac
import VerifiedGarbage.Proof.AesCcm.BytesAt
meta import VerifiedGarbage.Impl.AesCcm.AArch64
meta import VerifiedGarbage.Proof.AesCcm.AArch64.Env
meta import VerifiedGarbage.Proof.CmacAes.AArch64.Variant
meta import VerifiedGarbage.Proof.AesCcm.AArch64.CtrCT
meta import VerifiedGarbage.Proof.AesCcm.AArch64.Rel
meta import VerifiedGarbage.Proof.AesCcm.AArch64.Seal
meta import VerifiedGarbage.Proof.AesCcm.AArch64.Crypt
meta import VerifiedGarbage.Proof.AesCcm.AArch64.Tag
meta import VerifiedGarbage.Proof.AesCcm.AArch64.Mac
meta import VerifiedGarbage.Proof.AesCcm.BytesAt

/-! ### `AesCcm.AArch64.SealCT`, which only this module used -/

section

/-!
# AES-CCM on AArch64: `vg_aes_ccm_seal` is constant time

Untrusted: everything here is checked by Lean. Two runs with the same public
arguments (`args_two`): the entry by `entry_rel`, `Ctr₀` by the taint
analysis, the MAC by `mac_rel`, the tag by `tag_rel` and the encryption by
`ctr_rel`; the load of the address of `tag` from its slot by the taint
analysis, and the copy of the tag there and the restore by the taint
analysis from that address, which correctness says both runs load; between
them, the states the correctness proofs describe
(`Proof.AesGcm.AArch64.rel_seq`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.Taint VG.Impl.AesCcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq ct_of)
open VG.Proof.AesCcm (length_bytesAt)

theorem seal_ct (v : Proof.CmacAes.AArch64.UpdateImpl) :
    ConstantTime isa sealAArch64.pre sealAArch64.pub (Impl.AesCcm.AArch64.seal v.callee v.ctr.callee) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨A₁, A₂⟩ := args_two (args_of_seal h₁).1 (args_of_seal h₂).1 hq
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, -, -⟩ := hq
  have L := A₁.lay
  refine rel_seq (entry_rel A₁ A₂ (by agree_tac [q0, q1, q2, q3, q4, q5, q6, q7])) (entry_ok A₁) (entry_ok A₂)
    fun τ₁ τ₂ En₁ En₂ => ?_
  refine rel_seq (rel_env [.x2, .x3] En₁.env En₂.env (by agree_tac [En₁.x2, En₂.x2, En₁.x3, En₂.x3])
      ⟨_, by taint_decide⟩)
    (ctrs_ok L En₁.env (A₁.nonce.of_eq En₁.rd En₁.wr) En₁.x2 En₁.x3)
    (ctrs_ok L En₂.env (A₂.nonce.of_eq En₂.rd En₂.wr) En₂.x2 En₂.x3)
    fun ρ₁ ρ₂ ⟨E₁, f₁, c₁, _, _⟩ ⟨E₂, f₂, c₂, _, _⟩ => ?_
  have S₁ := En₁.slots.mut L (f₁.sub (frame_ctrs_mut _))
  have S₂ := En₂.slots.mut L (f₂.sub (frame_ctrs_mut _))
  have hn₁ := length_bytesAt τ₁.mem (σ₁.gpr .x2) (cxOf σ₁).nl
  have hn₂ := length_bytesAt τ₂.mem (σ₁.gpr .x2) (cxOf σ₁).nl
  refine rel_seq (mac_rel v L E₁ E₂ (.inl rfl) S₁ S₂ hn₁ hn₂ c₁ c₂) (mac_ok v L E₁ S₁ hn₁ c₁ (.inl rfl))
    (mac_ok v L E₂ S₂ hn₂ c₂ (.inl rfl)) fun κ₁ κ₂ M₁ M₂ => ?_
  have d₁ := (Proof.AesGcm.AArch64.bytesAt_frame M₁.frame (macR_c0 L (.inl rfl)) (by decide)).trans c₁
  have d₂ := (Proof.AesGcm.AArch64.bytesAt_frame M₂.frame (macR_c0 L (.inl rfl)) (by decide)).trans c₂
  refine rel_seq (tag_rel v.ctr L M₁.env M₂.env hn₁ hn₂ d₁ d₂ (.inl rfl)) (tag_ok v.ctr L M₁.env hn₁ d₁ (.inl rfl))
    (tag_ok v.ctr L M₂.env hn₂ d₂ (.inl rfl)) fun ω₁ ω₂ ⟨F₁, _, _, g₁, _⟩ ⟨F₂, _, _, g₂, _⟩ => ?_
  have e₁ := (Proof.AesGcm.AArch64.bytesAt_frame g₁ (tagR_c0 L (.inl rfl)) (by decide)).trans d₁
  have e₂ := (Proof.AesGcm.AArch64.bytesAt_frame g₂ (tagR_c0 L (.inl rfl)) (by decide)).trans d₂
  refine rel_seq (ctr_rel v.ctr L F₁ F₂ hn₁ hn₂ e₁ e₂) (ctr_ok v.ctr L F₁ hn₁ e₁) (ctr_ok v.ctr L F₂ hn₂ e₂)
    fun π₁ π₂ ⟨G₁, _, _, h₁, _⟩ ⟨G₂, _, _, h₂, _⟩ => ?_
  have T₁ := S₁.mut L ((M₁.frame.sub (macR_mut (.inl rfl))).trans ((g₁.sub (tagR_mut _ (.inl rfl))).trans
    (h₁.sub (ctrR_mut _))))
  have T₂ := S₂.mut L ((M₂.frame.sub (macR_mut (.inl rfl))).trans ((g₂.sub (tagR_mut _ (.inl rfl))).trans
    (h₂.sub (ctrR_mut _))))
  refine rel_seq (rel_env [] G₁ G₂ (by simp) ⟨_, by taint_decide⟩) (loadTag_ok G₁ T₁ .x11) (loadTag_ok G₂ T₂ .x11)
    fun ρ₁ ρ₂ ⟨x₁, og₁, _, sp₁, rd₁, wr₁⟩ ⟨x₂, og₂, _, sp₂, rd₂, wr₂⟩ => ?_
  exact rel_env [.x11] (G₁.others og₁ (by decide) sp₁ rd₁ wr₁) (G₂.others og₂ (by decide) sp₂ rd₂ wr₂)
    (by agree_tac [x₁, x₂]) ⟨_, by taint_decide⟩

end VG.Proof.AesCcm.AArch64

end

end

/-! ### `AesCcm.AArch64.Verified`, which only this module used -/

section

/-!
# AES-CCM on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementation `v` of `vg_cmac_aes_update`, with the `vg_aes_ctr32`
that goes with it), states satisfying the preconditions, and the shared
contracts of `Spec/Ccm/Contract.lean` with the working space as a last
argument (`Proof/AesCcm/Scratch.lean`), with no stack: the calls keep the
return address in `x30`, which each function saves in the working space.
`Frame.lean` allocates the working space.
-/

@[expose] public section

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.Impl.AesCcm.AArch64

/-! ## v8–v15 -/

theorem seal_keepsV (v : Proof.CmacAes.AArch64.UpdateImpl) :
    («seal» v.callee v.ctr.callee).allInstrs keepsV = true := by
  simp only [«seal», mac, b0, flagsSeg, aadHead, header, absorbPad, absTail, updBlock, tag, ctr, ctrChunk,
    ctrTail, ctrs, tagOut, callUpdate, callCtr, Code.allInstrs, v.keepsV, v.ctr.keepsV]
  decide +kernel

theorem open_keepsV (v : Proof.CmacAes.AArch64.UpdateImpl) :
    («open» v.callee v.ctr.callee).allInstrs keepsV = true := by
  simp only [«open», mac, b0, flagsSeg, aadHead, header, absorbPad, absTail, updBlock, tag, ctr, ctrChunk,
    ctrTail, ctrs, cmp, mask, callUpdate, callCtr, Code.allInstrs, v.keepsV, v.ctr.keepsV]
  decide +kernel

/-! ## Correctness and constant time -/

theorem seal_correct (v : Proof.CmacAes.AArch64.UpdateImpl) (s : State) (hs : sealAArch64.pre s) :
    ∃ t s', Exec isa («seal» v.callee v.ctr.callee) s t s' ∧ abiPreserved s s' ∧ sealAArch64.post s s' :=
  WP.withPreservedV (seal_wp v hs) (seal_keepsV v)

theorem open_correct (v : Proof.CmacAes.AArch64.UpdateImpl) (s : State) (hs : openAArch64.pre s) :
    ∃ t s', Exec isa («open» v.callee v.ctr.callee) s t s' ∧ abiPreserved s s' ∧ openAArch64.post s s' :=
  WP.withPreservedV (open_wp v hs) (open_keepsV v)

/-- A state satisfying the precondition of `vg_aes_ccm_seal`: a 7-byte nonce,
no associated data, no data, a 4-byte tag at `0x5000` and `work` at 0. -/
def sealSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 7 | .x4 => 0x3000 | .x6 => 0x4000 | _ => 0
  sp := 0x8000
  mem a := if a = 0x8008 then 4 else if a = 0x8001 then 0x50 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x8000, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩, ⟨0, 2560⟩]

/-- A state satisfying the precondition of `vg_aes_ccm_open`: as `sealSat`,
with the tag read only. -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x8000, 24⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0, 2560⟩] }

/-! ## The shared contracts -/

theorem seal_verified (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target («seal» v.callee v.ctr.callee) (Proof.AesCcm.sealScratchContract AArch64.abi) :=
  Verified.of_correct (seal_correct v) (seal_ct v) (by
    sig_implies [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre, Proof.AesCcm.sealRoundsPost,
      sealAArch64, sealPre, oneLay, onePub, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg,
      AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat)

theorem open_verified (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target («open» v.callee v.ctr.callee) (Proof.AesCcm.openScratchContract AArch64.abi) :=
  Verified.of_correct (open_correct v) (open_ct v) (by
    sig_implies [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre, Proof.AesCcm.openRoundsPost,
      Spec.Ccm.openLeak, openAArch64, openPre, oneLay, onePub, openRes, openLeak, args, rounds, AArch64.abi,
      AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range, List.range.loop]
      [openSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat)

end VG.Proof.AesCcm.AArch64

end

end


/-!
# AES-CCM on AArch64, with its working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (`Verified.lean`), in a frame that allocates it
(`Verified.stackArgScratch`): their working space is their third stack
argument, after `tag` and `tag_len`, so the frame of 2592 bytes holds a copy
of those two, the address of the working space and the working space, at the
next 16-byte boundary. The code itself uses no stack: its calls keep the
return address in `x30`. `open`'s leak, whether it succeeds, reads only its
buffers (`openLeak_local`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.Impl.AesCcm.AArch64

/-- A state satisfying `vg_aes_ccm_seal`'s precondition, without the working
space: `tag` and `tag_len`, its two stack arguments. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x8000, 16⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesCcm.sealRoundsContract AArch64.abi 2592).pre s := by
  implies_sat [Proof.AesCcm.sealRoundsContract, Spec.Ccm.sealSig, Spec.Ccm.sealPre, Proof.AesCcm.sealRoundsPost,
    AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
    List.range.loop] [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 («seal» v.callee v.ctr.callee))
      (Proof.AesCcm.sealRoundsContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Ccm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.sealPre AArch64.abi.ptrBits)
    (post := Proof.AesCcm.sealRoundsPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (seal_verified v) (by decide) (by decide) (sealPre_local _) (sealPost_local _)
    (sealPostOut_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_ccm_open`'s precondition, without the working
space: `tag` and `tag_len`, its two stack arguments. -/
def openFrameSat : State :=
  { openSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x8000, 16⟩],
                 wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesCcm.openRoundsContract AArch64.abi 2592).pre s := by
  implies_sat [Proof.AesCcm.openRoundsContract, Spec.Ccm.openSig, Spec.Ccm.openPre, Proof.AesCcm.openRoundsPost,
    Spec.Ccm.openLeak, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr,
    List.getD, List.range, List.range.loop] [openFrameSat, openSat, sealSat, stackArg, stackArgAddr,
    Mem.readW, Mem.read] using openFrameSat

theorem open_framed (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 («open» v.callee v.ctr.callee))
      (Proof.AesCcm.openRoundsContract AArch64.abi 2592) :=
  AArch64.Verified.stackArgScratch (sig := Spec.Ccm.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.openPre AArch64.abi.ptrBits)
    (post := Proof.AesCcm.openRoundsPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592)
    (leak := some (Spec.Ccm.openLeak AArch64.abi.ptrBits))
    (open_verified v) (by decide) (by decide) (openPre_local _) (openPost_local _)
    (openPostOut_local _) openFrameSat_pre
    (hleak := openLeak_local _)

end VG.Proof.AesCcm.AArch64
