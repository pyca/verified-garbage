module

public import VerifiedGarbage.Proof.AesOcb.Scratch
import VerifiedGarbage.Proof.AesOcb.X86_64.InitCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesOcb.X86_64.Seal
public import VerifiedGarbage.Proof.AesOcb.X86_64.Nonce
import VerifiedGarbage.Proof.AesOcb.X86_64.Open
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.AesOcb.X86_64.SealCT
import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.AesOcb.X86_64.SealCT
meta import VerifiedGarbage.Proof.AesOcb.X86_64.Open
meta import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Impl.AesOcb.X86_64
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.TCB.X86_64.State

/-! ### `AesOcb.X86_64.OpenCT`, which only this module used -/

section

/-!
# AES-OCB on x86-64: `vg_aes_ocb_open` is constant time

Untrusted: everything here is checked by Lean. As `seal` (`front_rel`), then
the copy of the received tag to `W`, the comparison, the mask and `restore`,
which pass the taint analysis from the public slots and the address of the
tag at `W + tgO`: the comparison's result is a value, not a branch.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (BlocksImpl)

section
variable {s₀ s₀' : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {Tg : Addr}
  (T : Two s₀ s₀' K W SP N A D R nl al n tl Tg)
include T

/-- `recv` keeps the public arguments. -/
theorem recv_one {s : State} (o : OneT K W SP R N A D nl n tl Tg s) :
    WP isa recv s (One K W SP R N A D nl n tl) := by
  refine WP.mono (recv_ok o.1.env T.ar.t1 T.ar.t16 o.2.1 o.1.sl.tl o.2.2 T.ar.tag.w) fun t ⟨m, g, rd, wr⟩ => ?_
  have fr : Frame (mutR W SP D n) s.mem t.mem := by
    rw [m]
    refine (writeBytes_frame _ _ _ (by rw [Proof.AesCcm.X86_64.length_bytesAt]; exact Region.contains_self _ _)).sub
      fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by have := T.ar.t16; omega_using [this])⟩
  exact o.1.step T.ar.lay T.ar.data.w (o.1.env.keep g rd wr) wr fr

/-- The comparison keeps the public arguments, and leaves 1 or 0 at `W`. -/
theorem cmpRes {s : State} (o : One K W SP R N A D nl n tl s) :
    WP isa cmp s fun t => One K W SP R N A D nl n tl t ∧
      ∃ c : Bool, t.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64 := by
  refine WP.mono (cmp_ok o.env T.ar.t1 T.ar.t16 o.sl.tl) fun t ⟨m, g, rd, wr⟩ => ?_
  have E : Env K W SP t := o.env.keep (fun r hr => g r
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd wr
  have fr : Frame (mutR W SP D n) s.mem t.mem := by
    rw [m]
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)).sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
  refine ⟨o.step T.ar.lay T.ar.data.w E wr fr, decide (bytesAt s.mem W tl = bytesAt s.mem (W + BitVec.ofNat 64 t2O) tl),
    ?_⟩
  rw [m, Mem.readW_writeW_self64]; simp only [decide_eq_true_eq]

/-- The mask keeps the public arguments. -/
theorem mask_one {s : State} (o : One K W SP R N A D nl n tl s) {c : Bool}
    (hok : s.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64) :
    WP isa mask s (One K W SP R N A D nl n tl) := by
  refine WP.mono (mask_ok o.env o.sl.data o.sl.len (T.ar.data.of_one o) hok) fun t ⟨E, _, wr, m⟩ => ?_
  have fr : Frame (mutR W SP D n) s.mem t.mem := by
    rw [m]
    refine (writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)).sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  exact o.step T.ar.lay T.ar.data.w E wr fr

variable (hw : s₀.wr = [⟨D, n⟩, ⟨W, 3584⟩]) (hw' : s₀'.wr = [⟨D, n⟩, ⟨W, 3584⟩])
include hw hw'

/-- `vg_aes_ocb_open` in two runs. -/
theorem open_rel (v : BlocksImpl) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') («open» (callees v)) fun _ _ => True := by
  have hDW := T.ar.data.w
  have hn : n ≤ 2 ^ 64 := Nat.le_of_lt T.ar.data.lt
  have fr := front_rel T hw hw' v false (.inr rfl)
  have rr := (rel_taintC [] [tgO] hDW hn (fun a b (h : True ∧ OneT K W SP R N A D nl n tl Tg a ∧
    OneT K W SP R N A D nl n tl Tg b) => ⟨h.2.1.1.env, h.2.2.1.env, h.2.1.1.sl, h.2.2.1.sl, h.2.1.1.wr, h.2.2.1.wr,
      fun _ h => (nomatch h), fun d hd => by
        simp only [List.mem_singleton] at hd; subst hd; exact ⟨by decide, by rw [h.2.1.2.1, h.2.2.2.1]⟩⟩)
    (c := recv) ⟨_, by taint_decide⟩).wp
    (F₁ := One K W SP R N A D nl n tl) (F₂ := One K W SP R N A D nl n tl)
    fun a b h => ⟨recv_one T h.2.1, recv_one T h.2.2⟩
  have cc := (rel_taintC [] [] hDW hn (fun a b (h : True ∧ One K W SP R N A D nl n tl a ∧
    One K W SP R N A D nl n tl b) => Both.of h.2.1 h.2.2) (c := cmp) ⟨_, by taint_decide⟩).wp
    (F₁ := fun (s : State) => One K W SP R N A D nl n tl s ∧ ∃ c : Bool, s.mem.readW (W + BitVec.ofNat 64 tagO) 64 =
      if c then 1#64 else 0#64)
    (F₂ := fun (s : State) => One K W SP R N A D nl n tl s ∧ ∃ c : Bool, s.mem.readW (W + BitVec.ofNat 64 tagO) 64 =
      if c then 1#64 else 0#64)
    fun a b h => ⟨cmpRes T h.2.1, cmpRes T h.2.2⟩
  have mm := (rel_taintC [] [] hDW hn (fun a b (h : True ∧ (One K W SP R N A D nl n tl a ∧
      ∃ c : Bool, a.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64) ∧
    (One K W SP R N A D nl n tl b ∧
      ∃ c : Bool, b.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64)) => Both.of h.2.1.1 h.2.2.1)
    (c := mask) ⟨_, by taint_decide⟩).wp
    (F₁ := One K W SP R N A D nl n tl) (F₂ := One K W SP R N A D nl n tl)
    fun a b h => ⟨mask_one T h.2.1.1 h.2.1.2.choose_spec, mask_one T h.2.2.1 h.2.2.2.choose_spec⟩
  have rs := rel_taintC [] [] hDW hn (fun a b (h : True ∧ One K W SP R N A D nl n tl a ∧
    One K W SP R N A D nl n tl b) => Both.of h.2.1 h.2.2) (c := .block ([ld .rax .r15 tagO] ++ restore))
    ⟨_, by taint_decide⟩
  unfold «open»
  exact RelCT.seq fr (RelCT.seq rr (RelCT.seq cc (RelCT.seq mm rs)))

end

/-- `vg_aes_ocb_open` is constant time. -/
theorem open_ct (v : BlocksImpl) : ConstantTime isa openX86_64.pre openX86_64.pub («open» (callees v)) :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hq e₁ e₂ => by
    have T := Two.of hq.1 (openArgs_of h₁) (openArgs_of h₂)
    obtain ⟨⟨q1, q2, q3, q4, q5, q6, q7, q8⟩, -⟩ := hq
    have hw₂ : s₂.wr = [⟨arg s₁ 0, (arg s₁ 1).toNat⟩, ⟨arg s₁ 4, 3584⟩] := by
      rw [h₂.2.1, q8 0 (by decide), q8 1 (by decide), q8 4 (by decide)]
    exact (open_rel T h₁.2.1 hw₂ v _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesOcb.X86_64

end

end

/-! ### `AesOcb.X86_64.Verified`, which only this module used -/

section

/-!
# AES-OCB on x86-64: `Verified`

Correctness and constant time (for any implementations `v` of
`vg_aes_encrypt_blocks`, `vg_aes_decrypt_blocks` and `vg_aes_expand_key_scratch`),
a state satisfying each precondition, and the shared contracts of
`Spec/Ocb/Contract.lean` with the working space as a last argument
(`Proof/AesOcb/Scratch.lean`; 3584 bytes for `seal` and `open`, 2560 for
`init`), with 8 bytes of stack: the return address of
the calls, whose callees use no stack. `Frame.lean` allocates the working
space.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.Impl.AesOcb.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)

theorem seal_mx (v : BlocksImpl) : («seal» (callees v)).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [«seal», front, tagOut, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill, hashSum, hashRest, padTo, body,
    whole, pass, nextOffset, rest, padCk, xorPad, tag, callBlocks, callees, Code.allInstrs, v.encMxcsr, v.decMxcsr,
    Bool.true_and, Bool.and_true, ↓reduceIte]
  decide +kernel

theorem open_mx (v : BlocksImpl) : («open» (callees v)).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [«open», front, recv, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill, hashSum, hashRest, padTo, body,
    whole, pass, nextOffset, rest, padCk, xorPad, tag, cmp, mask, callBlocks, callees, Code.allInstrs, v.encMxcsr,
    v.decMxcsr, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

theorem init_mx (v : BlocksImpl) : (init (callees v)).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [init, callees, Code.allInstrs, v.encMxcsr, v.expandMxcsr, Bool.true_and, Bool.and_true]
  decide +kernel

theorem seal_spSafe (v : BlocksImpl) : («seal» (callees v)).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [«seal», front, tagOut, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill, hashSum, hashRest, padTo, body,
    whole, pass, nextOffset, rest, padCk, xorPad, tag, callBlocks, callees, Code.all, v.encSpSafe, v.decSpSafe,
    Bool.true_and, Bool.and_true, ↓reduceIte]
  decide +kernel

theorem open_spSafe (v : BlocksImpl) : («open» (callees v)).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [«open», front, recv, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill, hashSum, hashRest, padTo, body,
    whole, pass, nextOffset, rest, padCk, xorPad, tag, cmp, mask, callBlocks, callees, Code.all, v.encSpSafe,
    v.decSpSafe, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

theorem init_spSafe (v : BlocksImpl) : (init (callees v)).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [init, callees, Code.all, v.encSpSafe, v.expandSpSafe, Bool.true_and, Bool.and_true]
  decide +kernel

theorem seal_correct (v : BlocksImpl) (s : State) (hs : sealX86_64.pre s) :
    ∃ t s', Exec isa («seal» (callees v)) s t s' ∧ abiPreserved s s' ∧ sealX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := seal_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (seal_mx v) he hg, hp⟩

theorem open_correct (v : BlocksImpl) (s : State) (hs : openX86_64.pre s) :
    ∃ t s', Exec isa («open» (callees v)) s t s' ∧ abiPreserved s s' ∧ openX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := open_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (open_mx v) he hg, hp⟩

theorem init_correct (v : BlocksImpl) (s : State) (hs : initX86_64.pre s) :
    ∃ t s', Exec isa (init (callees v)) s t s' ∧ abiPreserved s s' ∧ initX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := init_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (init_mx v) he hg, hp⟩

/-- A state satisfying the precondition of `vg_aes_ocb_seal`: a 1-byte nonce,
no associated data, no data, a 4-byte tag at `0x3000` and `work` at 0. -/
def sealSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 1 | .r8 => 0x2100 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8020 then 4 else if a = 0x8019 then 0x30 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x2100, 0⟩, ⟨0x8008, 40⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 4⟩, ⟨0, 3584⟩]

/-- A state satisfying the precondition of `vg_aes_ocb_init`: a 16-byte key. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩]

theorem seal_verified (v : BlocksImpl) :
    Verified X86_64.target («seal» (callees v)) (Proof.AesOcb.sealWorkContract X86_64.abi 448 8) :=
  Verified.of_correct (seal_correct v) (seal_ct v) (by
    sig_implies [Proof.AesOcb.sealWorkContract, Proof.AesOcb.sealWorkSig, Spec.Ocb.sealPre,
      Proof.AesOcb.sealRoundsPost, Proof.AesOcb.sealX86_64, Proof.AesOcb.sealPreX, Proof.AesOcb.oneFacts,
      Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad, Proof.AesOcb.aData, Proof.AesOcb.aTag,
      Proof.AesOcb.aWork, Proof.AesOcb.onePub, X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8,
      Proof.AesOcb.ret, Proof.AesOcb.rounds, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range,
      List.range.loop, VG.X86_64.below, X86_64.argRegs] [sealSat] using sealSat)

theorem initF_correct (v : BlocksImpl) (f : Proof.Aes.X86_64.BlocksFree v.enc v.expand) (s : State)
    (hs : initX86_64F.pre s) :
    ∃ t s', Exec isa (init (callees v)) s t s' ∧ abiPreserved s s' ∧ initX86_64F.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := initF_wp v f hs
  exact ⟨t, s', he, abiPreserved_of_exec (init_mx v) he hg, hp⟩

/-- A state satisfying the precondition of `vg_aes_ocb_init` with 24 bytes of
working space. -/
def initSatF : State := { initSat with wr := [⟨0x2000, 256⟩, ⟨0x4000, 24⟩] }

theorem initF_verified (v : BlocksImpl) (f : Proof.Aes.X86_64.BlocksFree v.enc v.expand) :
    Verified X86_64.target (init (callees v)) (Proof.AesOcb.initScratchContractF X86_64.abi 8) :=
  Verified.of_correct (initF_correct v f) (initF_ct v f) (by
    sig_implies [Proof.AesOcb.initScratchContractF, Proof.AesOcb.initScratchSigF, Spec.Ocb.initPre,
      Spec.Ocb.initPost, Proof.AesOcb.initX86_64F, Proof.AesOcb.initX86_64, Proof.AesOcb.stk8, Proof.AesOcb.ret,
      X86_64.abi, X86_64.argRegs, VG.X86_64.below] [initSatF, initSat] using initSatF)

theorem init_verified (v : BlocksImpl) :
    Verified X86_64.target (init (callees v)) (Proof.AesOcb.initScratchContract X86_64.abi 8) :=
  Verified.of_correct (init_correct v) (init_ct v) (by
    sig_implies [Proof.AesOcb.initScratchContract, Proof.AesOcb.initScratchSig, Spec.Ocb.initPre,
      Spec.Ocb.initPost, Proof.AesOcb.initX86_64, Proof.AesOcb.stk8, Proof.AesOcb.ret, X86_64.abi, X86_64.argRegs,
      VG.X86_64.below] [initSat] using initSat)

/-- A state satisfying the precondition of `vg_aes_ocb_open`: as `sealSat`,
with the tag read only. -/
def openSat : State := { sealSat with
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x2100, 0⟩, ⟨0x3000, 4⟩, ⟨0x8008, 40⟩]
  wr := [⟨0, 0⟩, ⟨0, 3584⟩] }

/-- `open`'s public data include its leak, from which `pub` has whether it
succeeds. -/
theorem open_verified (v : BlocksImpl) :
    Verified X86_64.target («open» (callees v)) (Proof.AesOcb.openWorkContract X86_64.abi 448 8) :=
  Verified.of_correct (open_correct v) (open_ct v)
    { pre := by sig_implies_pre [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs]
      post := by sig_implies_post [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs] at h
        sig_split h
        sig_reduce [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs]
        sig_simp [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by sig_implies_sat [Proof.AesOcb.openWorkContract, Proof.AesOcb.openWorkSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, Proof.AesOcb.openX86_64, Proof.AesOcb.openLeak,
        Proof.AesOcb.openPreX, Proof.AesOcb.oneFacts, Proof.AesOcb.aCtx, Proof.AesOcb.aNonce, Proof.AesOcb.aAad,
        Proof.AesOcb.aData, Proof.AesOcb.aTag, Proof.AesOcb.aWork, Proof.AesOcb.onePub, Proof.AesOcb.openOut,
        X86_64.abi, Proof.AesOcb.arg, Proof.AesOcb.args, Proof.AesOcb.stk8, Proof.AesOcb.ret, Proof.AesOcb.rounds,
        X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
        X86_64.argRegs] [openSat, sealSat] using openSat }

end VG.Proof.AesOcb.X86_64

end

end


/-!
# AES-OCB on x86-64, with its working space on the stack

Every function runs its code, proved with the working space as its last
argument (`Verified.lean`), in a frame that allocates it. `init`'s working
space is in a register (`rcx`): its frame of 2568 bytes holds the 2560
bytes and 8 more to keep `rsp` aligned (`Verified.stackScratch`). The
working space of `seal` and `open` is passed on the stack after the six
argument registers and four other stack arguments (`data`, `len`, `tag` and
`tag_len`), so their frame of 3632 bytes holds the 3584 bytes of working
space, a copy of those four arguments, the word that stands for the return
address and the address of the working space (`Verified.stackArgScratch`).
The code's own calls use 8 bytes below the frame, the return address, as
`vg_aes_encrypt_blocks`, `vg_aes_decrypt_blocks` and `vg_aes_expand_key_scratch` use
no stack. `open`'s leak, whether it succeeds, reads only its buffers
(`openLeak_local`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.Impl.AesOcb.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)

variable (v : BlocksImpl)

theorem init_xdepth : (init (callees v)).x86_64Depth ≤ 8 := by
  simp only [init, callees, Code.x86_64Depth, v.encNoStack, v.expandNoStack]
  decide +kernel

theorem seal_xdepth : («seal» (callees v)).x86_64Depth ≤ 8 := by
  simp only [«seal», front, tagOut, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill,
    hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest, padCk, xorPad, tag, callBlocks, callees,
    Code.x86_64Depth, v.encNoStack, v.decNoStack, ↓reduceIte]
  decide +kernel

theorem open_xdepth : («open» (callees v)).x86_64Depth ≤ 8 := by
  simp only [«open», front, recv, nonce, nonceBlock, copyLoop, Impl.AesOcb.X86_64.hash, hashChunk, hashFill,
    hashSum, hashRest, padTo, body, whole, pass, nextOffset, rest, padCk, xorPad, tag, cmp, mask, callBlocks, callees,
    Code.x86_64Depth, v.encNoStack, v.decNoStack, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

/-- A state satisfying `vg_aes_ocb_init`'s precondition, without the working
space. -/
def initFrameSat : State := { initSat with wr := [⟨0x2000, 256⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Ocb.initContract X86_64.abi 2576).pre s := by
  implies_sat [Spec.Ocb.initContract, Spec.Ocb.initSig, Spec.Ocb.initPre, Spec.Ocb.initPost,
    X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

theorem init_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (init (callees v)))
      (Spec.Ocb.initContract X86_64.abi 2576) :=
  X86_64.Verified.stackScratchPre (hpostOut := Proof.AesOcb.initPostOut_local _) (sig := Spec.Ocb.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Ocb.initPre X86_64.abi.ptrBits) (post := Spec.Ocb.initPost X86_64.abi.ptrBits)
    (wa := true) (stack := 8) (bytes := 2568) (init_verified v) (by decide) (by decide)
    (by decide) (init_spSafe v) (init_xdepth v) initFrameSat_pre

theorem initFrameSatF_pre : ∃ s, (Spec.Ocb.initContract X86_64.abi 40).pre s := by
  implies_sat [Spec.Ocb.initContract, Spec.Ocb.initSig, Spec.Ocb.initPre, Spec.Ocb.initPost,
    X86_64.abi, X86_64.argRegs] [initFrameSat, initSat] using initFrameSat

/-- `init_framed`, over functions that need no working space: a frame of the
24 bytes `init` writes itself, after the 8 that stand for the return
address. -/
theorem initF_framed (f : Proof.Aes.X86_64.BlocksFree v.enc v.expand) :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch 32 .rcx (init (callees v)))
      (Spec.Ocb.initContract X86_64.abi 40) :=
  X86_64.Verified.stackScratchPre (hpostOut := Proof.AesOcb.initPostOut_local _) (sig := Spec.Ocb.initSig) (nm := "scratch") (e := .u64) (n := 3)
    (pre := Spec.Ocb.initPre X86_64.abi.ptrBits) (post := Spec.Ocb.initPost X86_64.abi.ptrBits)
    (wa := true) (stack := 8) (bytes := 32) (initF_verified v f) (by decide) (by decide)
    (by decide) (init_spSafe v) (init_xdepth v) initFrameSatF_pre

/-- A state satisfying `vg_aes_ocb_seal`'s precondition, without the working
space. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x2100, 0⟩, ⟨0x8008, 32⟩], wr := [⟨0, 0⟩, ⟨0x3000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesOcb.sealRoundsContract X86_64.abi 3640).pre s := by
  implies_sat [Proof.AesOcb.sealRoundsContract, Spec.Ocb.sealSig, Spec.Ocb.sealPre, Proof.AesOcb.sealRoundsPost,
    X86_64.abi, X86_64.argRegs] [sealFrameSat, sealSat] using sealFrameSat

theorem seal_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 3632 4 («seal» (callees v)))
      (Proof.AesOcb.sealRoundsContract X86_64.abi 3640) :=
  X86_64.Verified.stackArgScratchPre (hpostOut := sealPostOut_local _) (sig := Spec.Ocb.sealSig) (nm := "work") (e := .u64)
    (n := 448) (pre := Spec.Ocb.sealPre X86_64.abi.ptrBits)
    (post := Proof.AesOcb.sealRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 3632) (seal_verified v) (by decide) (by decide) (by decide)
    (seal_spSafe v) (seal_xdepth v) (sealPre_local _) (sealPost_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_ocb_open`'s precondition, without the working
space. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x2100, 0⟩, ⟨0x3000, 4⟩, ⟨0x8008, 32⟩], wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesOcb.openRoundsContract X86_64.abi 3640).pre s := by
  implies_sat [Proof.AesOcb.openRoundsContract, Spec.Ocb.openSig, Spec.Ocb.openPre, Proof.AesOcb.openRoundsPost,
    Spec.Ocb.openLeak, X86_64.abi, X86_64.argRegs] [openFrameSat, sealSat] using openFrameSat

theorem open_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 3632 4 («open» (callees v)))
      (Proof.AesOcb.openRoundsContract X86_64.abi 3640) :=
  X86_64.Verified.stackArgScratchPre (hpostOut := openPostOut_local _) (sig := Spec.Ocb.openSig) (nm := "work") (e := .u64)
    (n := 448) (pre := Spec.Ocb.openPre X86_64.abi.ptrBits)
    (post := Proof.AesOcb.openRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (leak := some (Spec.Ocb.openLeak X86_64.abi.ptrBits)) (bytes := 3632) (open_verified v)
    (by decide) (by decide) (by decide) (open_spSafe v) (open_xdepth v) (openPre_local _)
    (openPost_local _) openFrameSat_pre (hleak := openLeak_local _)

end VG.Proof.AesOcb.X86_64
