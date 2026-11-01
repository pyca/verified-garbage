module

import VerifiedGarbage.Proof.Rc2.Arm.KeyIO
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.Table
public import VerifiedGarbage.Proof.Rc2.Arm.PiScan
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc2.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rc2.Arm.KeyIO
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Rc2.Contract
meta import VerifiedGarbage.Proof.Rc2.Contract
meta import VerifiedGarbage.Proof.Rc2.Table
meta import VerifiedGarbage.Proof.Rc2.Arm.PiScan
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Syms
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Rc2.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Verified RC2 key expansion

Verified under `abi.withConsts piConsts`: the contract without the table
(`keyContract`) for the state without its region (`stripConsts`), and what
the calling convention says of the table (`ConstsOk`), from which the scans
read it (`PiAt`, `consts_pi`). Constant time by the taint analysis with the
table's address public (`taintSym`). -/

@[expose] public section

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Impl.Rc2.Arm
open VG.Impl.Rc2 (piSym piQuads piConsts)

def keyContract : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let out : Region := ⟨State.addr (s.gpr .r3), 128⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 512⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [key, args] ∧ s.wr = [out, scratch] ∧ key.Disjoint out ∧ key.Disjoint scratch ∧
      out.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 128 ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + 512 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32 ∧
      Spec.Rc2.validKey (s.gpr .r1).toNat (s.gpr .r2).toNat
  post s s' := Spec.Rc2.scheduleAt s'.mem (State.addr (s.gpr .r3)) =
    Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) (s.gpr .r2).toNat
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

theorem stackArg_stripConsts (K : List (String × List (BitVec 64))) (s : State) (i : Nat) :
    stackArg (stripConsts K s) i = stackArg s i := rfl

theorem stackArgAddr_stripConsts (K : List (String × List (BitVec 64))) (s : State) (i : Nat) :
    stackArgAddr (stripConsts K s) i = stackArgAddr s i := rfl

theorem piConsts_eq : piConsts = [(piSym, piQuads)] := rfl

/-- What the calling convention says of the table (`ConstsOk`), as the scans
need it: PITABLE at the table's address, apart from the writable regions, and
the table's region last among the readable ones. -/
theorem consts_pi {st : Nat} {s : State} (hc : ConstsOk piConsts st s) :
    PiAt (s.syms piSym) s ∧ (∀ r ∈ s.wr, (⟨State.addr (s.syms piSym), 256⟩ : Region).Disjoint r) ∧
      s.rd.drop (s.rd.length - 1) = [⟨State.addr (s.syms piSym), 256⟩] ∧
      PiHeld s.mem (State.addr (s.syms piSym)) ∧
      ∀ r ∈ abi.reserved st s, (⟨State.addr (s.syms piSym), 256⟩ : Region).Disjoint r := by
  obtain ⟨hd, hh, ht, -⟩ := hc
  have e : constRegs piConsts s = [⟨State.addr (s.syms piSym), 256⟩] := by
    rw [constRegs, piConsts_eq, Abi.constRegions_cons, Abi.constRegions_nil, piQuads_length]; rfl
  have hl : piConsts.length = 1 := rfl
  rw [e, hl] at hd
  rw [e] at ht
  obtain ⟨hfit, hwr, hres⟩ := List.forall_mem_singleton.mp ht
  have hfit' : (s.syms piSym).toNat + 256 ≤ 2 ^ 32 := by
    have : (State.addr (s.syms piSym)).toNat = (s.syms piSym).toNat := by
      simp only [State.addr, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega_arith)
    rw [this] at hfit; exact hfit
  have held : PiHeld s.mem (State.addr (s.syms piSym)) := fun i hi => hh _ List.mem_cons_self i hi
  refine ⟨⟨⟨hfit', ?_, fun i hi => held.byte hi⟩, rfl⟩, hwr, hd, held, hres⟩
  have hm : (⟨State.addr (s.syms piSym), 256⟩ : Region) ∈ s.rd.drop (s.rd.length - 1) := by
    rw [hd]; exact List.mem_singleton_self _
  exact List.mem_of_mem_drop hm

theorem key_body_correct (s : State) (hs : keyContract.pre (stripConsts piConsts s))
    (hc : ConstsOk piConsts 0 s) :
    WP isa expandKey s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ keyContract.post s s') := by
  obtain ⟨hrd', hwr, keyOut, keyScratch, outScratch, argsOut, argsScratch, keyFit, outFit, scratchFit, spFit, ht, ht', hb, hb'⟩ := hs
  obtain ⟨hT, twr, tdrop, -, -⟩ := consts_pi hc
  have hrd : s.rd = [⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, ⟨stackArgAddr s 0, 4⟩,
      ⟨State.addr (s.syms piSym), 256⟩] := by
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, tdrop]
    have h' : s.rd.take (s.rd.length - piConsts.length) = _ := hrd'
    exact congrArg (· ++ _) h'
  clear argsOut argsScratch spFit
  simp only [stripConsts_wr, stripConsts_gpr, stackArg_stripConsts]
    at hwr keyOut keyScratch outScratch keyFit outFit scratchFit ht ht' hb hb'
  have tOut : (⟨State.addr (s.syms piSym), 256⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 128⟩ :=
    twr _ (by rw [hwr]; exact List.mem_cons_self)
  have tScr : (⟨State.addr (s.syms piSym), 256⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 512⟩ :=
    twr _ (by rw [hwr]; simp)
  rw [expandKey]
  apply WP.seq
  obtain ⟨s₀, run₀, scratch₀, keep₀⟩ := loadScratch_ok s (by
    rw [hrd, hwr]
    exact ⟨⟨stackArgAddr s 0, 4⟩, by simp, Region.contains_self _ _⟩)
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  have gpr₀ (r : Reg) (hr : r ≠ .r12) : s₀.gpr r = s.gpr r := keep₀.reg r (by simpa using hr)
  apply WP.seq
  rw [WP.block_append_iff, keySave_eq]
  apply WP.mono_syms (Spill.save_block_ok keySlots_ok (by rw [scratch₀]; omega_arith) fun d _ hd => by
    rw [keep₀.wr, scratch₀, hwr]
    exact ⟨⟨State.addr (stackArg s 0), 512⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
  intro s₁ h₁ sy₁
  obtain ⟨s₂, run₂, r8₂, key₂, len₂, ptr₂, bits₂, zero₂, keep₂⟩ := pinKey_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [h₁.1, scratch₀] at r8₂
  rw [h₁.1, gpr₀ .r0 (by decide)] at key₂
  rw [h₁.1, gpr₀ .r1 (by decide)] at len₂
  rw [h₁.1, gpr₀ .r3 (by decide)] at ptr₂
  rw [h₁.1, gpr₀ .r2 (by decide)] at bits₂
  have scratchFrame : Frame [⟨State.addr (stackArg s 0), 512⟩] s.mem s₂.mem := by
    rw [keep₂.mem, h₁.2.2.2, keep₀.mem, scratch₀]
    exact Spill.saveMem_frame _ _ _ (by decide) _ (by decide)
  have rd₂ : s₂.rd = s.rd := keep₂.rd.trans (h₁.2.1.trans keep₀.rd)
  have wr₂ : s₂.wr = s.wr := keep₂.wr.trans (h₁.2.2.1.trans keep₀.wr)
  have source₂ : Spec.Rc2.bytesAt s₂.mem (State.addr (s₂.gpr .r4)) (s.gpr .r1).toNat =
      Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat := by
    rw [key₂]
    exact bytesAt_frame scratchFrame (by simpa using keyScratch) (by omega_arith)
  have read₂ : ∀ i < (s.gpr .r1).toNat,
      InRegions (s₂.rd ++ s₂.wr) (State.addr (s₂.gpr .r4) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [rd₂, wr₂, key₂, hrd, hwr]
    exact ⟨⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, by simp,
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have write₂ : ∀ i < 128, InRegions s₂.wr (State.addr (s₂.gpr .r6) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [wr₂, ptr₂, hwr]
    exact ⟨⟨State.addr (s.gpr .r3), 128⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have sy₂ : s₂.syms = s.syms := (runBlock_syms run₂).trans (sy₁.trans (runBlock_syms run₀))
  have hT₂ : PiAt (s.syms piSym) s₂ := by
    refine ⟨⟨hT.fit, by rw [rd₂]; exact hT.rd, fun i hi => ?_⟩, by rw [sy₂]⟩
    rw [scratchFrame.bytes (R := ⟨State.addr (s.syms piSym), 256⟩) (by simpa using tScr) (by simp) hi]
    exact hT.held i hi
  have tOut₂ : (⟨State.addr (s.syms piSym), 256⟩ : Region).Disjoint ⟨State.addr (s₂.gpr .r6), 128⟩ := by
    rw [ptr₂]; exact tOut
  apply WP.seq
  apply WP.mono (expandCopyFill_ok s₂ (s.gpr .r1).toNat ht ht' hT₂ tOut₂ (by rw [key₂]; exact keyFit) (by rw [ptr₂]; exact outFit)
    (by simpa using len₂) zero₂ read₂ write₂ (by rw [key₂, ptr₂]; exact keyOut))
  intro s₃ h₃
  apply WP.seq
  have write₃ : ∀ i < 128, InRegions s₃.wr (State.addr (s₃.gpr .r6) + BitVec.ofNat 64 i) 1 := by
    rw [h₃.1.wr, h₃.1.reg .r6 (by decide)]; exact write₂
  apply WP.mono (expandReduce_ok s₃ _ (s.gpr .r2).toNat hb hb' (hT₂.frame h₃.1 tOut₂)
    (by rw [h₃.1.reg .r6 (by decide)]; exact tOut₂) (by rw [h₃.1.reg .r6 (by decide), ptr₂]; exact outFit)
    (by simpa using (h₃.1.reg .r7 (by decide)).trans bits₂) write₃
    (by rw [h₃.1.reg .r6 (by decide)]; exact h₃.2))
  intro s₄ h₄
  have core := (CoreFrame.of_key h₃.1).trans h₄.1
  have outFrame : Frame [⟨State.addr (s.gpr .r3), 128⟩] s₂.mem s₄.mem := by
    have h := core.mem
    rw [ptr₂] at h; exact h
  have r8₄ : s₄.gpr .r8 = stackArg s 0 := (core.reg .r8 (by decide)).trans r8₂
  have rd₄ := core.rd.trans rd₂
  have wr₄ := core.wr.trans wr₂
  have expanded : BytesPrefix s₄.mem (State.addr (s.gpr .r3))
      (Spec.Rc2.expandBytes (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) (s.gpr .r2).toNat) 128 := by
    have h := h₄.2
    rw [h₃.1.reg .r6 (by decide), ptr₂, source₂] at h
    rw [expandBytes_eq]
    have length : (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat).length = (s.gpr .r1).toNat := by
      simp [Spec.Rc2.bytesAt]
    rw [length]; exact h
  rw [WP.block_append_iff]
  obtain ⟨s₅, run₅, base₅, keep₅⟩ := scratchBase_ok s₄
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  rw [r8₄] at base₅
  have rd₅ := keep₅.rd.trans rd₄
  have wr₅ := keep₅.wr.trans wr₄
  have stored : Spill.Saved s₅.mem (State.addr (s₅.gpr .r12)) s.gpr (slotsOf saved) := by
    intro p hp
    have bound := keySlots_ok.bound hp
    rw [keep₅.mem, base₅, outFrame.readW (r := ⟨State.addr (stackArg s 0), 512⟩)
      (Offset.contains_base _ (by omega_arith) (by omega_arith)) (by simpa using outScratch.symm) (by decide),
      keep₂.mem, h₁.2.2.2, scratch₀, Spill.saveMem_saved _ _ _ _ keySlots_ok p hp]
    have sep : ∀ p ∈ slotsOf saved, p.1 ≠ .r12 := by decide
    exact gpr₀ _ (sep p hp)
  rw [keyRestore_eq]
  apply WP.mono (Spill.restore_block_ok keySlots_ok (by decide) (by rw [base₅]; omega_arith)
    (fun d _ hd => by
      rw [rd₅, wr₅, base₅, hrd, hwr]
      exact ⟨⟨State.addr (stackArg s 0), 512⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩) stored)
  intro s₆ h₆
  constructor
  · exact Spill.restored_of h₆.1 (by decide)
  · change Spec.Rc2.scheduleAt s₆.mem (State.addr (s.gpr .r3)) = _
    rw [h₆.2.2.1, keep₅.mem]
    exact scheduleAt_expanded expanded

def keySatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 1 | .r2 => 8 | .r3 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x4001 then 0x30 else 0
  rd := [⟨0x1000, 1⟩, ⟨0x4000, 4⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 512⟩]

/-- Key expansion's contract with the table, as the proof states it. -/
def keyContractC : Contract isa where
  pre s := keyContract.pre (stripConsts piConsts s) ∧ ConstsOk piConsts 0 s
  post := keyContract.post
  pub s₁ s₂ := keyContract.pub s₁ s₂ ∧ s₁.syms piSym = s₂.syms piSym

theorem key_correct (s : State) (hs : keyContractC.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ keyContractC.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := key_body_correct s hs.1 hs.2
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

def keyTaint : VG.Arm.Taint.T := { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, argLen := 4 }

theorem keyTaint_wf {s : State} (h : keyContract.pre (stripConsts piConsts s)) : VG.Arm.Taint.Wf keyTaint s := by
  obtain ⟨_, wr, _, _, _, ao, asc, _, _, _, spfit, _⟩ := h
  simp only [stripConsts_wr, stripConsts_sp, stackArg_stripConsts, stackArgAddr_stripConsts] at wr ao asc spfit
  refine ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨spfit, ?_⟩, fun _ h => (List.not_mem_nil h).elim⟩
  have addr : State.addr s.sp = stackArgAddr s 0 := by simp [stackArgAddr]
  simp only [keyTaint, addr, wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact ao
  · exact asc

theorem keyTaint_agree {s₁ s₂ : State} (h₁ : keyContract.pre (stripConsts piConsts s₁))
    (h₂ : keyContract.pre (stripConsts piConsts s₂))
    (hp : keyContract.pub s₁ s₂) : VG.Arm.Taint.Agree keyTaint s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, a0⟩ := hp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h,
    keyTaint_wf h₁, keyTaint_wf h₂, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => psp, fun k hk => ?_⟩
  · simp only [keyTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact p0
    · exact p1
    · exact p2
    · exact p3
  · have argByte_eq (s : State) : Taint.argByte s k = stackArgAddr s 0 + BitVec.ofNat 64 k := by
      simp [Taint.argByte, stackArgAddr]
    simp only [keyTaint] at hk
    rw [argByte_eq, argByte_eq, Mem.readW_byte s₁.mem _ hk, Mem.readW_byte s₂.mem _ hk]
    exact congrArg _ a0

theorem expandKey_constantTime : ConstantTime isa keyContractC.pre keyContractC.pub expandKey :=
  VG.Taint.constantTime (A := taintSym [piSym]) keyTaint (fun _ _ h₁ h₂ hp => ⟨keyTaint_agree h₁.1 h₂.1 hp.1,
    fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hp.2⟩) (by taint_decide)

theorem key_implies : keyContract.Implies (Proof.Rc2.expandKeyContract abi) := by
  sig_implies [Proof.Rc2.expandKeyContract, Proof.Rc2.expandKeySig, abi, argRegs,
    Arm.reduceClassify, Arm.Loc.val, State.addr, keyContract, Spec.Rc2.validKey]
    [keySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using keySatState

/-- The memory of the witness with the table: the table at `0x100000`, zero
elsewhere (irreducible: unfolding it in a definitional check would evaluate
the table). -/
@[irreducible] def keySatMem : Mem := constMem 0x100000 piQuads

theorem keySatMem_held : ∀ i < piQuads.length,
    keySatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = piQuads.getD i 0 := by
  unfold keySatMem
  exact constMem_held _ _ (by rw [piQuads_length]; decide)

/-- The witness's memory below the table. -/
theorem keySatMem_readW (a : Addr) (ha : ∀ i < 4, ¬ (a + BitVec.ofNat 64 i - 0x100000).toNat < 256) :
    keySatMem.readW a 32 = 0 := by
  have e : keySatMem.readW a 32 = Mem.readW (fun _ => (0 : Byte)) a 32 := by
    apply Mem.readW_congr
    intro i hi
    unfold keySatMem constMem
    rw [piQuads_length, ite_eq_right (ha i hi)]
  rw [e, Mem.readW, Mem.read_eq_of_bytes (n := 32 / 8) (v := 0) (fun i _ => by simp)]
  decide

/-- A state satisfying the precondition with the table: the working space at 0. -/
def keySatC : State :=
  { keySatState with
    mem := keySatMem, rd := [⟨0x1000, 1⟩, ⟨0x4000, 4⟩, ⟨0x100000, 256⟩], wr := [⟨0x2000, 128⟩, ⟨0, 512⟩],
    syms := fun _ => 0x100000 }

theorem keySatC_arg : stackArg keySatC 0 = 0 :=
  keySatMem_readW _ (by decide)

theorem key_sat : (Proof.Rc2.expandKeyContract (abi.withConsts piConsts)).pre keySatC := by
  have hl : piQuads.length = 32 := piQuads_length
  have held := keySatMem_held
  have a0 := keySatC_arg
  rw [piConsts_eq]
  generalize piQuads = W at hl held ⊢
  generalize e : keySatC = s at a0
  sig_pre [Proof.Rc2.expandKeyContract, Proof.Rc2.expandKeySig, abi, argRegs,
    Arm.reduceClassify, Arm.Loc.val, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
    Spec.Rc2.validKey]
  subst e
  rw [a0, hl]
  refine ⟨by decide, by decide, fun i hi => held i (by rw [hl]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ ([⟨0x2000, 128⟩, ⟨0, 512⟩] : List Region) at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide)

theorem keyC_implies : keyContractC.Implies (Proof.Rc2.expandKeyContract (abi.withConsts piConsts)) where
  pre _ hs := ⟨key_implies.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
  post s s' hs hp := post_consts.mpr (key_implies.post (stripConsts piConsts s) s' (pre_consts.mp hs).1 hp)
  pub s₁ s₂ h₁ h₂ hp := ⟨key_implies.pub (stripConsts piConsts s₁) (stripConsts piConsts s₂)
      (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hp).1,
    symAddr_eq_iff.mp ((pub_consts.mp hp).2 _ List.mem_cons_self)⟩
  sat := ⟨keySatC, key_sat⟩

theorem key_verified : Verified target expandKey (Proof.Rc2.expandKeyContract (abi.withConsts piConsts)) :=
  Verified.of_correct key_correct expandKey_constantTime keyC_implies

end VG.Proof.Rc2.Arm
