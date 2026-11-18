module

public import VerifiedGarbage.Impl.Rc2.Arm.Stream
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Rc2.Stream
public import VerifiedGarbage.Proof.Rc2.Arm.Cbc.Verified
public import VerifiedGarbage.Proof.Framework.Arm.Frame
public import VerifiedGarbage.Proof.Rc2.Scratch
public import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Rc2.Arm.Lit
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Rc2.Arm.KeyIO
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.Contract
public import VerifiedGarbage.Proof.Rc2.Table
public import VerifiedGarbage.Proof.Rc2.Arm.KeyLoop
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Syms
meta import VerifiedGarbage.Proof.Rc2.Arm.KeyIO
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Rc2.Contract
meta import VerifiedGarbage.Proof.Rc2.Contract
meta import VerifiedGarbage.Proof.Rc2.Table
meta import VerifiedGarbage.Proof.Rc2.Arm.KeyLoop
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Syms
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Rc2.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Rc2.Arm.Key`, which only this module used -/

section

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
  obtain e : constRegs piConsts s = [⟨State.addr (s.syms piSym), 256⟩] := by
    rw [constRegs, piConsts_eq, Abi.constRegions_cons, Abi.constRegions_nil, piQuads_length]; rfl
  have hl : piConsts.length = 1 := rfl
  rw [e, hl] at hd
  rw [e] at ht
  obtain ⟨hfit, hwr, hres⟩ := List.forall_mem_singleton.mp ht
  obtain hfit' : (s.syms piSym).toNat + 256 ≤ 2 ^ 32 := by
    have : (State.addr (s.syms piSym)).toNat = (s.syms piSym).toNat := by
      simp only [State.addr, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega_arith)
    rw [this] at hfit; exact hfit
  obtain held : PiHeld s.mem (State.addr (s.syms piSym)) := fun i hi => hh _ List.mem_cons_self i hi
  refine ⟨⟨⟨hfit', ?_, fun i hi => held.byte hi⟩, rfl⟩, hwr, hd, held, hres⟩
  obtain hm : (⟨State.addr (s.syms piSym), 256⟩ : Region) ∈ s.rd.drop (s.rd.length - 1) := by
    rw [hd]; exact List.mem_singleton_self _
  exact List.mem_of_mem_drop hm

theorem key_body_correct (s : State) (hs : keyContract.pre (stripConsts piConsts s))
    (hc : ConstsOk piConsts 0 s) :
    WP isa expandKey s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ keyContract.post s s') := by
  obtain ⟨hrd', hwr, keyOut, keyScratch, outScratch, argsOut, argsScratch, keyFit, outFit, scratchFit, spFit, ht, ht', hb, hb'⟩ := hs
  obtain ⟨hT, twr, tdrop, -, -⟩ := consts_pi hc
  obtain hrd : s.rd = [⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, ⟨stackArgAddr s 0, 4⟩,
      ⟨State.addr (s.syms piSym), 256⟩] := by
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, tdrop]
    have h' : s.rd.take (s.rd.length - piConsts.length) = _ := hrd'
    exact congrArg (· ++ _) h'
  clear argsOut argsScratch spFit
  simp only [stripConsts_wr, stripConsts_gpr, stackArg_stripConsts]
    at hwr keyOut keyScratch outScratch keyFit outFit scratchFit ht ht' hb hb'
  obtain tOut : (⟨State.addr (s.syms piSym), 256⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 128⟩ :=
    twr _ (by rw [hwr]; exact List.mem_cons_self)
  obtain tScr : (⟨State.addr (s.syms piSym), 256⟩ : Region).Disjoint ⟨State.addr (stackArg s 0), 512⟩ :=
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
  obtain scratchFrame : Frame [⟨State.addr (stackArg s 0), 512⟩] s.mem s₂.mem := by
    rw [keep₂.mem, h₁.2.2.2, keep₀.mem, scratch₀]
    exact Spill.saveMem_frame _ _ _ (by decide) _ (by decide)
  obtain rd₂ : s₂.rd = s.rd := keep₂.rd.trans (h₁.2.1.trans keep₀.rd)
  obtain wr₂ : s₂.wr = s.wr := keep₂.wr.trans (h₁.2.2.1.trans keep₀.wr)
  obtain source₂ : Spec.Rc2.bytesAt s₂.mem (State.addr (s₂.gpr .r4)) (s.gpr .r1).toNat =
      Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat := by
    rw [key₂]
    exact bytesAt_frame scratchFrame (by simpa using keyScratch) (by omega_arith)
  obtain read₂ : ∀ i < (s.gpr .r1).toNat,
      InRegions (s₂.rd ++ s₂.wr) (State.addr (s₂.gpr .r4) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [rd₂, wr₂, key₂, hrd, hwr]
    exact ⟨⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, by simp,
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain write₂ : ∀ i < 128, InRegions s₂.wr (State.addr (s₂.gpr .r6) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [wr₂, ptr₂, hwr]
    exact ⟨⟨State.addr (s.gpr .r3), 128⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain sy₂ : s₂.syms = s.syms := (runBlock_syms run₂).trans (sy₁.trans (runBlock_syms run₀))
  obtain hT₂ : PiAt (s.syms piSym) s₂ := by
    refine ⟨⟨hT.fit, by rw [rd₂]; exact hT.rd, fun i hi => ?_⟩, by rw [sy₂]⟩
    rw [scratchFrame.bytes (R := ⟨State.addr (s.syms piSym), 256⟩) (by simpa using tScr) (by simp) hi]
    exact hT.held i hi
  obtain tOut₂ : (⟨State.addr (s.syms piSym), 256⟩ : Region).Disjoint ⟨State.addr (s₂.gpr .r6), 128⟩ := by
    rw [ptr₂]; exact tOut
  apply WP.seq
  apply WP.mono (expandCopyFill_ok s₂ (s.gpr .r1).toNat ht ht' hT₂ tOut₂ (by rw [key₂]; exact keyFit) (by rw [ptr₂]; exact outFit)
    (by simpa using len₂) zero₂ read₂ write₂ (by rw [key₂, ptr₂]; exact keyOut))
  intro s₃ h₃
  apply WP.seq
  obtain write₃ : ∀ i < 128, InRegions s₃.wr (State.addr (s₃.gpr .r6) + BitVec.ofNat 64 i) 1 := by
    rw [h₃.1.wr, h₃.1.reg .r6 (by decide)]; exact write₂
  apply WP.mono (expandReduce_ok s₃ _ (s.gpr .r2).toNat hb hb' (hT₂.frame h₃.1 tOut₂)
    (by rw [h₃.1.reg .r6 (by decide)]; exact tOut₂) (by rw [h₃.1.reg .r6 (by decide), ptr₂]; exact outFit)
    (by simpa using (h₃.1.reg .r7 (by decide)).trans bits₂) write₃
    (by rw [h₃.1.reg .r6 (by decide)]; exact h₃.2))
  intro s₄ h₄
  obtain core := (CoreFrame.of_key h₃.1).trans h₄.1
  obtain outFrame : Frame [⟨State.addr (s.gpr .r3), 128⟩] s₂.mem s₄.mem := by
    have h := core.mem
    rw [ptr₂] at h; exact h
  obtain r8₄ : s₄.gpr .r8 = stackArg s 0 := (core.reg .r8 (by decide)).trans r8₂
  obtain rd₄ := core.rd.trans rd₂
  obtain wr₄ := core.wr.trans wr₂
  obtain expanded : BytesPrefix s₄.mem (State.addr (s.gpr .r3))
      (Spec.Rc2.expandBytes (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) (s.gpr .r2).toNat) 128 := by
    have h := h₄.2
    rw [h₃.1.reg .r6 (by decide), ptr₂, source₂] at h
    rw [expandBytes_eq]
    obtain length : (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat).length = (s.gpr .r1).toNat := by
      simp [Spec.Rc2.bytesAt]
    rw [length]; exact h
  rw [WP.block_append_iff]
  obtain ⟨s₅, run₅, base₅, keep₅⟩ := scratchBase_ok s₄
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  rw [r8₄] at base₅
  obtain rd₅ := keep₅.rd.trans rd₄
  obtain wr₅ := keep₅.wr.trans wr₄
  obtain stored : Spill.Saved s₅.mem (State.addr (s₅.gpr .r12)) s.gpr (slotsOf saved) := by
    intro p hp
    obtain bound := keySlots_ok.bound hp
    rw [keep₅.mem, base₅, outFrame.readW (r := ⟨State.addr (stackArg s 0), 512⟩)
      (Offset.contains_base _ (by omega_arith) (by omega_arith)) (by simpa using outScratch.symm) (by decide),
      keep₂.mem, h₁.2.2.2, scratch₀, Spill.saveMem_saved _ _ _ _ keySlots_ok p hp]
    obtain sep : ∀ p ∈ slotsOf saved, p.1 ≠ .r12 := by decide
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
  obtain addr : State.addr s.sp = stackArgAddr s 0 := by simp [stackArgAddr]
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

end VG.Proof.Rc2.Arm

end

end

@[expose] public section

section

/-!
# Streaming RC2-CBC on ARMv7: the calls

The callees take their scratch buffer `S` on the stack: a frame pushes it
(`push {r12, lr}`, with `S` in `r12` at `[sp]`) around the call. `key_call`
and `cbc_call` run the frame around the call of `vg_rc2_expand_key` and of
the CBC function: memory changes only in the callee's writable buffers and
the 8 bytes below the stack pointer. `key_rel` and `cbc_rel`: the frames, with
the same arguments and stack pointer in two runs, are constant time.
-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Impl.Rc2.Arm
open VG.Impl.Rc2 (piSym piQuads piConsts)

/-- Addresses below a pointer do not wrap. -/
theorem addr_sub {a : BitVec 32} {k : Nat} (h : k ≤ a.toNat) :
    State.addr (a - BitVec.ofNat 32 k) = State.addr a - BitVec.ofNat 64 k := by
  simp only [State.addr]
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := k) (by omega_arith), Nat.mod_eq_of_lt (a := k) (by omega_arith),
    Nat.mod_eq_of_lt (a := a.toNat) (by omega_arith)]
  omega_arith

theorem storeWords_two (m : Mem) (a : BitVec 32) (x y : BitVec 32) :
    storeWords m a [x, y] = (m.writeW (State.addr a) x).writeW (State.addr (a + 4)) y := rfl

/-- The 8 bytes below the stack pointer, where the frame pushes `S` and `lr`. -/
abbrev below (s : State) : Region := ⟨State.addr s.sp - 8, 8⟩

/-- The callee's stack argument. -/
abbrev argR (s : State) : Region := ⟨State.addr s.sp - 8, 4⟩

/-- The state the callee runs from, with the permissions it is given. -/
abbrev view (s : State) (rd wr : List Region) : State :=
  (pushed [.r12, .lr] s).callEntry.withRegions rd wr

theorem e8 : BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length) = 8 := rfl

section
variable {s : State} (hsp : 8 ≤ s.sp.toNat)
include hsp

theorem hA : State.addr (s.sp - 8) = State.addr s.sp - 8 := addr_sub hsp

theorem hA4 : State.addr (s.sp - 8 + BitVec.ofNat 32 4) = State.addr s.sp - 8 + 4 := by
  have := s.sp.isLt
  have e : (s.sp - 8).toNat = s.sp.toNat - 8 := BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hsp)
  rw [addr_add (by rw [e]; omega_arith), hA hsp]; rfl

theorem amem : (pushed [.r12, .lr] s).mem =
    (s.mem.writeW (State.addr s.sp - 8) (s.gpr .r12)).writeW (State.addr s.sp - 8 + 4) (s.gpr .lr) := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)) [s.gpr .r12, s.gpr .lr] = _
  rw [e8, storeWords_two, hA hsp, show (s.sp - 8 + 4 : BitVec 32) = s.sp - 8 + BitVec.ofNat 32 4 from rfl,
    hA4 hsp]

theorem fA : Frame [below s] s.mem (pushed [.r12, .lr] s).mem := by
  rw [amem hsp]
  refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith
  · simp only [Region.Contains]
    rw [Offset.add_sub_cancel_left]; decide

theorem sa0 (rd wr : List Region) : stackArgAddr (view s rd wr) 0 = State.addr s.sp - 8 := by
  unfold stackArgAddr
  simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, e8]
  rw [show s.sp - 8 + BitVec.ofNat 32 (4 * 0) = s.sp - 8 from BitVec.add_zero _, hA hsp]

theorem arg0 (rd wr : List Region) : stackArg (view s rd wr) 0 = s.gpr .r12 := by
  rw [stackArg, sa0 hsp, State.withRegions_mem, State.callEntry_mem, amem hsp, Mem.readW_writeW_sep
    (Offset.sep_base (State.addr s.sp - 8) (n := 4) (e := 4) (k := 4) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32]

theorem view_sp (rd wr : List Region) : (view s rd wr).sp.toNat = s.sp.toNat - 8 := by
  simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, e8]
  exact BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hsp)

/-- The callee's regions, which the frame covers with `s`'s. -/
theorem cov {rd wr : List Region} (hr : Covers rd (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    Covers (rd ++ argR s :: wr) ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) := by
  intro x n' ⟨r, hr', hc⟩
  rcases List.mem_append.mp hr' with h' | h'
  · obtain ⟨r', hr'', hc'⟩ := hr x n' ⟨r, h', hc⟩
    refine ⟨r', ?_, hc'⟩
    rcases List.mem_append.mp hr'' with h'' | h''
    · exact List.mem_append_left _ h''
    · exact List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ h'')
  · rcases List.mem_cons.mp h' with rfl | h'
    · have eb : (⟨State.addr (s.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)),
          4 * [Reg.r12, Reg.lr].length⟩ : Region) = below s := by rw [e8, hA hsp]; rfl
      refine ⟨below s, List.mem_append_right _ (by rw [pushed_wr, eb]; exact List.mem_cons_self ..), ?_⟩
      simp only [Region.Contains] at hc ⊢; omega_arith
    · obtain ⟨r', hr'', hc'⟩ := hw x n' ⟨r, h', hc⟩
      exact ⟨r', List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr''), hc'⟩

end

theorem covW {s : State} {wr : List Region} (hw : Covers wr s.wr) : Covers wr (pushed [.r12, .lr] s).wr := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := hw x n' hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

theorem view_gpr (s : State) (rd wr : List Region) (r : Reg) (hr : r ∉ linkRegs) :
    (view s rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr]

/-! ## `vg_rc2_expand_key` -/

/-- The region of PITABLE's table, at the address of `VG_RC2_PITABLE`. -/
abbrev tbl (s : State) : Region := ⟨State.addr (s.syms piSym), 256⟩

/-- What the call of `vg_rc2_expand_key` needs: its arguments and regions,
and the table, readable, held, and apart from what the call writes. -/
structure KeyPre (s : State) (K KL E O S : BitVec 32) : Prop where
  r0 : s.gpr .r0 = K
  r1 : s.gpr .r1 = KL
  r2 : s.gpr .r2 = E
  r3 : s.gpr .r3 = O
  r12 : s.gpr .r12 = S
  hsp : 8 ≤ s.sp.toNat
  valid : Spec.Rc2.validKey KL.toNat E.toNat
  ko : (⟨State.addr K, KL.toNat⟩ : Region).Disjoint ⟨State.addr O, 128⟩
  ks : (⟨State.addr K, KL.toNat⟩ : Region).Disjoint ⟨State.addr S, 512⟩
  os : (⟨State.addr O, 128⟩ : Region).Disjoint ⟨State.addr S, 512⟩
  bk : (below s).Disjoint ⟨State.addr K, KL.toNat⟩
  bo : (below s).Disjoint ⟨State.addr O, 128⟩
  bs : (below s).Disjoint ⟨State.addr S, 512⟩
  hK : K.toNat + KL.toNat ≤ 2 ^ 32
  hO : O.toNat + 128 ≤ 2 ^ 32
  hS : S.toNat + 512 ≤ 2 ^ 32
  reads : Covers [⟨State.addr K, KL.toNat⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr O, 128⟩, ⟨State.addr S, 512⟩] s.wr
  tfit : (s.syms piSym).toNat + 256 ≤ 2 ^ 32
  tHeld : Proof.Rc2.PiHeld s.mem (State.addr (s.syms piSym))
  tO : (tbl s).Disjoint ⟨State.addr O, 128⟩
  tS : (tbl s).Disjoint ⟨State.addr S, 512⟩
  tb : (below s).Disjoint (tbl s)
  trd : tbl s ∈ s.rd
  tal : (State.addr (s.syms piSym)).toNat % 64 = 0

/-- What the call of `vg_rc2_expand_key` leaves. -/
structure KeyPost (s : State) (K KL E O S : BitVec 32) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr O, 128⟩, ⟨State.addr S, 512⟩, below s] s.mem s'.mem
  sched : Spec.Rc2.scheduleAt s'.mem (State.addr O) =
    Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (State.addr K) KL.toNat) E.toNat

abbrev keyRd (s : State) (K KL : BitVec 32) : List Region := [⟨State.addr K, KL.toNat⟩, argR s]
abbrev keyWr (O S : BitVec 32) : List Region := [⟨State.addr O, 128⟩, ⟨State.addr S, 512⟩]

/-- The callee's readable regions: the key, its stack argument and the table. -/
abbrev keyRdC (s : State) (K KL : BitVec 32) : List Region := keyRd s K KL ++ [tbl s]

theorem KeyPre.pre0 {s : State} {K KL E O S : BitVec 32} (h : KeyPre s K KL E O S) :
    keyContract.pre (view s (keyRd s K KL) (keyWr O S)) := by
  have hv := view_sp h.hsp (keyRd s K KL) (keyWr O S)
  simp only [keyContract, arg0 h.hsp, sa0 h.hsp, view_gpr _ _ _ .r0 (by decide), view_gpr _ _ _ .r1 (by decide),
    view_gpr _ _ _ .r2 (by decide), view_gpr _ _ _ .r3 (by decide), h.r0, h.r1, h.r2, h.r3, h.r12,
    State.withRegions_rd, State.withRegions_wr, hv]
  refine ⟨trivial, trivial, h.ko, h.ks, h.os, ?_, ?_, h.hK, h.hO, h.hS, by have := s.sp.isLt; omega_arith, h.valid⟩
  · exact (h.bo.sub_left (Region.sub_prefix (by decide)))
  · exact (h.bs.sub_left (Region.sub_prefix (by decide)))

/-- The table, as the callee's calling convention states it. -/
theorem KeyPre.consts {s : State} {K KL E O S : BitVec 32} (h : KeyPre s K KL E O S) :
    ConstsOk piConsts 0 (view s (keyRdC s K KL) (keyWr O S)) := by
  have e : constRegs piConsts (view s (keyRdC s K KL) (keyWr O S)) = [tbl s] := by
    rw [constRegs, piConsts_eq, Abi.constRegions_cons, Abi.constRegions_nil, piQuads_length]; rfl
  refine ⟨by rw [e]; rfl, ?_, ?_, ?_⟩
  · rw [piConsts_eq]
    intro c hc i hi
    simp only [List.mem_singleton] at hc
    subst hc
    rw [piQuads_length] at hi
    show (pushed [.r12, .lr] s).mem.readW (State.addr (s.syms piSym) + BitVec.ofNat 64 (8 * i)) 64 = _
    rw [(fA h.hsp).readW (r := tbl s) (Offset.contains_base _ (by omega_arith) (by omega_arith)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.tb.symm) (by decide)]
    exact h.tHeld i (by rw [piQuads_length]; exact hi)
  · rw [e]
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    refine ⟨?_, fun r hr => ?_, fun r hr => nomatch hr⟩
    · rw [abi_ptrBits]
      show (State.addr (s.syms piSym)).toNat + 256 ≤ 2 ^ 32
      have := h.tfit
      simp only [State.addr, BitVec.toNat_setWidth]
      rw [Nat.mod_eq_of_lt (by omega_arith)]
      exact this
    · change r ∈ keyWr O S at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.tO
      · exact h.tS
  · rw [e]
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact h.tal

theorem KeyPre.pre {s : State} {K KL E O S : BitVec 32} (h : KeyPre s K KL E O S) :
    keyContractC.pre (view s (keyRdC s K KL) (keyWr O S)) :=
  ⟨h.pre0, h.consts⟩

/-- The callee's regions, which the frame covers with `s`'s. -/
theorem covC {s : State} {K KL E O S : BitVec 32} (h : KeyPre s K KL E O S) :
    Covers (keyRdC s K KL ++ keyWr O S) ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) := by
  have c := cov h.hsp h.reads h.writes
  have ct : Covers [tbl s] ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) :=
    Covers.left (Covers.of_mem fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [pushed_rd]; exact h.trd)
  refine Covers.of_forall fun r hr => ?_
  simp only [keyRdC, keyRd, keyWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (Covers.of_mem fun x hx => by simp only [List.mem_singleton] at hx; subst hx; simp).trans c
  · exact (Covers.of_mem fun x hx => by simp only [List.mem_singleton] at hx; subst hx; simp).trans c
  · exact ct
  · exact (Covers.of_mem fun x hx => by simp only [List.mem_singleton] at hx; subst hx; simp).trans c
  · exact (Covers.of_mem fun x hx => by simp only [List.mem_singleton] at hx; subst hx; simp).trans c

theorem key_noCalls : expandKey.noCalls = true := by decide +kernel

theorem key_call {s : State} {K KL E O S : BitVec 32} (h : KeyPre s K KL E O S) :
    WP isa Stream.keyCall s (KeyPost s K KL E O S) := by
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using h.hsp) (by simp) ?_
  refine WP.call (k := keyContractC) key_correct (rd := keyRdC s K KL) (wr := keyWr O S) h.pre
    (covC h) (covW h.writes) ?_ key_noCalls
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs _ hpost ml ul hfl
  have hfl' : Frame [below s] s₂.mem ml := by rw [e8, hA h.hsp] at hfl; exact hfl
  have bytesK : Spec.Rc2.bytesAt (pushed [.r12, .lr] s).mem (State.addr K) KL.toNat =
      Spec.Rc2.bytesAt s.mem (State.addr K) KL.toNat :=
    VG.Proof.Rc2.bytesAt_frame (fA h.hsp) _ _ (by omega_arith) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bk.symm)
  change Spec.Rc2.scheduleAt s₂.mem _ = _ at hpost
  simp only [State.withRegions_mem, State.callEntry_mem, view_gpr _ _ _ .r0 (by decide),
    view_gpr _ _ _ .r1 (by decide), view_gpr _ _ _ .r2 (by decide), view_gpr _ _ _ .r3 (by decide),
    h.r0, h.r1, h.r2, h.r3, bytesK] at hpost
  refine ⟨?_, ?_, ?_, fun r hr hlr => ?_, ?_, ?_⟩ <;> dsimp only
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_sp, hsp₂, pushed_sp, e8]; exact BitVec.sub_add_cancel _ _
  · have : r ≠ .r12 := by intro e; subst e; simp [preserved] at hr
    rw [popped_gpr this, hcs r hr hlr, pushed_gpr]
  · refine (((fA h.hsp).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (hf.sub fun r hr => ⟨r, by simp at hr; rcases hr with rfl | rfl <;> simp, fun _ h => h⟩)).trans
      (hfl'.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)
  · rw [Proof.Rc2.scheduleAt_frame hfl' _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.bo.symm]
    exact hpost

theorem key_rel {K KL E O S sp₀ T₀ : BitVec 32} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → KeyPre s₁ K KL E O S ∧ KeyPre s₂ K KL E O S ∧ s₁.sp = sp₀ ∧ s₂.sp = sp₀ ∧
      s₁.syms piSym = T₀ ∧ s₂.syms piSym = T₀) :
    RelCT isa P Stream.keyCall fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ hp => by obtain ⟨_, _, h₁, h₂, _⟩ := h _ _ hp; rw [h₁, h₂]) ?_
  refine RelCT.call key_correct expandKey_constantTime
    [⟨State.addr K, KL.toNat⟩, ⟨State.addr sp₀ - 8, 4⟩, ⟨State.addr T₀, 256⟩] (keyWr O S)
    fun a b ⟨s₁, s₂, hp, pa, pb⟩ => ?_
  obtain ⟨h₁, h₂, sp₁, sp₂, t₁, t₂⟩ := h _ _ hp
  rw [push_pushed rfl (by simpa using h₁.hsp), Option.some.injEq] at pa
  rw [push_pushed rfl (by simpa using h₂.hsp), Option.some.injEq] at pb
  subst pa pb
  have e₁ : keyRdC s₁ K KL = [⟨State.addr K, KL.toNat⟩, ⟨State.addr sp₀ - 8, 4⟩, ⟨State.addr T₀, 256⟩] := by
    rw [← sp₁, ← t₁]; rfl
  have e₂ : keyRdC s₂ K KL = [⟨State.addr K, KL.toNat⟩, ⟨State.addr sp₀ - 8, 4⟩, ⟨State.addr T₀, 256⟩] := by
    rw [← sp₂, ← t₂]; rfl
  have p₁ := h₁.pre
  have p₂ := h₂.pre
  have c₁ := covC h₁
  have c₂ := covC h₂
  rw [e₁] at c₁
  rw [e₂] at c₂
  have a₁ := arg0 h₁.hsp (keyRdC s₁ K KL) (keyWr O S)
  have a₂ := arg0 h₂.hsp (keyRdC s₂ K KL) (keyWr O S)
  rw [view, e₁] at p₁ a₁
  rw [view, e₂] at p₂ a₂
  refine ⟨p₁, p₂, ⟨?_, ?_⟩, c₁, covW h₁.writes, c₂, covW h₂.writes⟩
  · simp only [keyContract, a₁, a₂, State.withRegions_gpr, State.withRegions_sp,
      State.callEntry_sp, pushed_sp, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), pushed_gpr, h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₂.r0, h₂.r1,
      h₂.r2, h₂.r3, h₁.r12, h₂.r12, sp₁, sp₂]
    exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  · show s₁.syms piSym = s₂.syms piSym
    rw [t₁, t₂]

/-! ## The CBC functions -/

end VG.Proof.Rc2.Arm.Stream

end

section

/-!
# Streaming RC2-CBC on ARMv7: the byte copy

`copy_wp`: the copy of `L` bytes from `src + so` to `dst + dd`
(`Impl.Rc2.Arm.Stream.copy`), for any registers, offsets and count, writes the
source bytes at the destination (`writeBytes`), advances both pointers by `L`,
and changes no other register but `r12` and the count.
-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_sub wp_subs wp_cmp wp_ldr
  wp_str wp_ldrb wp_strb wp_ldrSp eval_eq eval_ne ofNat_beq_zero sub_ofNat cmp0)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame)

end VG.Proof.Rc2.Arm.Stream

end

section

/-!
# Streaming RC2-CBC on ARMv7: the contracts, spelled out

The contract of `vg_rc2_cbc_init` with its facts written out for ARMv7 and a
stack of 8 bytes (`initContract`), which implies the shared one
(`init_implies`).
-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm
open VG.Impl.Rc2 (piSym piQuads piConsts)

/-- `vg_rc2_cbc_init`'s contract under `abi`, spelled out. -/
def initContract0 : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let iv : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let args : Region := ⟨stackArgAddr s 0, 12⟩
    let ctx : Region := ⟨State.addr (stackArg s 1), 144⟩
    let scr : Region := ⟨State.addr (stackArg s 2), 576⟩
    let below : Region := ⟨State.addr s.sp - 8, 8⟩
    8 ≤ s.sp.toNat ∧ s.sp.toNat + 12 ≤ 2 ^ 32 ∧ s.rd = [key, iv, args] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ iv.Disjoint ctx ∧ iv.Disjoint scr ∧ ctx.Disjoint scr ∧
      ctx.Disjoint args ∧ scr.Disjoint args ∧ below.Disjoint key ∧ below.Disjoint iv ∧
      below.Disjoint ctx ∧ below.Disjoint scr ∧ below.Disjoint args ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧
      (stackArg s 1).toNat + 144 ≤ 2 ^ 32 ∧ (stackArg s 2).toNat + 576 ≤ 2 ^ 32
  post s s' :=
    ∀ direction, match Spec.Rc2.initWithEffectiveBits
        (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
        (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat) direction
        (s.gpr .r2).toNat with
      | .ok c => BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) = 0 ∧
        Spec.Rc2.contextAt s'.mem (State.addr (stackArg s 1)) direction 0 = c
      | .error e => (BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0)).toNat = e.code
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
    stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2

def initSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r3 => 0x2000 | _ => 0
  sp := 0x6000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x6005 then 0x30 else if a = 0x6009 then 0x40 else 0
  rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩, ⟨0x6000, 12⟩]
  wr := [⟨0x3000, 144⟩, ⟨0x4000, 576⟩]

theorem init_implies0 : initContract0.Implies (Proof.Rc2.cbcInitScratchContract abi 8) := by
  sig_implies [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argRegs,
    Arm.reduceClassify, Arm.Loc.val, State.addr, initContract0]
    [initSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using initSatState

/-- `initContract0` with the table's region last among the readable ones, as
the proofs state it. -/
def initContract : Contract isa :=
  { initContract0 with
    pre s :=
      let key : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
      let iv : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
      let args : Region := ⟨stackArgAddr s 0, 12⟩
      let ctx : Region := ⟨State.addr (stackArg s 1), 144⟩
      let scr : Region := ⟨State.addr (stackArg s 2), 576⟩
      let below : Region := ⟨State.addr s.sp - 8, 8⟩
      8 ≤ s.sp.toNat ∧ s.sp.toNat + 12 ≤ 2 ^ 32 ∧ s.rd = [key, iv, args, tbl s] ∧ s.wr = [ctx, scr] ∧
        key.Disjoint ctx ∧ key.Disjoint scr ∧ iv.Disjoint ctx ∧ iv.Disjoint scr ∧ ctx.Disjoint scr ∧
        ctx.Disjoint args ∧ scr.Disjoint args ∧ below.Disjoint key ∧ below.Disjoint iv ∧
        below.Disjoint ctx ∧ below.Disjoint scr ∧ below.Disjoint args ∧
        (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧
        (stackArg s 1).toNat + 144 ≤ 2 ^ 32 ∧ (stackArg s 2).toNat + 576 ≤ 2 ^ 32 }

/-- What the calling convention says of the table, as `init` needs it. -/
structure InitTab (s : State) : Prop where
  fit : (s.syms piSym).toNat + 256 ≤ 2 ^ 32
  held : Proof.Rc2.PiHeld s.mem (State.addr (s.syms piSym))
  wr : ∀ r ∈ s.wr, (tbl s).Disjoint r
  below : (tbl s).Disjoint ⟨State.addr s.sp - 8, 8⟩
  al : (State.addr (s.syms piSym)).toNat % 64 = 0

/-- `vg_rc2_cbc_init`'s contract under `abi.withConsts piConsts`, as the
proofs state it. -/
def initContractC : Contract isa where
  pre s := initContract.pre s ∧ InitTab s
  post := initContract.post
  pub s₁ s₂ := initContract.pub s₁ s₂ ∧ s₁.syms piSym = s₂.syms piSym

/-- The precondition with the table, from the one without it (`stripConsts`)
and what the calling convention says of the table. -/
theorem initC_pre {s : State} (h : initContract0.pre (stripConsts piConsts s)) (hc : ConstsOk piConsts 8 s) :
    initContractC.pre s := by
  obtain ⟨hT, twr, tdrop, held, tres⟩ := consts_pi hc
  obtain ⟨a1, a2, hrd, rest⟩ := h
  refine ⟨⟨a1, a2, ?_, rest⟩, ⟨hT.fit, held, twr, tres _ List.mem_cons_self,
    hc.aligned (by rw [piConsts_eq]; exact List.mem_cons_self)⟩⟩
  rw [← List.take_append_drop (s.rd.length - 1) s.rd, tdrop]
  have h' : s.rd.take (s.rd.length - piConsts.length) = _ := hrd
  exact congrArg (· ++ _) h'

/-- The memory of the witness with the table: the table at `0x100000`, and
`initSatState`'s elsewhere (irreducible: unfolding it in a definitional check
would evaluate the table). -/
@[irreducible] def initSatMem : Mem := fun a =>
  if (a - 0x100000).toNat < 256 then constMem 0x100000 piQuads a else initSatState.mem a

theorem initSatMem_held : ∀ i < piQuads.length,
    initSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = piQuads.getD i 0 := by
  intro i hi
  rw [piQuads_length] at hi
  rw [← constMem_held 0x100000 piQuads (by rw [piQuads_length]; decide) i (by rw [piQuads_length]; exact hi)]
  apply Mem.readW_congr
  intro j hj
  unfold initSatMem
  refine ite_eq_left ?_
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  omega_arith

/-- The witness's memory outside the table. -/
theorem initSatMem_eq (a : Addr) (ha : ¬ (a - 0x100000).toNat < 256) : initSatMem a = initSatState.mem a := by
  unfold initSatMem
  exact ite_eq_right ha

/-- `initSatState` with the table. -/
def initSatC : State :=
  { initSatState with
    mem := initSatMem, rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩, ⟨0x6000, 12⟩, ⟨0x100000, 256⟩], syms := fun _ => 0x100000 }

theorem initSatC_arg {i : Nat} (hi : i < 3) : stackArg initSatC i = stackArg initSatState i := by
  apply Mem.readW_congr
  intro j hj
  apply initSatMem_eq
  have h : ∀ i < 3, ∀ j < 4, ¬ (stackArgAddr initSatState i + BitVec.ofNat 64 j - 0x100000).toNat < 256 := by
    decide
  exact h i hi j hj

theorem initSat_pre : (Proof.Rc2.cbcInitScratchContract (abi.withConsts piConsts) 8).pre initSatC := by
  have hl : piQuads.length = 32 := piQuads_length
  have held := initSatMem_held
  have a0 := initSatC_arg (i := 0) (by decide)
  have a1 := initSatC_arg (i := 1) (by decide)
  have a2 := initSatC_arg (i := 2) (by decide)
  rw [piConsts_eq]
  generalize piQuads = W at hl held ⊢
  generalize e : initSatC = s at a0 a1 a2
  sig_pre [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argRegs,
    Arm.reduceClassify, Arm.Loc.val, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  have v0 : stackArg initSatState 0 = 0 := by decide
  have v1 : stackArg initSatState 1 = 0x3000 := by decide
  have v2 : stackArg initSatState 2 = 0x4000 := by decide
  rw [a0, a1, a2, v0, v1, v2, hl]
  refine ⟨by decide, by decide, by decide, fun i hi => held i (by rw [hl]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ ([⟨0x3000, 144⟩, ⟨0x4000, 576⟩] : List Region) at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | rfl | decide | exact Region.disjoint_of_sep (by decide)

theorem init_implies : initContractC.Implies (Proof.Rc2.cbcInitScratchContract (abi.withConsts piConsts) 8) where
  pre _ hs := initC_pre (init_implies0.pre _ (pre_consts.mp hs).1) (pre_consts.mp hs).2
  post s s' hs hp := post_consts.mpr (init_implies0.post (stripConsts piConsts s) s' (pre_consts.mp hs).1 hp)
  pub s₁ s₂ h₁ h₂ hp := ⟨init_implies0.pub (stripConsts piConsts s₁) (stripConsts piConsts s₂)
      (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_consts.mp hp).1,
    symAddr_eq_iff.mp ((pub_consts.mp hp).2 _ List.mem_cons_self)⟩
  sat := ⟨initSatC, initSat_pre⟩

end VG.Proof.Rc2.Arm.Stream

end

/-!
# Streaming RC2-CBC on ARMv7: facts shared by the proofs

Sub-ranges of buffers and stack arguments.
-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm

theorem ivSub (C : BitVec 32) : Region.Sub ⟨State.addr C + BitVec.ofNat 64 128, 8⟩ ⟨State.addr C, 144⟩ :=
  Offset.sub_base _ (by decide)
theorem lrSub (S : BitVec 32) : Region.Sub ⟨State.addr S + BitVec.ofNat 64 512, 4⟩ ⟨State.addr S, 576⟩ :=
  Offset.sub_base _ (by decide)

theorem ofNat_toNat32 (x : BitVec 32) : x = BitVec.ofNat 32 x.toNat := by simp

theorem add0 (a : Addr) : a + BitVec.ofNat 64 0 = a := BitVec.add_zero a

theorem e128 : (128 : Addr) = BitVec.ofNat 64 128 := rfl
theorem e136 : (136 : Addr) = BitVec.ofNat 64 136 := rfl
/-- A range at an offset within a region of `rs`. -/
theorem cov1 {rs : List Region} {b : Addr} {len : Nat} (hR : (⟨b, len⟩ : Region) ∈ rs) {off n : Nat}
    (h : off + n ≤ len) : Covers [⟨b + BitVec.ofNat 64 off, n⟩] rs :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, hR, off, rfl, h⟩

/-- The `i`-th stack argument, of the 12 bytes of them. -/
theorem stackArgAddr_eq (s : State) {i : Nat} (hi : i < 3) (hsp : s.sp.toNat + 12 ≤ 2 ^ 32) :
    stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (4 * i) := by
  unfold stackArgAddr
  rw [show s.sp + BitVec.ofNat 32 (4 * 0) = s.sp from BitVec.add_zero _, addr_add (by omega_arith)]

theorem argIn {s : State} {rs : List Region} (hR : (⟨stackArgAddr s 0, 12⟩ : Region) ∈ rs) {i : Nat}
    (hi : i < 3) (hsp : s.sp.toNat + 12 ≤ 2 ^ 32) : InRegions rs (stackArgAddr s i) 4 := by
  rw [stackArgAddr_eq s hi hsp]
  exact ⟨_, hR, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

/-- Memory reads of 1 byte within a word written elsewhere. -/
theorem bytesAt_writeW {m : Mem} {p a : Addr} {n : Nat} (v : BitVec 32) (hn : n ≤ 2 ^ 64)
    (hd : (⟨p, n⟩ : Region).Disjoint ⟨a, 4⟩) :
    Spec.Rc2.bytesAt (m.writeW a v) p n = Spec.Rc2.bytesAt m p n :=
  VG.Proof.Rc2.bytesAt_frame ((Frame.refl _ _).writeW (r := ⟨a, 4⟩) (List.mem_singleton_self _) _
    (Region.contains_self _ _)) p n hn (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd)

/-- A stack argument, read from memory that changed only outside the arguments. -/
theorem stackArg_frame {s : State} {m : Mem} {rs : List Region} (hf : Frame rs s.mem m)
    (hsp : s.sp.toNat + 12 ≤ 2 ^ 32) (hd : ∀ r ∈ rs, (⟨stackArgAddr s 0, 12⟩ : Region).Disjoint r)
    {i : Nat} (hi : i < 3) : m.readW (stackArgAddr s i) 32 = stackArg s i := by
  rw [stackArg]
  refine hf.readW ?_ hd (by decide)
  rw [stackArgAddr_eq s hi hsp]
  exact Offset.contains_base _ (by omega_arith) (by omega_arith)

theorem preserved_ne {r : Reg} (hr : r ∈ preserved) (hl : r ≠ .lr) :
    r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hl | decide

/-- `t` is `s` but for `r12` and the flags. -/
structure Keep (s t : State) : Prop where
  reg : ∀ r, r ≠ .r12 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

end VG.Proof.Rc2.Arm.Stream
