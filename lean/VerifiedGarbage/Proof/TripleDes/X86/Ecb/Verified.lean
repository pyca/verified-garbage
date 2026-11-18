module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Rc2.X86.Cbc.CallFrame
import VerifiedGarbage.Proof.CmacTripleDes.X86.Block
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.TripleDes.EcbMemory
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.TripleDes.X86.ConstantTime
public import VerifiedGarbage.Proof.TripleDes.Scratch
public import VerifiedGarbage.Proof.Rc2.X86.Save
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Rc2.X86.BlockArgs
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Rc2.Select
import VerifiedGarbage.Proof.Rc2.Select32
import VerifiedGarbage.Proof.Rc2.Word
import VerifiedGarbage.Proof.Rc2.Word32
import VerifiedGarbage.Proof.Rc2.X86.KeyIO
import VerifiedGarbage.Proof.Rc2.X86.KeyLookup
import VerifiedGarbage.Proof.Rc2.X86.RoundSteps
import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Proof.TripleDes.X86.Bytes
public import VerifiedGarbage.Proof.TripleDes.X86.RestoredOutput
import VerifiedGarbage.Proof.TripleDes.X86.WordStore
import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.X86.Bitsliced.SboxLit
public import VerifiedGarbage.Proof.TripleDes.X86.Bitsliced.Batch
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.TripleDes.Core
import Batteries.Logic
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.X86.Taint

/-! ### `TripleDes.X86.CorrectBlock`, which this module and modules that import it used -/

section

/-! ### `TripleDes.X86.Head`, which only this module used -/

section

/-! ### `TripleDes.X86.Body`, which only this module used -/

section

/-! ## `Loop` -/

@[expose] public section

section

namespace VG.Proof.TripleDes.X86

open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix feistelStep)

def keyAddr (base : BitVec 32) (direction : Direction) (j : Nat) : BitVec 32 :=
  base + BitVec.ofNat 32 (8 * (if direction = .encrypt then j else 15 - j))

def readKey (m : Mem) (ptr : BitVec 32) : BitVec 64 :=
  m.readW (wordAddr ptr 1) 32 ++ m.readW (wordAddr ptr 0) 32

theorem readKey_frame {m m' : Mem} {ptr : BitVec 32} {regions : List Region}
    (hf : Frame regions m m')
    (sep : ∀ j < 2, ∀ r ∈ regions, (⟨wordAddr ptr j, 4⟩ : Region).Disjoint r) :
    readKey m' ptr = readKey m ptr := by
  exact congrArg₂ (fun hi lo : BitVec 32 => hi ++ lo)
    (hf.readW (a := wordAddr ptr 1) (w := 32) (r := ⟨wordAddr ptr 1, 4⟩)
      (Region.contains_self _ _) (sep 1 (by decide)) (by decide))
    (hf.readW (a := wordAddr ptr 0) (w := 32) (r := ⟨wordAddr ptr 0, 4⟩)
      (Region.contains_self _ _) (sep 0 (by decide)) (by decide))

theorem keyAddr_step (base : BitVec 32) (direction : Direction) (j : Nat) (hj : j < 15) :
    (if direction = .encrypt then keyAddr base direction j + 8
      else keyAddr base direction j - 8) = keyAddr base direction (j + 1) := by
  cases direction
  · change base + BitVec.ofNat 32 (8 * j) + BitVec.ofNat 32 8 = base + BitVec.ofNat 32 (8 * (j + 1))
    rw [Offset.add_ofNat_add_ofNat]
    exact congrArg (fun n => base + BitVec.ofNat 32 n) (by omega_using [])
  · change base + BitVec.ofNat 32 (8 * (15 - j)) - BitVec.ofNat 32 8 = base + BitVec.ofNat 32 (8 * (15 - (j + 1)))
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      Offset.ofNat_sub_ofNat (by omega_using [hj])]
    exact congrArg (fun n => base + BitVec.ofNat 32 n) (by omega_using [])

def endPointer (base : BitVec 32) (d : Direction) : BitVec 32 :=
  if d = .encrypt then base + 128 else base - 8

theorem keyAddr_end (base : BitVec 32) (d : Direction) :
    (if d = .encrypt then keyAddr base d 15 + 8 else keyAddr base d 15 - 8) = endPointer base d := by
  cases d <;> simp only [endPointer, keyAddr, reduceCtorEq, ite_true, ite_false, Nat.reduceSub, Nat.reduceMul]
  · change base + BitVec.ofNat 32 120 + BitVec.ofNat 32 8 = base + BitVec.ofNat 32 128
    rw [Offset.add_ofNat_add_ofNat]
  · rw [BitVec.add_zero]

structure LoopInv (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32) (n : Nat) (s : State) : Prop where
  positive : 1 ≤ n
  bounded : n ≤ 16
  left : s.gpr .esi = (roundPrefix keys direction (16 - n) v).1
  right : s.gpr .edi = (roundPrefix keys direction (16 - n) v).2
  counter : roundCount s = BitVec.ofNat 32 n
  pointer : roundKeyPtr s = keyAddr base direction (16 - n)
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  base : s.gpr .ebp = origin.gpr .ebp
  sp : s.gpr .esp = origin.gpr .esp
  frame : Frame [workRegion origin] origin.mem s.mem

structure LoopPost (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32) (s : State) : Prop where
  left : s.gpr .esi = (roundPrefix keys direction 16 v).1
  right : s.gpr .edi = (roundPrefix keys direction 16 v).2
  counter : roundCount s = 0
  pointer : roundKeyPtr s = endPointer base direction
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  base : s.gpr .ebp = origin.gpr .ebp
  sp : s.gpr .esp = origin.gpr .esp
  frame : Frame [workRegion origin] origin.mem s.mem

theorem loopStep (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (keyAddr base direction j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (keyAddr base direction j) t, 4⟩ : Region).Disjoint (workRegion origin))
    (hslots : ∀ j < 16, ∀ k < 128, ∀ t < 2,
      Mem.Sep (wordAddr (origin.gpr .ebp) k) 4 (wordAddr (keyAddr base direction j) t) 4)
    (hkeys : ∀ j < 16, (readKey origin.mem (keyAddr base direction j)).setWidth 48 =
      roundKey keys direction j)
    (n : Nat) (s : State) (hs : LoopInv keys direction base origin v n s) :
    WP isa (.block (roundBody ++ roundAdvance direction)) s (fun s' =>
      (isa.eval .ne s' = some false ∧ LoopPost keys direction base origin v s') ∨
      (isa.eval .ne s' = some true ∧ ∃ m < n, LoopInv keys direction base origin v m s')) := by
  obtain hj : 16 - n < 16 := by omega_using [hs.positive]
  obtain hwork : workRegion s = workRegion origin := by simp only [workRegion, hs.base]
  obtain hokS : Ok sboxCfg s := hok.congr hs.base hs.base hs.rd hs.wr
  obtain preS : BoxPre s := by
    refine ⟨hokS, ?_, ?_, ?_⟩
    · rw [hs.rd, hs.wr, hs.pointer]; exact hread _ hj
    · intro t ht a ha hb
      obtain hsw := spill_sub_work s a hb
      rw [hwork] at hsw
      rw [hs.pointer] at ha
      exact hsep _ hj t ht a ha hsw
    · rw [hs.base, hs.pointer]; exact hslots _ hj
  obtain hk : (roundKeyWord s).setWidth 48 = roundKey keys direction (16 - n) := by
    change (readKey s.mem (roundKeyPtr s)).setWidth 48 = _
    rw [hs.pointer]
    obtain hmem := readKey_frame hs.frame (ptr := keyAddr base direction (16 - n))
      (fun t ht q hq => by obtain rfl := List.mem_singleton.mp hq; exact hsep _ hj t ht)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hkeys _ hj)
  obtain ⟨s', run, left, right, ptr, count, flag, rd, wr, keptBase, keptSp, frame⟩ :=
    roundStep_ok direction s _ _ (roundKeyWord s) n hs.positive
      (by omega_using [hs.bounded]) hs.left hs.right rfl preS hs.counter
  obtain hidx : 16 - (n - 1) = 16 - n + 1 := by
    omega_using [hs.positive, hs.bounded]
  obtain hleft : s'.gpr .esi = (roundPrefix keys direction (16 - (n - 1)) v).1 := by
    rw [hidx]
    exact left.trans (congrArg (fun pair => pair.1)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  obtain hright : s'.gpr .edi = (roundPrefix keys direction (16 - (n - 1)) v).2 := by
    rw [hidx]
    obtain hval := congrArg (fun key =>
      ((roundPrefix keys direction (16 - n) v).1 ^^^
        Spec.TripleDes.roundFunction (roundPrefix keys direction (16 - n) v).2 key)) hk
    exact (right.trans hval).trans (congrArg (fun pair => pair.2)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  obtain hframe : Frame [workRegion origin] origin.mem s'.mem := by
    rw [hwork] at frame
    exact hs.frame.trans frame
  refine WP.of_runBlock ⟨s', run, ?_⟩
  by_cases hlast : n = 1
  · left
    refine ⟨?_, ?_⟩
    · simpa only [hlast, ne_eq, not_true_eq_false, decide_false] using flag
    · subst n
      exact ⟨hleft, hright, count, by
        rw [ptr, nextPtr, hs.pointer]
        exact keyAddr_end base direction, rd.trans hs.rd, wr.trans hs.wr, keptBase.trans hs.base, keptSp.trans hs.sp, hframe⟩
  · right
    refine ⟨?_, n - 1, by omega_using [hs.positive], ?_⟩
    · simpa only [hlast, ne_eq, not_false_eq_true, decide_true] using flag
    · refine ⟨by omega_using [hs.positive, hlast], by omega_using [hs.bounded],
        hleft, hright, count, ?_, rd.trans hs.rd, wr.trans hs.wr, keptBase.trans hs.base, keptSp.trans hs.sp, hframe⟩
      rw [ptr, nextPtr, hs.pointer, keyAddr_step base direction (16 - n) (by
        omega_using [hs.positive, hlast]), ← hidx]

/-- The complete sixteen-round loop, in either key order. -/
theorem roundsLoop_ok (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hl : origin.gpr .esi = v.1) (hr : origin.gpr .edi = v.2)
    (hptr : roundKeyPtr origin = keyAddr base direction 0)
    (hcount : roundCount origin = BitVec.ofNat 32 16)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (keyAddr base direction j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (keyAddr base direction j) t, 4⟩ : Region).Disjoint (workRegion origin))
    (hslots : ∀ j < 16, ∀ k < 128, ∀ t < 2,
      Mem.Sep (wordAddr (origin.gpr .ebp) k) 4 (wordAddr (keyAddr base direction j) t) 4)
    (hkeys : ∀ j < 16, (readKey origin.mem (keyAddr base direction j)).setWidth 48 =
      roundKey keys direction j) :
    WP isa (.loop (.block (roundBody ++ roundAdvance direction)) .ne)
      origin (LoopPost keys direction base origin v) := by
  apply WP.loop (M := isa) (body := .block (roundBody ++ roundAdvance direction))
    (c := .ne) (Q := LoopPost keys direction base origin v) (LoopInv keys direction base origin v)
    (loopStep keys direction base origin v hok hread hsep hslots hkeys)
    16 origin
  exact ⟨by decide, by decide, hl, hr, hcount, hptr, rfl, rfl, rfl, rfl, Frame.refl _ _⟩

end VG.Proof.TripleDes.X86

end

/-! ## `PassStart` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.X86.RegUpd VG.Impl.TripleDes.X86
open VG.Spec.TripleDes (Direction)

def scheduleArg (s : State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .esp) 1) 32

def startAddr (c : Nat) (d : Direction) (s : State) : BitVec 32 :=
  scheduleArg s + BitVec.ofNat 32 (128 * c + if d = .encrypt then 0 else 120)

def startMem (c : Nat) (d : Direction) (s : State) : Mem :=
  (s.mem.writeW (wordAddr (s.gpr .ebp) 4) (startAddr c d s)).writeW
    (wordAddr (s.gpr .ebp) 5) (16 : BitVec 32)

theorem passStart_ok (c : Nat) (d : Direction) (s : State) (hok : Ok sboxCfg s)
    (hr : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 1) 4) :
    ∃ s', runBlock isa (passStart c d) s = some s' ∧ s'.mem = startMem c d s ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) := by
  obtain hw4 := hok.slotIn 4 (by decide)
  obtain hw5 := hok.slotIn 5 (by decide)
  simp only [wordAddr, addr, sboxCfg] at hw4 hw5 hr
  refine ⟨_, by
    simp only [passStart, imm, runBlock_cons, runStep_some, runBlock_nil, exec,
      execAlu, readSrc, State.load32, State.store32, State.ea, memOp, hw4, hw5, hr,
      ite_true, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
      mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
      reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · intro r hr
    simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]

/-- Starting a DES pass writes only its public pointer and round count. -/
theorem start_frame (c : Nat) (d : Direction) (s : State)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32) : Frame [workRegion s] s.mem (startMem c d s) := by
  obtain h4 : (workRegion s).Contains (wordAddr (s.gpr .ebp) 4) 4 := by
    change (workRegion s).Contains (addr (s.gpr .ebp) 16) 4
    rw [addr_eq (by omega_using [fit])]
    exact Offset.contains _ (by decide) (by decide) (by decide)
  obtain h5 : (workRegion s).Contains (wordAddr (s.gpr .ebp) 5) 4 := by
    change (workRegion s).Contains (addr (s.gpr .ebp) 20) 4
    rw [addr_eq (by omega_using [fit])]
    exact Offset.contains _ (by decide) (by decide) (by decide)
  exact ((Frame.refl [workRegion s] s.mem).writeW (List.mem_singleton_self _) _ h4).writeW
    (List.mem_singleton_self _) _ h5

theorem start_pointer (c : Nat) (d : Direction) (s : State) (t : State)
    (base : t.gpr .ebp = s.gpr .ebp) (mem : t.mem = startMem c d s)
    (fit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32) :
    roundKeyPtr t = startAddr c d s ∧ roundCount t = 16 := by
  obtain hsep : Mem.Sep (wordAddr (s.gpr .ebp) 4) 4 (wordAddr (s.gpr .ebp) 5) 4 := by
    intro a h4 h5; exact counter_ptr_sep s fit a h5 h4
  constructor
  · unfold roundKeyPtr
    rw [base, mem, startMem, Mem.readW_writeW_sep hsep (by decide), Mem.readW_writeW_self32]
  · unfold roundCount
    rw [base, mem, startMem, Mem.readW_writeW_self32]
end VG.Proof.TripleDes.X86

end

/-! ## `Pass` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix)

structure PassPost (keys : DesSchedule) (d : Direction) (origin : State)
    (v : BitVec 32 × BitVec 32) (s : State) : Prop where
  left : s.gpr .esi = (roundPrefix keys d 16 v).2
  right : s.gpr .edi = (roundPrefix keys d 16 v).1
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  base : s.gpr .ebp = origin.gpr .ebp
  sp : s.gpr .esp = origin.gpr .esp
  frame : Frame [workRegion origin] origin.mem s.mem

theorem roundsWithSwap_ok (keys : DesSchedule) (d : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32) (hok : Ok sboxCfg origin)
    (hl : origin.gpr .esi = v.1) (hr : origin.gpr .edi = v.2)
    (hptr : roundKeyPtr origin = keyAddr base d 0) (hcount : roundCount origin = 16)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (keyAddr base d j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (keyAddr base d j) t, 4⟩ : Region).Disjoint (workRegion origin))
    (hslots : ∀ j < 16, ∀ k < 128, ∀ t < 2,
      Mem.Sep (wordAddr (origin.gpr .ebp) k) 4 (wordAddr (keyAddr base d j) t) 4)
    (hkeys : ∀ j < 16, (readKey origin.mem (keyAddr base d j)).setWidth 48 = roundKey keys d j) :
    WP isa (.seq (.loop (.block (roundBody ++ roundAdvance d)) .ne) (.block swapHalves))
      origin (PassPost keys d origin v) := by
  apply WP.seq
  apply WP.mono (roundsLoop_ok keys d base origin v hok hl hr hptr hcount hread hsep hslots hkeys)
  intro s hs
  obtain ⟨s', run, left, right, rd, wr, mem, keptBase, keptSp⟩ := swapHalves_ok s
  apply WP.of_runBlock
  refine ⟨s', run, left.trans hs.right, right.trans hs.left, rd.trans hs.rd, wr.trans hs.wr,
    keptBase.trans hs.base, keptSp.trans hs.sp, ?_⟩
  rw [mem]; exact hs.frame

theorem pass_ok (c : Nat) (keys : DesSchedule) (d : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32) (hok : Ok sboxCfg origin)
    (hl : origin.gpr .esi = v.1) (hr : origin.gpr .edi = v.2)
    (hptr : startAddr c d origin = keyAddr base d 0)
    (harg : InRegions (origin.rd ++ origin.wr) (wordAddr (origin.gpr .esp) 1) 4)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (keyAddr base d j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (keyAddr base d j) t, 4⟩ : Region).Disjoint (workRegion origin))
    (hslots : ∀ j < 16, ∀ k < 128, ∀ t < 2,
      Mem.Sep (wordAddr (origin.gpr .ebp) k) 4 (wordAddr (keyAddr base d j) t) 4)
    (hkeys : ∀ j < 16, (readKey origin.mem (keyAddr base d j)).setWidth 48 = roundKey keys d j) :
    WP isa (pass c d) origin (PassPost keys d origin v) := by
  obtain ⟨s, run, mem, rd, wr, regs⟩ := passStart_ok c d origin hok harg
  obtain keptBase := regs .ebp (by decide)
  obtain keptSp := regs .esp (by decide)
  obtain hwork : workRegion s = workRegion origin := by simp only [workRegion, keptBase]
  obtain hf : Frame [workRegion origin] origin.mem s.mem := by
    rw [mem]; exact start_frame c d origin hok.fit
  obtain hkeysS : ∀ j < 16, (readKey s.mem (keyAddr base d j)).setWidth 48 = roundKey keys d j := by
    intro j hj
    obtain heq := readKey_frame hf (ptr := keyAddr base d j)
      (fun t ht q hq => by obtain rfl := List.mem_singleton.mp hq; exact hsep j hj t ht)
    exact (congrArg (BitVec.setWidth 48) heq).trans (hkeys j hj)
  obtain hreadS : ∀ j < 16, ∀ t < 2, InRegions (s.rd ++ s.wr) (wordAddr (keyAddr base d j) t) 4 := by
    rw [rd, wr]; exact hread
  obtain hsepS : ∀ j < 16, ∀ t < 2, (⟨wordAddr (keyAddr base d j) t, 4⟩ : Region).Disjoint (workRegion s) := by
    rw [hwork]; exact hsep
  obtain hslotsS : ∀ j < 16, ∀ k < 128, ∀ t < 2,
      Mem.Sep (wordAddr (s.gpr .ebp) k) 4 (wordAddr (keyAddr base d j) t) 4 := by
    rw [keptBase]; exact hslots
  obtain start := start_pointer c d origin s keptBase mem hok.fit
  obtain htail := roundsWithSwap_ok keys d base s v (hok.congr keptBase keptBase rd wr)
    ((regs .esi (by decide)).trans hl) ((regs .edi (by decide)).trans hr)
    (start.1.trans hptr) start.2 hreadS hsepS hslotsS hkeysS
  apply WP.seq
  apply WP.of_runBlock
  refine ⟨s, run, WP.mono htail ?_⟩
  intro s' hs
  refine ⟨hs.left, hs.right, hs.rd.trans rd, hs.wr.trans wr, hs.base.trans keptBase,
    hs.sp.trans keptSp, ?_⟩
  have hframe := hs.frame
  rw [hwork] at hframe
  exact hf.trans hframe
end VG.Proof.TripleDes.X86

end

/-! ## `WordState` -/

section

namespace VG.Proof.TripleDes.X86

open VG VG.X86 VG.Impl.TripleDes.X86
open VG.Proof.TripleDes (desCore roundPrefix)

/-- A DES word held as two 32-bit Feistel registers. -/
structure WordState (x : BitVec 64) (s : State) : Prop where
  left : s.gpr .esi = ((x >>> 32).setWidth 32)
  right : s.gpr .edi = (x.setWidth 32)

theorem PassPost.wordState {keys : Spec.TripleDes.DesSchedule}
    {direction : Spec.TripleDes.Direction} {origin s : State} {x : BitVec 64}
    (hs : PassPost keys direction origin ((x >>> 32).setWidth 32, x.setWidth 32) s) :
    WordState (desCore keys direction x) s := by
  obtain hcore := VG.Proof.TripleDes.desCore_roundPrefix keys direction x
  let halves := roundPrefix keys direction 16 ((x >>> 32).setWidth 32, x.setWidth 32)
  obtain hleft : ((desCore keys direction x >>> 32).setWidth 32) = halves.2 :=
    (congrArg (fun v : BitVec 64 => ((v >>> 32).setWidth 32)) hcore).trans
      (VG.Proof.TripleDes.appended_left halves.2 halves.1)
  obtain hright : ((desCore keys direction x).setWidth 32) = halves.1 :=
    (congrArg (fun v : BitVec 64 => (v.setWidth 32)) hcore).trans
      (VG.Proof.TripleDes.appended_right halves.2 halves.1)
  exact ⟨hs.left.trans hleft.symm, hs.right.trans hright.symm⟩

end VG.Proof.TripleDes.X86

end

/-! ## `Ready` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

def componentBase (base : BitVec 32) (component : Nat) : BitVec 32 :=
  base + BitVec.ofNat 32 (128 * component)

structure Ready (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) : Prop where
  spills : Ok sboxCfg s
  schedule : scheduleArg s = base
  argRead : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 1) 4
  argSeparate : (⟨wordAddr (s.gpr .esp) 1, 4⟩ : Region).Disjoint (workRegion s)
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    InRegions (s.rd ++ s.wr) (wordAddr (keyAddr (componentBase base c) d j) t) 4
  separate : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    (⟨wordAddr (keyAddr (componentBase base c) d j) t, 4⟩ : Region).Disjoint (workRegion s)
  slots : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ k < 128, ∀ t < 2,
    Mem.Sep (wordAddr (s.gpr .ebp) k) 4 (wordAddr (keyAddr (componentBase base c) d j) t) 4
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (readKey s.mem (keyAddr (componentBase base c) d j)).setWidth 48 = roundKey (keys c) d j

theorem Ready.congr {keys : Nat → DesSchedule} {base : BitVec 32} {s t : State}
    (hs : Ready keys base s) (hbase : t.gpr .ebp = s.gpr .ebp) (hsp : t.gpr .esp = s.gpr .esp)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hf : Frame [workRegion s] s.mem t.mem) : Ready keys base t := by
  obtain hwork : workRegion t = workRegion s := by unfold workRegion; rw [hbase]
  refine ⟨hs.spills.congr hbase hbase hrd hwr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold scheduleArg
    rw [hsp]
    obtain hm := hf.readW (a := wordAddr (s.gpr .esp) 1) (w := 32)
      (r := ⟨wordAddr (s.gpr .esp) 1, 4⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hs.argSeparate) (by decide)
    exact hm.trans hs.schedule
  · rw [hsp, hrd, hwr]; exact hs.argRead
  · rw [hsp, hwork]; exact hs.argSeparate
  · rw [hrd, hwr]; exact hs.read
  · rw [hwork]; exact hs.separate
  · rw [hbase]; exact hs.slots
  · intro c hc d j hj
    obtain hm := readKey_frame hf (ptr := keyAddr (componentBase base c) d j)
      (fun t ht q hq => by obtain rfl := List.mem_singleton.mp hq; exact hs.separate c hc d j hj t ht)
    exact (congrArg (BitVec.setWidth 48) hm).trans (hs.values c hc d j hj)

theorem Ready.congrFrame {keys : Nat → DesSchedule} {base : BitVec 32} {s t : State}
    (hs : Ready keys base s) (hbase : t.gpr .ebp = s.gpr .ebp) (hsp : t.gpr .esp = s.gpr .esp)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (rs : List Region) (hf : Frame rs s.mem t.mem)
    (hargs : ∀ q ∈ rs, (⟨wordAddr (s.gpr .esp) 1, 4⟩ : Region).Disjoint q)
    (hkeys : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ i < 2, ∀ q ∈ rs,
      (⟨wordAddr (keyAddr (componentBase base c) d j) i, 4⟩ : Region).Disjoint q) :
    Ready keys base t := by
  obtain hwork : workRegion t = workRegion s := by unfold workRegion; rw [hbase]
  refine ⟨hs.spills.congr hbase hbase hrd hwr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold scheduleArg
    rw [hsp]
    obtain hm := hf.readW (a := wordAddr (s.gpr .esp) 1) (w := 32)
      (r := ⟨wordAddr (s.gpr .esp) 1, 4⟩) (Region.contains_self _ _)
      hargs (by decide)
    exact hm.trans hs.schedule
  · rw [hsp, hrd, hwr]; exact hs.argRead
  · rw [hsp, hwork]; exact hs.argSeparate
  · rw [hrd, hwr]; exact hs.read
  · rw [hwork]; exact hs.separate
  · rw [hbase]; exact hs.slots
  · intro c hc d j hj
    obtain hm := readKey_frame hf (ptr := keyAddr (componentBase base c) d j)
      (hkeys c hc d j hj)
    exact (congrArg (BitVec.setWidth 48) hm).trans (hs.values c hc d j hj)

structure Stable (origin s : State) : Prop where
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  bp : s.gpr .ebp = origin.gpr .ebp
  sp : s.gpr .esp = origin.gpr .esp
  frame : Frame [workRegion origin] origin.mem s.mem

theorem Stable.trans {s t u : State} (hs : Stable s t) (ht : Stable t u) : Stable s u := by
  obtain hwork : workRegion t = workRegion s := by unfold workRegion; rw [hs.bp]
  have hf := ht.frame
  rw [hwork] at hf
  exact ⟨ht.rd.trans hs.rd, ht.wr.trans hs.wr, ht.bp.trans hs.bp, ht.sp.trans hs.sp,
    hs.frame.trans hf⟩

theorem passPointer (base : BitVec 32) (c : Nat) (d : Direction) (s : State)
    (hs : scheduleArg s = base) : startAddr c d s = keyAddr (componentBase base c) d 0 := by
  cases d <;> simp only [startAddr, keyAddr, componentBase, hs, reduceCtorEq,
    ite_true, ite_false, Nat.mul_zero, Nat.sub_zero, Nat.reduceMul]
  all_goals rw [Offset.add_ofNat_add_ofNat]

theorem pass_word_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) (x : BitVec 64)
    (c : Nat) (hc : c < 3) (d : Direction) (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (pass c d) s (fun t => WordState (VG.Proof.TripleDes.desCore (keys c) d x) t ∧
      Ready keys base t ∧ Stable s t) := by
  apply WP.mono (pass_ok c (keys c) d (componentBase base c) s
    ((x >>> 32).setWidth 32, x.setWidth 32) hready.spills hword.left hword.right
    (passPointer base c d s hready.schedule) hready.argRead (hready.read c hc d)
    (hready.separate c hc d) (hready.slots c hc d) (hready.values c hc d))
  intro t ht
  exact ⟨ht.wordState, hready.congr ht.base ht.sp ht.rd ht.wr ht.frame,
    ⟨ht.rd, ht.wr, ht.base, ht.sp, ht.frame⟩⟩

end VG.Proof.TripleDes.X86

end

/-! ## `Body` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.Impl.TripleDes.X86
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (desCore)

theorem threePasses_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) (x : BitVec 64)
    (c₀ c₁ c₂ : Nat) (h₀ : c₀ < 3) (h₁ : c₁ < 3) (h₂ : c₂ < 3)
    (d₀ d₁ d₂ : Direction) (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (.seq (pass c₀ d₀) (.seq (pass c₁ d₁) (pass c₂ d₂))) s
      (fun t => WordState (desCore (keys c₂) d₂ (desCore (keys c₁) d₁ (desCore (keys c₀) d₀ x))) t ∧
        Ready keys base t ∧ Stable s t) := by
  apply WP.seq
  apply WP.mono (pass_word_ok keys base s x c₀ h₀ d₀ hready hword)
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (pass_word_ok keys base s₁ _ c₁ h₁ d₁ hs₁.2.1 hs₁.1)
  intro s₂ hs₂
  apply WP.mono (pass_word_ok keys base s₂ _ c₂ h₂ d₂ hs₂.2.1 hs₂.1)
  intro s₃ hs₃
  exact ⟨hs₃.1, hs₃.2.1, hs₁.2.2.trans (hs₂.2.2.trans hs₃.2.2)⟩

def blockCore (keys : Nat → DesSchedule) (direction : Direction) (x : BitVec 64) : BitVec 64 :=
  match direction with
  | .encrypt => desCore (keys 2) .encrypt (desCore (keys 1) .decrypt (desCore (keys 0) .encrypt x))
  | .decrypt => desCore (keys 0) .decrypt (desCore (keys 1) .encrypt (desCore (keys 2) .decrypt x))

theorem blockBody_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) (x : BitVec 64)
    (direction : Direction) (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (blockBody direction) s
      (fun t => WordState (blockCore keys direction x) t ∧ Ready keys base t ∧ Stable s t) := by
  cases direction
  · exact threePasses_ok keys base s x 0 1 2 (by decide) (by decide) (by decide)
      .encrypt .decrypt .encrypt hready hword
  · exact threePasses_ok keys base s x 2 1 0 (by decide) (by decide) (by decide)
      .decrypt .encrypt .decrypt hready hword

end VG.Proof.TripleDes.X86

end

end

end


@[expose] public section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.Rc2.X86 (addr32)

def prepared (s : State) : State := s.setReg .ebp (scratchArg s 3)
def saveRegion (s : State) : Region := ⟨addr32 (scratchArg s 3), 16⟩

structure HeadPre (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) : Prop where
  ready : Ready keys base (prepared s)
  scratchFit : (scratchArg s 3).toNat + 512 ≤ 2 ^ 32
  dataFit : (dataArg s).toNat + 8 ≤ 2 ^ 32
  saveWrite : ∀ i < 4, InRegions s.wr (addr32 (scratchArg s 3) + BitVec.ofNat 64 (4 * i)) 4
  argRead : ∀ i ∈ [1, 2, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4
  argSeparate : ∀ i ∈ [1, 2, 3], (⟨wordAddr (s.gpr .esp) i, 4⟩ : Region).Disjoint (saveRegion s)
  dataRead : ∀ i < 2, InRegions (s.rd ++ s.wr) (wordAddr (dataArg s) i) 4
  dataSeparate : (⟨addr32 (dataArg s), 8⟩ : Region).Disjoint (saveRegion s)
  keySeparate : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    (⟨wordAddr (keyAddr (componentBase base c) d j) t, 4⟩ : Region).Disjoint (saveRegion s)

structure HeadPost (keys : Nat → DesSchedule) (base : BitVec 32) (original s : State) : Prop where
  word : WordState (Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt original.mem (addr32 (dataArg original))))) s
  ready : Ready keys base s
  saved : Saved original s
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  bp : s.gpr .ebp = scratchArg original 3
  sp : s.gpr .esp = original.gpr .esp
  data : dataArg s = dataArg original
  frame : Frame [saveRegion original] original.mem s.mem

theorem blockHead_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State)
    (hp : HeadPre keys base s) : WP isa (.block (blockSave ++ blockLoad)) s (HeadPost keys base s) := by
  rw [WP.block_append_iff, blockSave]
  apply WP.mono (saveWithArg_ok s 3 (hp.argRead 3 (by decide)) hp.scratchFit hp.saveWrite)
  intro s₁ h₁
  obtain sp₁ : s₁.gpr .esp = s.gpr .esp := h₁.reg .esp (by decide) (by decide)
  have frame₁ : Frame [saveRegion s] s.mem s₁.mem := h₁.frame
  have bp₁ : s₁.gpr .ebp = (prepared s).gpr .ebp := h₁.bp
  obtain sp₁' : s₁.gpr .esp = (prepared s).gpr .esp := by
    rw [prepared, gpr_setReg_of_ne _ _ (by decide)]; exact sp₁
  obtain ready₁ : Ready keys base s₁ := hp.ready.congrFrame bp₁ sp₁' h₁.rd h₁.wr
    [saveRegion s] frame₁
    (by intro q hq; obtain rfl := List.mem_singleton.mp hq
        rw [prepared, gpr_setReg_of_ne _ _ (by decide)]
        exact hp.argSeparate 1 (by decide))
    (by intro c hc d j hj i hi q hq; obtain rfl := List.mem_singleton.mp hq
        exact hp.keySeparate c hc d j hj i hi)
  obtain data₁ : dataArg s₁ = dataArg s := by
    unfold dataArg
    rw [sp₁]
    exact frame₁.readW (r := ⟨wordAddr (s.gpr .esp) 2, 4⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.argSeparate 2 (by decide)) (by decide)
  obtain args₁ : InRegions (s₁.rd ++ s₁.wr) (wordAddr (s₁.gpr .esp) 2) 4 := by
    rw [sp₁, h₁.rd, h₁.wr]; exact hp.argRead 2 (by decide)
  obtain reads₁ : ∀ i < 2, InRegions (s₁.rd ++ s₁.wr) (wordAddr (dataArg s₁) i) 4 := by
    rw [h₁.rd, h₁.wr, data₁]; exact hp.dataRead
  obtain input₁ : Spec.TripleDes.blockAt s₁.mem (addr32 (dataArg s₁)) =
      Spec.TripleDes.blockAt s.mem (addr32 (dataArg s)) := by
    rw [data₁]
    exact VG.Proof.TripleDes.blockAt_eq_of_frame _ frame₁
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.dataSeparate)
  apply WP.mono (blockLoad_ok s₁ (by rw [data₁]; exact hp.dataFit) args₁ reads₁)
  intro s₂ h₂
  obtain hf : Frame [workRegion s₁] s₁.mem s₂.mem := by rw [h₂.mem]; exact Frame.refl _ _
  obtain input := congrArg (fun b => Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock b)) input₁
  refine ⟨⟨h₂.l.trans (congrArg (fun x : BitVec 64 => (x >>> 32).setWidth 32) input),
    h₂.r.trans (congrArg (fun x : BitVec 64 => x.setWidth 32) input)⟩,
    ready₁.congr h₂.bp h₂.sp h₂.rd h₂.wr hf, h₁.saved.congr h₂.bp hf,
    h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.bp.trans h₁.bp, h₂.sp.trans sp₁, ?_, ?_⟩
  · unfold dataArg
    rw [h₂.mem, h₂.sp]
    exact data₁
  · rw [h₂.mem]; exact frame₁

end VG.Proof.TripleDes.X86

end

end


/-! ## `RestoredTail` -/

@[expose] public section

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32)

structure RestoredTailPost (original origin : State) (x : BitVec 64) (s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (addr32 (dataArg origin)) =
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp x)
  saved : ∀ r ∈ savedRegs, s.gpr r = original.gpr r
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.gpr .esp = origin.gpr .esp
  frame : Frame [⟨addr32 (dataArg origin), 8⟩, workRegion origin] origin.mem s.mem

theorem blockTailRestored_ok (original s : State) (x : BitVec 64) (hword : WordState x s)
    (hsaved : Saved original s) (hok : Ok sboxCfg s)
    (dataFit : (dataArg s).toNat + 8 ≤ 2 ^ 32)
    (harg : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 2) 4)
    (hargSep : (⟨wordAddr (s.gpr .esp) 2, 4⟩ : Region).Disjoint (workRegion s))
    (hw : ∀ i < 2, InRegions s.wr (wordAddr (dataArg s) i) 4)
    (hread : ∀ i < 4, InRegions (s.rd ++ s.wr) (addr32 (s.gpr .ebp) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block (finalSave ++ blockRestore ++ restoredOutput)) s (RestoredTailPost original s x) := by
  rw [WP.block_append_iff, WP.block_append_iff]
  apply WP.mono (finalSave_ok s hok)
  intro s₁ h₁
  obtain saved₁ := hsaved.congr h₁.bp h₁.frame
  obtain reads₁ : ∀ i < 4, InRegions (s₁.rd ++ s₁.wr) (addr32 (s₁.gpr .ebp) + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [h₁.rd, h₁.wr, h₁.bp]; exact hread
  apply WP.mono (blockRestore_ok original s₁ saved₁ (by rw [h₁.bp]; exact hok.fit) reads₁)
  intro s₂ h₂
  obtain sp₂ : s₂.gpr .esp = s.gpr .esp := h₂.sp.trans h₁.sp
  obtain ptr₂ : s₂.gpr .eax = s.gpr .ebp := h₂.ptr.trans h₁.bp
  obtain rd₂ : s₂.rd = s.rd := h₂.rd.trans h₁.rd
  obtain wr₂ : s₂.wr = s.wr := h₂.wr.trans h₁.wr
  obtain data₂ : dataArg s₂ = dataArg s := by
    unfold dataArg
    rw [sp₂, h₂.mem]
    exact h₁.frame.readW (r := ⟨wordAddr (s.gpr .esp) 2, 4⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hargSep) (by decide)
  obtain input₂ : finalWord s₂ = Spec.TripleDes.permute Spec.TripleDes.fp x := by
    unfold finalWord
    rw [ptr₂, h₂.mem]
    change (s₁.mem.readW (wordAddr (s.gpr .ebp) 7) 32 ++
      s₁.mem.readW (wordAddr (s.gpr .ebp) 6) 32 : BitVec 64) =
        Spec.TripleDes.permute Spec.TripleDes.fp x
    rw [h₁.hi, h₁.lo, VG.Proof.TripleDes.halves_append, hword.left, hword.right,
      VG.Proof.TripleDes.halves_append]
  obtain reads₂ : ∀ k ∈ [24, 28], InRegions (s₂.rd ++ s₂.wr) (addr (s₂.gpr .eax) k) 4 := by
    intro k hk
    rw [rd₂, wr₂, ptr₂]
    obtain hwk : InRegions s.wr (addr (s.gpr .ebp) k) 4 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact hok.slotIn 6 (by decide)
      · exact hok.slotIn 7 (by decide)
    obtain ⟨r, hr, hc⟩ := hwk
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain arg₂ : InRegions (s₂.rd ++ s₂.wr) (wordAddr (s₂.gpr .esp) 2) 4 := by
    rw [rd₂, wr₂, sp₂]; exact harg
  obtain writes₂ : ∀ i < 2, InRegions s₂.wr (wordAddr (dataArg s₂) i) 4 := by
    rw [wr₂, data₂]; exact hw
  obtain ⟨s₃, run₃, mem₃, rd₃, wr₃, regs₃⟩ := restoredOutput_ok s₂
    (by rw [data₂]; exact dataFit) arg₂ reads₂ writes₂
  obtain hm : s₃.mem = s₁.mem.writeW (addr32 (dataArg s))
      (byteRev64 (Spec.TripleDes.permute Spec.TripleDes.fp x)) := by
    rw [mem₃, data₂, input₂, h₂.mem]
  refine WP.of_runBlock ⟨s₃, run₃, ⟨?_, ?_, rd₃.trans rd₂, wr₃.trans wr₂,
    (regs₃ .esp (by decide) (by decide) (by decide)).trans sp₂, ?_⟩⟩
  · rw [hm]
    exact blockAt_writeW _ _ _
  · intro r hr
    obtain neq : ∀ r ∈ savedRegs, r ≠ .eax ∧ r ≠ .ecx ∧ r ≠ .edx := by decide
    exact (regs₃ r (neq r hr).1 (neq r hr).2.1 (neq r hr).2.2).trans (h₂.saved r hr)
  · rw [hm]
    exact (h₁.frame.mono (by intro r hr; obtain rfl := List.mem_singleton.mp hr; simp)).writeW
      (List.mem_cons_self) _ (Region.contains_self _ _)

end VG.Proof.TripleDes.X86

end

/-! ## `Block` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Spec.TripleDes (Direction Schedule)
open VG.Proof.Rc2.X86 (addr32)

def blockResult (keys : Schedule) (d : Direction) (b : Spec.TripleDes.Block) : Spec.TripleDes.Block :=
  match d with
  | .encrypt => Spec.TripleDes.encryptBlock keys b
  | .decrypt => Spec.TripleDes.decryptBlock keys b

theorem blockResult_core (keys : Schedule) (d : Direction) (b : Spec.TripleDes.Block) :
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp
      (blockCore (Spec.TripleDes.componentSchedule keys) d
        (Spec.TripleDes.permute Spec.TripleDes.ip (Spec.TripleDes.decodeBlock b)))) = blockResult keys d b := by
  cases d
  · exact (VG.Proof.TripleDes.encryptBlock_eq_cores keys b).symm
  · exact (VG.Proof.TripleDes.decryptBlock_eq_cores keys b).symm

def blockRegions (s : State) : List Region :=
  [⟨addr32 (dataArg s), 8⟩, ⟨addr32 (scratchArg s 3), 512⟩]

structure BlockPost (keys : Schedule) (d : Direction) (original s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (addr32 (dataArg original)) =
    blockResult keys d (Spec.TripleDes.blockAt original.mem (addr32 (dataArg original)))
  saved : ∀ r ∈ savedRegs, s.gpr r = original.gpr r
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  sp : s.gpr .esp = original.gpr .esp
  frame : Frame (blockRegions original) original.mem s.mem

theorem block_ok (keys : Schedule) (base : BitVec 32) (d : Direction) (s : State)
    (hp : HeadPre (Spec.TripleDes.componentSchedule keys) base s)
    (hread : ∀ i < 4, InRegions (s.rd ++ s.wr) (addr32 (scratchArg s 3) + BitVec.ofNat 64 (4 * i)) 4)
    (hwrite : ∀ i < 2, InRegions s.wr (wordAddr (dataArg s) i) 4)
    (hargSep : (⟨wordAddr (s.gpr .esp) 2, 4⟩ : Region).Disjoint (workRegion (prepared s))) :
    WP isa (block d) s (BlockPost keys d s) := by
  rw [block]
  apply WP.seq
  apply WP.mono (blockHead_ok (Spec.TripleDes.componentSchedule keys) base s hp)
  intro s₁ h₁
  apply WP.seq
  apply WP.mono (blockBody_ok (Spec.TripleDes.componentSchedule keys) base s₁ _ d h₁.ready h₁.word)
  intro s₂ h₂
  have stable := h₂.2.2
  obtain bp₂ : s₂.gpr .ebp = scratchArg s 3 := stable.bp.trans h₁.bp
  obtain sp₂ : s₂.gpr .esp = s.gpr .esp := stable.sp.trans h₁.sp
  obtain work₁ : workRegion s₁ = workRegion (prepared s) := by
    unfold workRegion prepared
    rw [h₁.bp, VG.X86.RegUpd.gpr_setReg_self]
  obtain data₂ : dataArg s₂ = dataArg s := by
    unfold dataArg
    rw [stable.sp]
    obtain sep : (⟨wordAddr (s₁.gpr .esp) 2, 4⟩ : Region).Disjoint (workRegion s₁) := by
      rw [h₁.sp, work₁]
      exact hargSep
    obtain hm := stable.frame.readW (a := wordAddr (s₁.gpr .esp) 2) (w := 32)
      (r := ⟨wordAddr (s₁.gpr .esp) 2, 4⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact sep) (by decide)
    exact hm.trans h₁.data
  obtain saved₂ := h₁.saved.congr stable.bp stable.frame
  obtain reads₂ : ∀ i < 4, InRegions (s₂.rd ++ s₂.wr) (addr32 (s₂.gpr .ebp) + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [stable.rd, stable.wr, h₁.rd, h₁.wr, bp₂]; exact hread
  obtain writes₂ : ∀ i < 2, InRegions s₂.wr (wordAddr (dataArg s₂) i) 4 := by
    rw [stable.wr, h₁.wr, data₂]; exact hwrite
  obtain arg₂ : InRegions (s₂.rd ++ s₂.wr) (wordAddr (s₂.gpr .esp) 2) 4 := by
    rw [stable.rd, stable.wr, h₁.rd, h₁.wr, sp₂]; exact hp.argRead 2 (by decide)
  obtain work₂ : workRegion s₂ = workRegion (prepared s) := by
    unfold workRegion prepared
    rw [bp₂, VG.X86.RegUpd.gpr_setReg_self]
  apply WP.mono (blockTailRestored_ok s s₂ _ h₂.1 saved₂ h₂.2.1.spills
    (by rw [data₂]; exact hp.dataFit) arg₂
    (by rw [sp₂, work₂]; exact hargSep) writes₂ reads₂)
  intro s₃ h₃
  refine ⟨?_, h₃.saved, h₃.rd.trans (stable.rd.trans h₁.rd), h₃.wr.trans (stable.wr.trans h₁.wr),
    h₃.sp.trans sp₂, ?_⟩
  · have hr := h₃.result
    rw [data₂] at hr
    exact hr.trans (blockResult_core keys d _)
  · have hf₁ : Frame (blockRegions s) s.mem s₁.mem := h₁.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨⟨addr32 (scratchArg s 3), 512⟩, by simp [blockRegions], Region.sub_prefix (by decide)⟩)
    obtain hf₂ : Frame (blockRegions s) s₁.mem s₂.mem := stable.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨⟨addr32 (scratchArg s 3), 512⟩, by simp [blockRegions], ?_⟩
      unfold workRegion
      rw [h₁.bp]
      exact Offset.sub_base _ (by decide))
    obtain hf₃ : Frame (blockRegions s) s₂.mem s₃.mem := h₃.frame.sub (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [data₂]
        exact ⟨⟨addr32 (dataArg s), 8⟩, by simp [blockRegions], fun _ h => h⟩
      · refine ⟨⟨addr32 (scratchArg s 3), 512⟩, by simp [blockRegions], ?_⟩
        unfold workRegion
        rw [bp₂]
        exact Offset.sub_base _ (by decide))
    exact hf₁.trans (hf₂.trans hf₃)

end VG.Proof.TripleDes.X86

end

/-! ## `Contract` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)
open VG.Spec.TripleDes (Direction)

/-- The IA-32 calling convention and memory layout used by the block proof. -/
def blockContract (d : Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨addr32 (arg s 0), 384⟩
    let data : Region := ⟨addr32 (arg s 1), 8⟩
    let scratch : Region := ⟨addr32 (arg s 2), 512⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨addr32 (s.gpr .esp), 4⟩
    s.rd = [key, args] ∧ s.wr = [data, scratch] ∧ key.Disjoint scratch ∧ data.Disjoint scratch ∧
      args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 384 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 8 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 512 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  post s s' := Spec.TripleDes.blockAt s'.mem (addr32 (arg s 1)) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (addr32 (arg s 0))) d
      (Spec.TripleDes.blockAt s.mem (addr32 (arg s 1)))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 3, arg s₁ i = arg s₂ i

end VG.Proof.TripleDes.X86

end

/-! ## `ScheduleMemory` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight
open VG.Spec.TripleDes (Direction)
open VG.Proof.Rc2.X86 (addr32)
def selectedRound (d : Direction) (j : Nat) : Nat := if d = .encrypt then j else 15 - j

theorem selectedRound_bound (d : Direction) (j : Nat) (hj : j < 16) : selectedRound d j < 16 := by
  cases d <;> simp only [selectedRound, reduceCtorEq, ite_true, ite_false] <;> omega_arith

theorem keyAddr_component (base : BitVec 32) (c : Nat) (d : Direction) (j : Nat) :
    keyAddr (componentBase base c) d j = base + BitVec.ofNat 32 (8 * (16 * c + selectedRound d j)) := by
  unfold keyAddr componentBase selectedRound
  rw [Offset.add_ofNat_add_ofNat]
  exact congrArg (fun n => base + BitVec.ofNat 32 n) (by omega_using [])

theorem keyWordAddress (base : BitVec 32) (fit : base.toNat + 384 ≤ 2 ^ 32)
    (c j t : Nat) (hc : c < 3) (hj : j < 16) (ht : t < 2) (d : Direction) :
    wordAddr (keyAddr (componentBase base c) d j) t =
      addr32 base + BitVec.ofNat 64 (8 * (16 * c + selectedRound d j) + 4 * t) := by
  obtain bound := selectedRound_bound d j hj
  rw [wordAddr, keyAddr_component]
  unfold addr
  rw [Offset.add_ofNat_add_ofNat]
  exact VG.Proof.Rc2.X86.addr_add (by omega_using [fit, hc, ht, bound])

theorem readKey_component (m : Mem) (base : BitVec 32)
    (fit : base.toNat + 384 ≤ 2 ^ 32) (c j : Nat) (hc : c < 3) (hj : j < 16) (d : Direction) :
    readKey m (keyAddr (componentBase base c) d j) =
      m.readW (addr32 base + BitVec.ofNat 64 (8 * (16 * c + selectedRound d j))) 64 := by
  rw [readKey, keyWordAddress base fit c j 1 hc hj (by decide) d,
    keyWordAddress base fit c j 0 hc hj (by decide) d]
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one]
  rw [← Offset.add_ofNat_add_ofNat]
  exact readW_pair m _

theorem ready_of_regions (s : State) (base : BitVec 32) (hok : Ok sboxCfg s)
    (hb : scheduleArg s = base) (fit : base.toNat + 384 ≤ 2 ^ 32)
    (hread : ∀ p, (⟨addr32 base, 384⟩ : Region).Contains p 4 → InRegions (s.rd ++ s.wr) p 4)
    (hdis : (⟨addr32 base, 384⟩ : Region).Disjoint ⟨addr32 (s.gpr .ebp), 512⟩)
    (harg : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 1) 4)
    (hargSep : (⟨wordAddr (s.gpr .esp) 1, 4⟩ : Region).Disjoint (workRegion s)) :
    Ready (Spec.TripleDes.componentSchedule (Spec.TripleDes.scheduleAt s.mem (addr32 base))) base s := by
  obtain workSub : Region.Sub (workRegion s) ⟨addr32 (s.gpr .ebp), 512⟩ :=
    Offset.sub_base _ (by decide)
  obtain keySub : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
      Region.Sub ⟨wordAddr (keyAddr (componentBase base c) d j) t, 4⟩ ⟨addr32 base, 384⟩ := by
    intro c hc d j hj t ht
    rw [keyWordAddress base fit c j t hc hj ht d]
    obtain bound := selectedRound_bound d j hj
    exact Offset.sub_base _ (by omega_using [hc, ht, bound])
  refine ⟨hok, hb, harg, hargSep, ?_, ?_, ?_, ?_⟩
  · intro c hc d j hj t ht
    apply hread
    rw [keyWordAddress base fit c j t hc hj ht d]
    obtain bound := selectedRound_bound d j hj
    exact Offset.contains_base _ (by omega_using [hc, ht, bound]) (by omega_using [hc, ht, bound])
  · intro c hc d j hj t ht
    exact (hdis.sub_left (keySub c hc d j hj t ht)).sub_right workSub
  · intro c hc d j hj k hk t ht
    have scratchFit : (s.gpr .ebp).toNat + 512 ≤ 2 ^ 32 := hok.fit
    apply hdis.symm.sep
    · rw [wordAddr, addr_eq (by omega_using [hk, scratchFit])]
      exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])
    · rw [keyWordAddress base fit c j t hc hj ht d]
      obtain bound := selectedRound_bound d j hj
      exact Offset.contains_base _ (by omega_using [hc, ht, bound]) (by omega_using [hc, ht, bound])
  · intro c hc d j hj
    rw [readKey_component s.mem base fit c j hc hj d]
    exact (VG.Proof.TripleDes.componentSchedule_readW s.mem (addr32 base) c
      (selectedRound d j) hc (selectedRound_bound d j hj)).symm

end VG.Proof.TripleDes.X86

end

/-! ## `Pre` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight
open VG.Proof.Rc2.X86 (addr32 argContainsCount)
open VG.Spec.TripleDes (Direction)

theorem argument_word (s : State) (i : Nat) : arg s i = s.mem.readW (wordAddr (s.gpr .esp) (i + 1)) 32 := by
  unfold arg argAddr
  apply congrArg (fun p => s.mem.readW p 32)
  change addr (s.gpr .esp) (4 + 4 * i) = addr (s.gpr .esp) (4 * (i + 1))
  exact congrArg (addr (s.gpr .esp)) (by omega_using [])

theorem data_argument (s : State) : dataArg s = arg s 1 := (argument_word s 1).symm

theorem scratch_argument (s : State) : scratchArg s 3 = arg s 2 := (argument_word s 2).symm

theorem headPre_of_contract (d : Direction) (s : State) (hs : (blockContract d).pre s) :
    HeadPre (Spec.TripleDes.componentSchedule (Spec.TripleDes.scheduleAt s.mem (addr32 (arg s 0))))
      (arg s 0) s := by
  obtain ⟨hrd, hwr, keySep, dataSep, argsData, argsScratch, _, _, keyFit, dataFit, scratchFit, spFit⟩ := hs
  obtain bp : (prepared s).gpr .ebp = arg s 2 := by rw [prepared, gpr_setReg_self, scratch_argument]
  obtain sp : (prepared s).gpr .esp = s.gpr .esp := gpr_setReg_of_ne s _ (by decide)
  obtain saveSub : Region.Sub (saveRegion s) ⟨addr32 (arg s 2), 512⟩ := by
    rw [saveRegion, scratch_argument]
    exact Region.sub_prefix (by decide)
  obtain workSub : Region.Sub (workRegion (prepared s)) ⟨addr32 (arg s 2), 512⟩ := by
    rw [workRegion, bp]
    exact Offset.sub_base _ (by decide)
  obtain argContains : ∀ i ∈ [1, 2, 3], (⟨argAddr s 0, 12⟩ : Region).Contains
      (wordAddr (s.gpr .esp) i) 4 := by
    intro i hi
    obtain hb : 1 ≤ i ∧ i ≤ 3 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    rw [wordAddr, addr_eq (by omega_using [spFit, hb])]
    obtain h := argContainsCount s 3 spFit (i - 1) (by omega_using [hb])
    rw [show 4 + 4 * (i - 1) = 4 * i by omega_using [hb]] at h
    exact h
  obtain argSub : ∀ i ∈ [1, 2, 3], Region.Sub ⟨wordAddr (s.gpr .esp) i, 4⟩ ⟨argAddr s 0, 12⟩ := by
    intro i hi a ha
    exact (argContains i hi).byte (by change (a - wordAddr (s.gpr .esp) i).toNat + 1 ≤ 4 at ha; omega_using [ha])
  obtain argRead : ∀ i ∈ [1, 2, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4 := by
    intro i hi
    rw [hrd, hwr]
    exact ⟨⟨argAddr s 0, 12⟩, by simp, argContains i hi⟩
  obtain slots : ∀ i < 128, InRegions (prepared s).wr (wordAddr ((prepared s).gpr .ebp) i) 4 := by
    intro i hi
    rw [bp, wordAddr, addr_eq (by omega_using [scratchFit, hi])]
    change InRegions s.wr _ 4
    rw [hwr]
    exact ⟨⟨addr32 (arg s 2), 512⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  obtain hok : Ok sboxCfg (prepared s) := by
    refine ⟨slots, ?_, ?_, ?_⟩
    · intro k hk; change k < 0 at hk; omega
    · change ((prepared s).gpr .ebp).toNat + 512 ≤ 2 ^ 32
      rw [bp]; exact scratchFit
    · intro k hk j hj; change j < 0 at hj; omega
  obtain hb : scheduleArg (prepared s) = arg s 0 := by
    unfold scheduleArg
    rw [sp]
    exact (argument_word s 0).symm
  obtain ready := ready_of_regions (prepared s) (arg s 0) hok hb keyFit
    (by intro p hp
        change InRegions (s.rd ++ s.wr) p 4
        rw [hrd, hwr]
        exact ⟨⟨addr32 (arg s 0), 384⟩, by simp, hp⟩)
    (by rw [bp]; exact keySep)
    (by change InRegions (s.rd ++ s.wr) (wordAddr ((prepared s).gpr .esp) 1) 4
        rw [sp]; exact argRead 1 (by decide))
    (by rw [sp]; exact (argsScratch.sub_left (argSub 1 (by decide))).sub_right workSub)
  refine ⟨ready, ?_, ?_, ?_, argRead, ?_, ?_, dataSep.sub_right saveSub, ?_⟩
  · rw [scratch_argument]; exact scratchFit
  · rw [data_argument]; exact dataFit
  · intro i hi
    rw [scratch_argument, hwr]
    exact ⟨⟨addr32 (arg s 2), 512⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  · intro i hi
    exact (argsScratch.sub_left (argSub i hi)).sub_right saveSub
  · intro i hi
    rw [data_argument, wordAddr, addr_eq (by omega_using [dataFit, hi]), hrd, hwr]
    exact ⟨⟨addr32 (arg s 1), 8⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  · intro c hc direction j hj t ht
    obtain keySub : Region.Sub ⟨wordAddr (keyAddr (componentBase (arg s 0) c) direction j) t, 4⟩
        ⟨addr32 (arg s 0), 384⟩ := by
      rw [keyWordAddress _ keyFit c j t hc hj ht direction]
      obtain bound := selectedRound_bound direction j hj
      exact Offset.sub_base _ (by omega_using [hc, ht, bound])
    exact (keySep.sub_left keySub).sub_right saveSub

end VG.Proof.TripleDes.X86

end

/-! ## `CorrectBlock` -/

section

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32 argContainsCount)
open VG.Spec.TripleDes (Direction)

theorem block_correct (d : Direction) (s : State) (hs : (blockContract d).pre s) :
    WP isa (block d) s (fun s' => abiPreserved s s' ∧ (blockContract d).post s s') := by
  obtain hp := headPre_of_contract d s hs
  obtain ⟨_, hwr, _, _, _, argsScratch, retData, retScratch, _, dataFit, _, spFit⟩ := hs
  obtain hwrite : ∀ i < 2, InRegions s.wr (wordAddr (dataArg s) i) 4 := by
    intro i hi
    rw [data_argument, wordAddr, addr_eq (by omega_using [dataFit, hi]), hwr]
    exact ⟨⟨addr32 (arg s 1), 8⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  obtain hread : ∀ i < 4, InRegions (s.rd ++ s.wr) (addr32 (scratchArg s 3) + BitVec.ofNat 64 (4 * i)) 4 := by
    intro i hi
    obtain ⟨r, hr, hc⟩ := hp.saveWrite i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain hargSep : (⟨wordAddr (s.gpr .esp) 2, 4⟩ : Region).Disjoint (workRegion (prepared s)) := by
    obtain sub : Region.Sub ⟨wordAddr (s.gpr .esp) 2, 4⟩ ⟨argAddr s 0, 12⟩ := by
      rw [wordAddr, addr_eq (by omega_using [spFit]), VG.Proof.Rc2.X86.argAddr_eq s 0 (by omega_using [spFit])]
      exact Offset.sub _ (by decide) (by decide)
    obtain workSub : Region.Sub (workRegion (prepared s)) ⟨addr32 (arg s 2), 512⟩ := by
      unfold workRegion prepared
      rw [VG.X86.RegUpd.gpr_setReg_self, scratch_argument]
      exact Offset.sub_base _ (by decide)
    exact (argsScratch.sub_left sub).sub_right workSub
  apply WP.mono (block_ok (Spec.TripleDes.scheduleAt s.mem (addr32 (arg s 0)))
    (arg s 0) d s hp hread hwrite hargSep)
  intro s' hpost
  refine ⟨⟨?_, ?_⟩, hpost.result⟩
  · intro r hr
    obtain hregs : ∀ r ∈ calleeSaved, r ∈ savedRegs ∨ r = .esp := by decide
    rcases hregs r hr with h | rfl
    · exact hpost.saved r h
    · exact hpost.sp
  · apply hpost.frame.readW (r := ⟨addr32 (s.gpr .esp), 4⟩) (Region.contains_self _ _) _ (by decide)
    intro r hr
    simp only [blockRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact retData
    · exact retScratch

end VG.Proof.TripleDes.X86

end

end

end

/-! ## `EncryptBlock` -/

section

/-! # The encryption block: CMAC's block on the block's two words

`vg_triple_des_encrypt_block` saves the caller's registers in the working
space, runs CMAC's block (`Proof.CmacTripleDes.X86.block_ok`) on the block's
words as big-endian integers, restores the registers and stores the result:
the block function's contract, as the decryption block's. -/

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Wp VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32 argContainsCount)
open VG.Spec.TripleDes (Direction)

/-- The encryption block's instructions before CMAC's block. -/
theorem encHead_eq : encSave ++ encLoad =
    ([.mov .eax (.mem ⟨.esp, 12⟩), .store ⟨.eax, 128⟩ .ebp, .store ⟨.eax, 132⟩ .ebx,
      .store ⟨.eax, 136⟩ .esi, .store ⟨.eax, 140⟩ .edi, .mov .ebp (.reg .eax),
      .mov .ecx (.mem ⟨.esp, 8⟩), .mov .eax (.mem ⟨.ecx, 0⟩), .mov .edx (.mem ⟨.ecx, 4⟩),
      .bswap .eax, .bswap .edx, .mov .esi (.mem ⟨.esp, 4⟩)] : List Instr) := rfl

/-- The encryption block's instructions after it. -/
theorem encStore_eq : encStore =
    ([.bswap .eax, .bswap .edx, .mov .ecx (.reg .ebp), .mov .ebx (.mem ⟨.ecx, 132⟩),
      .mov .esi (.mem ⟨.ecx, 136⟩), .mov .edi (.mem ⟨.ecx, 140⟩), .mov .ebp (.mem ⟨.ecx, 128⟩),
      .mov .ecx (.mem ⟨.esp, 8⟩), .store ⟨.ecx, 0⟩ .eax, .store ⟨.ecx, 4⟩ .edx] : List Instr) := rfl

/-- `vg_triple_des_encrypt_block`: CMAC's block on the block's two words. -/
theorem encBlock_correct (s : State) (hs : (blockContract .encrypt).pre s) :
    WP isa encryptBlock s (fun s' => abiPreserved s s' ∧ (blockContract .encrypt).post s s') := by
  obtain ⟨hrd, hwr, keySep, dataSep, argsData, argsScratch, retData, retScratch, keyFit, dataFit,
    scratchFit, spFit⟩ := hs
  -- The arguments' words, the scratch buffer's and the block's.
  obtain argC : ∀ i < 3, (⟨argAddr s 0, 12⟩ : Region).Contains (addr (s.gpr .esp) (4 + 4 * i)) 4 := fun i hi => by
    rw [addr_eq (by omega_using [spFit, hi])]
    exact argContainsCount s 3 (by omega_using [spFit]) i hi
  obtain argIn : ∀ i < 3, InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (4 + 4 * i)) 4 := fun i hi => by
    rw [hrd]; exact ⟨_, by simp, argC i hi⟩
  obtain scrC : ∀ k, k + 4 ≤ 512 → (⟨addr32 (arg s 2), 512⟩ : Region).Contains (addr (arg s 2) k) 4 := fun k hk => by
    rw [addr_eq (by omega_using [scratchFit, hk])]
    exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])
  obtain scrW : ∀ k, k + 4 ≤ 512 → InRegions s.wr (addr (arg s 2) k) 4 := fun k hk => by
    rw [hwr]; exact ⟨_, by simp, scrC k hk⟩
  obtain datC : ∀ k, k + 4 ≤ 8 → (⟨addr32 (arg s 1), 8⟩ : Region).Contains (addr (arg s 1) k) 4 := fun k hk => by
    rw [addr_eq (by omega_using [dataFit, hk])]
    exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])
  obtain datW : ∀ k, k + 4 ≤ 8 → InRegions s.wr (addr (arg s 1) k) 4 := fun k hk => by
    rw [hwr]; exact ⟨_, by simp, datC k hk⟩
  -- Reading an argument, the block or the schedule after writes to the scratch buffer.
  obtain argRd : ∀ {m : Mem}, Frame [⟨addr32 (arg s 2), 512⟩] s.mem m → ∀ i < 3,
      m.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 = arg s i := fun fr i hi =>
    fr.readW (argC i hi) (fun r hr => by rw [List.mem_singleton.mp hr]; exact argsScratch) (by decide)
  obtain datRd : ∀ {m : Mem}, Frame [⟨addr32 (arg s 2), 512⟩] s.mem m → ∀ k, k + 4 ≤ 8 →
      m.readW (addr (arg s 1) k) 32 = s.mem.readW (addr (arg s 1) k) 32 := fun fr k hk =>
    fr.readW (datC k hk) (fun r hr => by rw [List.mem_singleton.mp hr]; exact dataSep) (by decide)
  unfold encryptBlock
  refine WP.seq ?_
  rw [encHead_eq]
  -- The working space's address, and the registers saved in it.
  refine wp_ldm (B := s.gpr .esp) rfl (argIn 2 (by decide)) fun s₁ u₁ => ?_
  obtain a₁ : s₁.gpr .eax = arg s 2 := u₁.gpr
  refine wp_stm (B := arg s 2) a₁ (by rw [u₁.wr]; exact scrW 128 (by decide)) fun s₂ u₂ => ?_
  refine wp_stm (B := arg s 2) (by rw [u₂.gpr]; exact a₁) (by rw [u₂.wr, u₁.wr]; exact scrW 132 (by decide))
    fun s₃ u₃ => ?_
  refine wp_stm (B := arg s 2) (by rw [u₃.gpr, u₂.gpr]; exact a₁)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact scrW 136 (by decide)) fun s₄ u₄ => ?_
  refine wp_stm (B := arg s 2) (by rw [u₄.gpr, u₃.gpr, u₂.gpr]; exact a₁)
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact scrW 140 (by decide)) fun s₅ u₅ => ?_
  obtain g₅ : ∀ r, r ≠ .eax → s₅.gpr r = s.gpr r := fun r hr => by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other r hr]
  obtain m₅ : s₅.mem = (((s.mem.writeW (addr (arg s 2) 128) (s.gpr .ebp)).writeW (addr (arg s 2) 132)
      (s.gpr .ebx)).writeW (addr (arg s 2) 136) (s.gpr .esi)).writeW (addr (arg s 2) 140) (s.gpr .edi) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other .ebp (by decide),
      u₁.other .ebx (by decide), u₁.other .esi (by decide), u₁.other .edi (by decide)]
  obtain f₅ : Frame [⟨addr32 (arg s 2), 512⟩] s.mem s₅.mem := by
    rw [m₅]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (scrC 128 (by decide))).writeW
      (List.mem_singleton_self _) _ (scrC 132 (by decide))).writeW (List.mem_singleton_self _) _
      (scrC 136 (by decide))).writeW (List.mem_singleton_self _) _ (scrC 140 (by decide))
  obtain rd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine wp_mov fun s₆ u₆ => ?_
  -- The block's words and the schedule's address.
  refine wp_ldm (B := s.gpr .esp) (by rw [u₆.other _ (by decide), g₅ _ (by decide)])
    (by rw [u₆.rd, u₆.wr, rd₅, wr₅]; exact argIn 1 (by decide)) fun s₇ u₇ => ?_
  obtain c₇ : s₇.gpr .ecx = arg s 1 := by rw [u₇.gpr, u₆.mem]; exact argRd f₅ 1 (by decide)
  obtain datIn : ∀ k, k + 4 ≤ 8 → InRegions (s.rd ++ s.wr) (addr (arg s 1) k) 4 := fun k hk => by
    obtain ⟨r, hr, hc⟩ := datW k hk
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine wp_ldm (B := arg s 1) c₇ (by rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr, rd₅, wr₅]; exact datIn 0 (by decide))
    fun s₈ u₈ => ?_
  refine wp_ldm (B := arg s 1) (by rw [u₈.other _ (by decide)]; exact c₇)
    (by rw [u₈.rd, u₈.wr, u₇.rd, u₇.wr, u₆.rd, u₆.wr, rd₅, wr₅]; exact datIn 4 (by decide)) fun s₉ u₉ => ?_
  refine wp_bswap fun s₁₀ u₁₀ => wp_bswap fun s₁₁ u₁₁ => ?_
  obtain m₁₁ : s₁₁.mem = s₅.mem := by rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  obtain rd₁₁ : s₁₁.rd = s.rd := by rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅]
  obtain wr₁₁ : s₁₁.wr = s.wr := by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅]
  obtain sp₁₁ : s₁₁.gpr .esp = s.gpr .esp := by
    rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), g₅ _ (by decide)]
  refine wp_ldm (B := s.gpr .esp) sp₁₁ (by rw [rd₁₁, wr₁₁]; exact argIn 0 (by decide)) fun t ut => WP.block_nil ?_
  -- The state CMAC's block starts from.
  obtain tm : t.mem = s₅.mem := by rw [ut.mem, m₁₁]
  obtain trd : t.rd = s.rd := by rw [ut.rd, rd₁₁]
  obtain twr : t.wr = s.wr := by rw [ut.wr, wr₁₁]
  obtain tsp : t.gpr .esp = s.gpr .esp := by rw [ut.other _ (by decide), sp₁₁]
  obtain tsi : t.gpr .esi = arg s 0 := by rw [ut.gpr, m₁₁]; exact argRd f₅ 0 (by decide)
  obtain tbp : t.gpr .ebp = arg s 2 := by
    rw [ut.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, a₁]
  obtain tax : t.gpr .eax = bswap (s.mem.readW (addr (arg s 1) 0) 32) := by
    rw [ut.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide), u₈.gpr, u₇.mem,
      u₆.mem]
    exact congrArg bswap (datRd f₅ 0 (by decide))
  obtain tdx : t.gpr .edx = bswap (s.mem.readW (addr (arg s 1) 4) 32) := by
    rw [ut.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide), u₉.gpr, u₈.mem, u₇.mem, u₆.mem]
    exact congrArg bswap (datRd f₅ 4 (by decide))
  obtain hp : Proof.CmacTripleDes.X86.BlockPre t :=
    ⟨⟨384, by rw [trd, twr, hrd, tsi]; exact List.mem_append_left _ List.mem_cons_self, Nat.le_refl _,
        by rw [tsi]; exact keyFit⟩,
      ⟨512, by rw [twr, hwr, tbp]; exact List.mem_cons_of_mem _ List.mem_cons_self, by decide,
        by rw [tbp]; exact scratchFit⟩,
      by rw [tbp, tsi]; exact (keySep.sub_right (Region.sub_prefix (by decide))).symm⟩
  refine WP.seq (WP.mono (Proof.CmacTripleDes.X86.block_ok hp) fun u ⟨same, usi, uval⟩ => ?_)
  -- The schedule and the block it was run on.
  obtain ksch : Proof.CmacTripleDes.X86.sch t = Spec.TripleDes.scheduleAt s.mem (addr32 (arg s 0)) := by
    rw [Proof.CmacTripleDes.X86.sch, tsi, tm]
    exact VG.Proof.TripleDes.scheduleAt_eq_of_frame _ f₅
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact keySep)
  obtain a0 : addr (arg s 1) 0 = addr32 (arg s 1) := by
    rw [addr_eq (by omega_using [dataFit])]; exact BitVec.add_zero _
  obtain a4 : addr (arg s 1) 4 = addr32 (arg s 1) + 4 := addr_eq (by omega_using [dataFit])
  obtain xin : t.gpr .eax ++ t.gpr .edx =
      Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (addr32 (arg s 1))) := by
    rw [tax, tdx, a0, a4, decodeBlock_readW]
  -- The frame so far: the scratch buffer.
  obtain fu : Frame [⟨addr32 (arg s 2), 512⟩] s.mem u.mem := by
    refine f₅.trans (by
      rw [← tm]
      exact same.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr, Proof.CmacTripleDes.X86.xR, tbp]; exact Region.sub_prefix (by decide)⟩)
  obtain ubp : u.gpr .ebp = arg s 2 := same.ebp.trans tbp
  obtain usp : u.gpr .esp = s.gpr .esp := same.esp.trans tsp
  obtain urd : u.rd = s.rd := same.rd.trans trd
  obtain uwr : u.wr = s.wr := same.wr.trans twr
  -- The saved registers' words, which CMAC's block does not write.
  obtain svd : ∀ k v, (k = 128 ∨ k = 132 ∨ k = 136 ∨ k = 140) → s₅.mem.readW (addr (arg s 2) k) 32 = v →
      u.mem.readW (addr (arg s 2) k) 32 = v := fun k v hk hv => by
    rw [← hv, ← tm]
    refine same.frame.readW (r := ⟨addr (arg s 2) k, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    rw [List.mem_singleton.mp hr, Proof.CmacTripleDes.X86.xR, tbp, addr_eq (by omega_using [scratchFit, hk])]
    exact Offset.disjoint_base _ (by omega_using [hk]) (by omega_using [hk])
  -- Reading a word of the scratch buffer after a write of another.
  obtain rdw : ∀ (m : Mem) (j k : Nat) (v : BitVec 32), j + 4 ≤ k ∨ k + 4 ≤ j → j + 4 ≤ 512 → k + 4 ≤ 512 →
      (m.writeW (addr (arg s 2) k) v).readW (addr (arg s 2) j) 32 = m.readW (addr (arg s 2) j) 32 :=
    fun m j k v h hj hk => by
      rw [addr_eq (k := j) (by omega_using [scratchFit, hj]), addr_eq (k := k) (by omega_using [scratchFit, hk])]
      exact Mem.readW_writeW_sep (Offset.sep _ h (by omega_using [hj]) (by omega_using [hk])) (by decide)
  obtain sv0 : u.mem.readW (addr (arg s 2) 128) 32 = s.gpr .ebp := svd 128 _ (by decide) (by
    rw [m₅, rdw _ _ _ _ (by decide) (by decide) (by decide), rdw _ _ _ _ (by decide) (by decide) (by decide),
      rdw _ _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32])
  obtain sv1 : u.mem.readW (addr (arg s 2) 132) 32 = s.gpr .ebx := svd 132 _ (by decide) (by
    rw [m₅, rdw _ _ _ _ (by decide) (by decide) (by decide), rdw _ _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32])
  obtain sv2 : u.mem.readW (addr (arg s 2) 136) 32 = s.gpr .esi := svd 136 _ (by decide) (by
    rw [m₅, rdw _ _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32])
  obtain sv3 : u.mem.readW (addr (arg s 2) 140) 32 = s.gpr .edi := svd 140 _ (by decide) (by
    rw [m₅, Mem.readW_writeW_self32])
  obtain scrIn : ∀ k, k + 4 ≤ 512 → InRegions (s.rd ++ s.wr) (addr (arg s 2) k) 4 := fun k hk => by
    obtain ⟨r, hr, hc⟩ := scrW k hk
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [encStore_eq]
  refine wp_bswap fun v₁ w₁ => wp_bswap fun v₂ w₂ => wp_mov fun v₃ w₃ => ?_
  obtain c₃ : v₃.gpr .ecx = arg s 2 := by
    rw [w₃.gpr, w₂.other _ (by decide), w₁.other _ (by decide), ubp]
  obtain m₃ : v₃.mem = u.mem := by rw [w₃.mem, w₂.mem, w₁.mem]
  obtain rd₃ : v₃.rd = s.rd := by rw [w₃.rd, w₂.rd, w₁.rd, urd]
  obtain wr₃ : v₃.wr = s.wr := by rw [w₃.wr, w₂.wr, w₁.wr, uwr]
  refine wp_ldm (B := arg s 2) c₃ (by rw [rd₃, wr₃]; exact scrIn 132 (by decide)) fun v₄ w₄ => ?_
  refine wp_ldm (B := arg s 2) (by rw [w₄.other _ (by decide)]; exact c₃)
    (by rw [w₄.rd, w₄.wr, rd₃, wr₃]; exact scrIn 136 (by decide)) fun v₅ w₅ => ?_
  refine wp_ldm (B := arg s 2) (by rw [w₅.other _ (by decide), w₄.other _ (by decide)]; exact c₃)
    (by rw [w₅.rd, w₅.wr, w₄.rd, w₄.wr, rd₃, wr₃]; exact scrIn 140 (by decide)) fun v₆ w₆ => ?_
  refine wp_ldm (B := arg s 2)
    (by rw [w₆.other _ (by decide), w₅.other _ (by decide), w₄.other _ (by decide)]; exact c₃)
    (by rw [w₆.rd, w₆.wr, w₅.rd, w₅.wr, w₄.rd, w₄.wr, rd₃, wr₃]; exact scrIn 128 (by decide)) fun v₇ w₇ => ?_
  obtain m₇ : v₇.mem = u.mem := by rw [w₇.mem, w₆.mem, w₅.mem, w₄.mem, m₃]
  obtain rd₇ : v₇.rd = s.rd := by rw [w₇.rd, w₆.rd, w₅.rd, w₄.rd, rd₃]
  obtain wr₇ : v₇.wr = s.wr := by rw [w₇.wr, w₆.wr, w₅.wr, w₄.wr, wr₃]
  obtain sp₇ : v₇.gpr .esp = s.gpr .esp := by
    rw [w₇.other _ (by decide), w₆.other _ (by decide), w₅.other _ (by decide), w₄.other _ (by decide),
      w₃.other _ (by decide), w₂.other _ (by decide), w₁.other _ (by decide), usp]
  refine wp_ldm (B := s.gpr .esp) sp₇ (by rw [rd₇, wr₇]; exact argIn 1 (by decide)) fun v₈ w₈ => ?_
  obtain c₈ : v₈.gpr .ecx = arg s 1 := by rw [w₈.gpr, m₇]; exact argRd fu 1 (by decide)
  refine wp_stm (B := arg s 1) c₈ (by rw [w₈.wr, wr₇]; exact datW 0 (by decide)) fun v₉ w₉ => ?_
  refine wp_stm (B := arg s 1) (by rw [w₉.gpr]; exact c₈) (by rw [w₉.wr, w₈.wr, wr₇]; exact datW 4 (by decide))
    fun v₁₀ w₁₀ => WP.block_nil ?_
  -- The registers on return.
  obtain g : ∀ r, v₁₀.gpr r = v₈.gpr r := fun r => by rw [w₁₀.gpr, w₉.gpr]
  obtain ebx : v₁₀.gpr .ebx = s.gpr .ebx := by
    rw [g, w₈.other _ (by decide), w₇.other _ (by decide), w₆.other _ (by decide), w₅.other _ (by decide),
      w₄.gpr, m₃, sv1]
  obtain esi : v₁₀.gpr .esi = s.gpr .esi := by
    rw [g, w₈.other _ (by decide), w₇.other _ (by decide), w₆.other _ (by decide), w₅.gpr, w₄.mem, m₃, sv2]
  obtain edi : v₁₀.gpr .edi = s.gpr .edi := by
    rw [g, w₈.other _ (by decide), w₇.other _ (by decide), w₆.gpr, w₅.mem, w₄.mem, m₃, sv3]
  obtain ebp : v₁₀.gpr .ebp = s.gpr .ebp := by
    rw [g, w₈.other _ (by decide), w₇.gpr, w₆.mem, w₅.mem, w₄.mem, m₃, sv0]
  obtain esp : v₁₀.gpr .esp = s.gpr .esp := by rw [g, w₈.other _ (by decide), sp₇]
  -- The memory on return: the result over the block.
  obtain eax₈ : v₈.gpr .eax = bswap (u.gpr .eax) := by
    rw [w₈.other _ (by decide), w₇.other _ (by decide), w₆.other _ (by decide), w₅.other _ (by decide),
      w₄.other _ (by decide), w₃.other _ (by decide), w₂.other _ (by decide), w₁.gpr]
  obtain edx₈ : v₈.gpr .edx = bswap (u.gpr .edx) := by
    rw [w₈.other _ (by decide), w₇.other _ (by decide), w₆.other _ (by decide), w₅.other _ (by decide),
      w₄.other _ (by decide), w₃.other _ (by decide), w₂.gpr, w₁.other _ (by decide)]
  obtain mem : v₁₀.mem = u.mem.writeW (addr32 (arg s 1)) (byteRev64 (u.gpr .eax ++ u.gpr .edx)) := by
    rw [w₁₀.mem, w₉.mem, w₉.gpr, w₈.mem, m₇, eax₈, edx₈, a0, a4, writeW_pair, bswapPair]
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [ebx, esi, edi, ebp, esp]
  · rw [mem]
    refine (Mem.readW_writeW_sep ?_ (by decide)).trans (fu.readW (r := ⟨addr32 (s.gpr .esp), 4⟩)
      (Region.contains_self _ _) (fun r hr => by rw [List.mem_singleton.mp hr]; exact retScratch) (by decide))
    exact retData.sep (Region.contains_self _ _) (Region.contains_self _ _)
  · change Spec.TripleDes.blockAt v₁₀.mem (addr32 (arg s 1)) = Spec.TripleDes.encryptBlock _ _
    rw [mem, blockAt_writeW, uval, ksch, xin]
    rfl

end VG.Proof.TripleDes.X86

end

/-! ## `Call` -/

@[expose] public section

section

namespace VG.Proof.TripleDes.X86.Ecb

open VG VG.X86 VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32)
open VG.Proof.Rc2.X86.Cbc (callWithGpr)

def kept : List Reg := [.ebx, .esi, .edi, .ebp, .esp]

def blockCode (d : Spec.TripleDes.Direction) : Prog isa :=
  match d with | .encrypt => encryptBlock | .decrypt => decryptBlock

theorem block_nosp (d : Spec.TripleDes.Direction) : NoSp (blockCode d) := by
  apply NoSp.of_all
  cases d
  · change encryptBlock.allInstrs _ = true
    lit_decide
  · change decryptBlock.allInstrs _ = true
    lit_decide

theorem block_stack (d : Spec.TripleDes.Direction) : stackUse (blockCode d) = 0 := by
  cases d
  · change stackUse encryptBlock = 0
    lit_decide
  · simp only [blockCode, decryptBlock, block, blockBody, pass, stackUse, Nat.max_self]

/-- The block functions meet their contract: the encryption block is CMAC's,
the decryption block the bit-per-word one. -/
theorem blockCode_correct (d : Spec.TripleDes.Direction) (s : State) (hs : (blockContract d).pre s) :
    WP isa (blockCode d) s (fun s' => abiPreserved s s' ∧ (blockContract d).post s s') := by
  cases d
  · exact encBlock_correct s hs
  · exact block_correct .decrypt s hs

open VG.X86.Straight (wordAddr)
open VG.Proof.Rc2.X86 (argContainsCount)
open VG.Proof.TripleDes.Bitslice (blockOut)
open VG.Proof.TripleDes.X86.Bitsliced (BatchPre batch_wp)
open VG.Impl.TripleDes.X86.Bitslice (bufSlot encryptBatch decryptBatch batch)

/-- The bitsliced functions' contract: the working space, with the 32 blocks
from its word `bufSlot` on, and the schedule, as stack arguments. Each block
becomes its TDEA encryption or decryption, and the words of the working
space from 87 up to the blocks are kept. -/
def batchContract (d : Spec.TripleDes.Direction) : Contract isa where
  pre s :=
    let space : Region := ⟨addr32 (arg s 0), 784⟩
    let key : Region := ⟨addr32 (arg s 1), 384⟩
    let args : Region := ⟨argAddr s 0, 8⟩
    let ret : Region := ⟨addr32 (s.gpr .esp), 4⟩
    s.rd = [key, args] ∧ s.wr = [space] ∧ key.Disjoint space ∧ ret.Disjoint space ∧
      (arg s 0).toNat + 784 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 384 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 12 ≤ 2 ^ 32
  post s s' :=
    (∀ b < 32, Spec.TripleDes.blockAt s'.mem (wordAddr (arg s 0) (bufSlot + 2 * b)) =
      blockOut (Spec.TripleDes.scheduleAt s.mem (addr32 (arg s 1))) d
        (Spec.TripleDes.blockAt s.mem (wordAddr (arg s 0) (bufSlot + 2 * b)))) ∧
    ∀ k, 87 ≤ k → k < bufSlot →
      s'.mem.readW (wordAddr (arg s 0) k) 32 = s.mem.readW (wordAddr (arg s 0) k) 32
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 2, arg s₁ i = arg s₂ i

def batchCode (d : Spec.TripleDes.Direction) : Prog isa :=
  match d with | .encrypt => encryptBatch | .decrypt => decryptBatch

theorem batchCode_eq (d : Spec.TripleDes.Direction) : batchCode d = batch d := by cases d <;> rfl

theorem batch_nosp (d : Spec.TripleDes.Direction) : NoSp (batchCode d) := by
  apply NoSp.of_all
  cases d
  · change encryptBatch.allInstrs _ = true
    lit_decide
  · change decryptBatch.allInstrs _ = true
    lit_decide

theorem batch_stack (d : Spec.TripleDes.Direction) : stackUse (batchCode d) = 0 := by
  cases d
  · change stackUse encryptBatch = 0
    lit_decide
  · change stackUse decryptBatch = 0
    lit_decide

theorem batch_correct (d : Spec.TripleDes.Direction) (s : State) (hs : (batchContract d).pre s) :
    WP isa (batchCode d) s (fun s' => abiPreserved s s' ∧ (batchContract d).post s s') := by
  obtain ⟨rd, wr, keySpace, retSpace, fit, keyFit, spFit⟩ := hs
  have argRead (i : Nat) (hi : i < 2) : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (4 + 4 * i)) 4 := by
    rw [rd, wr, addr_eq (by omega_using [spFit, hi])]
    exact ⟨⟨argAddr s 0, 8⟩, by simp, argContainsCount s 2 (by omega_using [spFit]) i hi⟩
  have hp : BatchPre s (arg s 0) (arg s 1) :=
    { a0 := rfl, a1 := rfl, r0 := argRead 0 (by decide), r1 := argRead 1 (by decide)
      space := by rw [wr]; exact List.mem_singleton_self _
      fit := fit
      key := by rw [rd]; exact List.mem_cons_self
      keyFit := keyFit
      apart := keySpace }
  rw [batchCode_eq]
  refine WP.mono (batch_wp d hp) fun s' h => ⟨⟨h.callee, ?_⟩, h.blocks, h.mid⟩
  refine h.frame.readW (r := ⟨addr32 (s.gpr .esp), 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact retSpace

theorem batchCall_eq (d : Spec.TripleDes.Direction) : Impl.TripleDes.X86.Ecb.batchCall d =
    .frame (.push [.ebx, .ebp])
      (.call (match d with | .encrypt => "vg_triple_des_encrypt_batch" | .decrypt => "vg_triple_des_decrypt_batch")
        (batchCode d)) (.pop .eax 2) := by cases d <;> rfl

/-- What a call of a bitsliced function needs: the schedule at `ebx` and the
working space at `ebp`. -/
structure BatchCallPre (s : State) : Prop where
  reads : Covers [⟨addr32 (s.gpr .ebx), 384⟩, ⟨addr32 (s.gpr .ebp), 784⟩] (s.rd ++ s.wr)
  writes : Covers [⟨addr32 (s.gpr .ebp), 784⟩] s.wr
  keySpace : (Region.mk (addr32 (s.gpr .ebx)) 384).Disjoint ⟨addr32 (s.gpr .ebp), 784⟩
  keyFit : (s.gpr .ebx).toNat + 384 ≤ 2 ^ 32
  spaceFit : (s.gpr .ebp).toNat + 784 ≤ 2 ^ 32
  stackLo : 12 ≤ (s.gpr .esp).toNat
  stackKey : (below (s.gpr .esp) 12).Disjoint ⟨addr32 (s.gpr .ebx), 384⟩
  stackSpace : (below (s.gpr .esp) 12).Disjoint ⟨addr32 (s.gpr .ebp), 784⟩

structure BatchCallPost (d : Spec.TripleDes.Direction) (s s' : State) : Prop where
  callee : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [⟨addr32 (s.gpr .ebp), 784⟩, below (s.gpr .esp) 12] s.mem s'.mem
  blocks : ∀ b < 32, Spec.TripleDes.blockAt s'.mem (wordAddr (s.gpr .ebp) (bufSlot + 2 * b)) =
    blockOut (Spec.TripleDes.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
      (Spec.TripleDes.blockAt s.mem (wordAddr (s.gpr .ebp) (bufSlot + 2 * b)))
  mid : ∀ k, 87 ≤ k → k < bufSlot →
    s'.mem.readW (wordAddr (s.gpr .ebp) k) 32 = s.mem.readW (wordAddr (s.gpr .ebp) k) 32

/-- Words of the working space are in it. -/
theorem space_sub {A : BitVec 32} (fit : A.toNat + 784 ≤ 2 ^ 32) {k n : Nat} (hk : 4 * k + n ≤ 784)
    (hn : 0 < n) : Region.Sub ⟨wordAddr A k, n⟩ ⟨addr32 A, 784⟩ := by
  rw [wordAddr, addr_eq (by omega_using [fit, hk, hn])]
  exact Offset.sub_base _ hk

theorem batchCall_ok (d : Spec.TripleDes.Direction) (s : State) (hp : BatchCallPre s) :
    WP isa (Impl.TripleDes.X86.Ecb.batchCall d) s (BatchCallPost d s) := by
  rw [batchCall_eq]
  let rs : List Reg := [.ebx, .ebp]
  obtain hrs : .esp ∉ rs := by decide
  have fit : 4 * rs.length + 4 ≤ (s.gpr .esp).toNat := hp.stackLo
  let sE := (pushed rs s).callEntry
  obtain a0 : arg sE 0 = s.gpr .ebp := by rw [callEntry_arg fit hrs (by decide)]; rfl
  obtain a1 : arg sE 1 = s.gpr .ebx := by rw [callEntry_arg fit hrs (by decide)]; rfl
  obtain eA : argAddr sE 0 = ((s.gpr .esp) - BitVec.ofNat 32 8).setWidth 64 := by rw [callEntry_argAddr0]; rfl
  obtain eSp : sE.gpr .esp = s.gpr .esp - BitVec.ofNat 32 12 := by rw [callEntry_esp']; rfl
  obtain r4 : Region.Sub ⟨((s.gpr .esp) - BitVec.ofNat 32 12).setWidth 64, 4⟩ (below (s.gpr .esp) 12) :=
    Region.sub_prefix (by decide)
  refine callWithGpr (c := batchCode d) (k := batchContract d)
    (batch_correct d) (batch_nosp d) (by decide) hrs
    (by rw [batch_stack]; exact hp.stackLo) (rd := [⟨addr32 (s.gpr .ebx), 384⟩, ⟨argAddr sE 0, 8⟩])
    (wr := [⟨addr32 (s.gpr .ebp), 784⟩]) ⟨?_, ?_, ?_⟩ ?_
  · change (batchContract d).pre (sE.withRegions _ _)
    simp only [batchContract, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    refine ⟨trivial, trivial, hp.keySpace, hp.stackSpace.sub_left r4, hp.spaceFit, hp.keyFit, ?_⟩
    rw [sub_toNat hp.stackLo]
    have := (s.gpr .esp).isLt
    omega_using []
  · intro a n ⟨r, hr, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
    · apply InRegions_append_cons.mpr
      left
      rw [eA] at hc
      exact hc
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
  · intro a n h
    obtain ⟨r, hr, hc⟩ := hp.writes a n h
    exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩
  · intro s' rd wr cs frame ⟨s₂, mem₂, gpr₂, post⟩
    rw [batch_stack] at frame
    change (batchContract d).post (sE.withRegions _ _) s₂ at post
    simp only [batchContract, State.withRegions_mem, arg_withRegions, a0, a1] at post
    obtain ⟨blocks, mid⟩ := post
    obtain stackFrame := callEntry_frame fit hrs
    change Frame [below (s.gpr .esp) 12] s.mem sE.mem at stackFrame
    obtain m12 : Frame [below (s.gpr .esp) 12] s₂.mem s'.mem :=
      Frame.below_mono (wr := []) mem₂ (by decide) hp.stackLo
    have sep : ∀ {k n : Nat}, 4 * k + n ≤ 784 → 0 < n → ∀ r ∈ [below (s.gpr .esp) 12],
        (⟨wordAddr (s.gpr .ebp) k, n⟩ : Region).Disjoint r := by
      intro k n hk hn r hr
      obtain rfl := List.mem_singleton.mp hr
      exact (hp.stackSpace.sub_right (space_sub hp.spaceFit hk hn)).symm
    refine ⟨cs, rd, wr, frame, fun b hb => ?_, fun k hlo hhi => ?_⟩
    · have hk : 4 * (bufSlot + 2 * b) + 8 ≤ 784 := by unfold bufSlot; omega_using [hb]
      rw [VG.Proof.TripleDes.blockAt_eq_of_frame _ m12 (sep hk (by decide)), blocks b hb,
        VG.Proof.TripleDes.scheduleAt_eq_of_frame (p := addr32 (s.gpr .ebx)) stackFrame
          (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact hp.stackKey.symm),
        VG.Proof.TripleDes.blockAt_eq_of_frame _ stackFrame (sep hk (by decide))]
    · have hk : 4 * k + 4 ≤ 784 := by unfold bufSlot at hhi; omega_using [hhi]
      rw [m12.readW (Region.contains_self _ _) (sep hk (by decide)) (by decide), mid k hlo hhi,
        stackFrame.readW (Region.contains_self _ _) (sep hk (by decide)) (by decide)]

end VG.Proof.TripleDes.X86.Ecb

end

/-! ## `Pre` -/

section

/-! # Permissions and separation for one ECB step -/

namespace VG.Proof.TripleDes.X86.Ecb

open VG VG.X86
open VG.Proof.Rc2.X86 (addr32 addr_add)

abbrev keyR (s : State) : Region := ⟨addr32 (s.gpr .ebx), 384⟩
abbrev dataR (s : State) (n : Nat := 1) : Region := ⟨addr32 (s.gpr .esi), 8 * n⟩
abbrev bufR (s : State) : Region := ⟨addr32 (s.gpr .ebp), 1024⟩

structure StepPre (s : State) (n : Nat := 1) : Prop where
  reads : Covers [keyR s, dataR s n, bufR s] (s.rd ++ s.wr)
  writes : Covers [dataR s n, bufR s] s.wr
  keyData : (keyR s).Disjoint (dataR s n)
  keyBuf : (keyR s).Disjoint (bufR s)
  dataBuf : (dataR s n).Disjoint (bufR s)
  keyFit : (s.gpr .ebx).toNat + 384 ≤ 2 ^ 32
  dataFit : (s.gpr .esi).toNat + 8 * n ≤ 2 ^ 32
  bufFit : (s.gpr .ebp).toNat + 1024 ≤ 2 ^ 32
  stackLo : 16 ≤ (s.gpr .esp).toNat
  stackKey : (below (s.gpr .esp) 16).Disjoint (keyR s)
  stackData : (below (s.gpr .esp) 16).Disjoint (dataR s n)
  stackBuf : (below (s.gpr .esp) 16).Disjoint (bufR s)


end VG.Proof.TripleDes.X86.Ecb

end

/-! ## `Slice` -/

section

/-! # Restricting ECB permissions to a consecutive subrange -/

namespace VG.Proof.TripleDes.X86.Ecb

open VG VG.X86
open VG.Proof.Rc2.X86 (addr32 addr_add)

theorem StepPre.slice {s s' : State} {n m i : Nat} (hp : StepPre s n) (bound : i + m ≤ n) (hm : 1 ≤ m)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (key : s'.gpr .ebx = s.gpr .ebx)
    (buf : s'.gpr .ebp = s.gpr .ebp)
    (sp : s'.gpr .esp = s.gpr .esp)
    (ptr : s'.gpr .esi = s.gpr .esi + BitVec.ofNat 32 (8 * i)) : StepPre s' m := by
  obtain fit : (s.gpr .esi).toNat + 8 * i < 2 ^ 32 := by omega_using [hp.dataFit, bound, hm]
  obtain ptrAddr : addr32 (s'.gpr .esi) = addr32 (s.gpr .esi) + BitVec.ofNat 64 (8 * i) := by
    rw [ptr, addr_add fit]
  obtain sub : Region.Sub (dataR s' m) (dataR s n) := by
    change Region.Sub ⟨addr32 (s'.gpr .esi), 8 * m⟩ ⟨addr32 (s.gpr .esi), 8 * n⟩
    rw [ptrAddr]
    exact Offset.sub_base _ (by omega_using [bound])
  constructor
  · have hc : Covers [keyR s', dataR s' m, bufR s'] [keyR s, dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨keyR s, by simp, 0, by simp [key], by simp⟩
      · exact ⟨dataR s n, by simp, 8 * i, ptrAddr, by change 8 * i + 8 * m ≤ 8 * n; omega_using [bound]⟩
      · exact ⟨bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [rd, wr]
    exact fun a k h => hp.reads a k (hc a k h)
  · have hc : Covers [dataR s' m, bufR s'] [dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨dataR s n, by simp, 8 * i, ptrAddr, by change 8 * i + 8 * m ≤ 8 * n; omega_using [bound]⟩
      · exact ⟨bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [wr]
    exact fun a k h => hp.writes a k (hc a k h)
  · simpa only [keyR, key] using hp.keyData.sub_right sub
  · simpa only [keyR, bufR, key, buf] using hp.keyBuf
  · simpa only [bufR, buf] using hp.dataBuf.sub_left sub
  · rw [key]; exact hp.keyFit
  · rw [ptr]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_using [fit] : 8 * i < 2 ^ 32), Nat.mod_eq_of_lt fit]
    omega_using [hp.dataFit, bound]
  · rw [buf]; exact hp.bufFit
  · rw [sp]; exact hp.stackLo
  · simpa only [keyR, key, sp] using hp.stackKey
  · rw [sp]; exact hp.stackData.sub_right sub
  · simpa only [bufR, buf, sp] using hp.stackBuf

theorem StepPre.head {s : State} {n : Nat} (hp : StepPre s n) (hn : 1 ≤ n) : StepPre s :=
  hp.slice (i := 0) hn (by decide) rfl rfl rfl rfl rfl (by simp)

end VG.Proof.TripleDes.X86.Ecb

end

/-! ## `Steps` -/

section

namespace VG.Proof.TripleDes.X86.Ecb
open VG VG.X86 VG.X86.Wp VG.Impl.TripleDes.X86 VG.Impl.TripleDes.X86.Ecb
open VG.X86.Straight (addr_add_ofNat)
open VG.Proof.Modes (off_sub_toNat off_sub_not)

theorem eval_b (s : State) : isa.eval .b s = s.cf := rfl

theorem eval_ne (s : State) : isa.eval .ne s = s.zf.map (!·) := rfl

theorem ofNat32_beq_zero {x : Nat} (hx : x < 2 ^ 32) : (BitVec.ofNat 32 x == 0) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  bv_omega

/-- The group's count, `min(edi, 32)`, into `ecx`. -/
theorem countR_ok {s : State} {m : Nat} (hm : m < 2 ^ 32) (he : s.gpr .edi = BitVec.ofNat 32 m) :
    WP isa countR s fun s' => s'.gpr .ecx = BitVec.ofNat 32 (min m 32) ∧
      (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold countR
  apply WP.seq
  show WP isa (.block [.mov .ecx (.reg .edi), .alu .cmp .edi (.imm 32)]) s _
  refine wp_mov fun s₁ u₁ => ?_
  refine wp_cmpi fun s₂ u₂ cf₂ _ => WP.block_nil ?_
  have e₂ : s₂.gpr .ecx = BitVec.ofNat 32 m := by rw [u₂.gpr, u₁.gpr]; exact he
  have o₂ : ∀ r, r ≠ .ecx → s₂.gpr r = s.gpr r := fun r hr => by rw [u₂.gpr]; exact u₁.other r hr
  have cf : s₂.cf = some (decide (m < 32)) := by
    rw [cf₂, u₁.other _ (by decide), he, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]; rfl
  refine WP.ite (decide (m < 32)) ((eval_b s₂).trans cf) (fun h => ?_) (fun h => ?_)
  · have h : m < 32 := of_decide_eq_true h
    exact WP.block_nil ⟨by rw [e₂, Nat.min_eq_left (Nat.le_of_lt h)], o₂, by rw [u₂.mem, u₁.mem],
      by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  · have h : ¬ m < 32 := of_decide_eq_false h
    show WP isa (.block [.mov .ecx (.imm (BitVec.ofNat 32 32))]) s₂ _
    refine wp_movi fun s₃ u₃ => WP.block_nil ⟨by rw [u₃.gpr, Nat.min_eq_right (Nat.le_of_not_lt h)],
      fun r hr => (u₃.other r hr).trans (o₂ r hr), by rw [u₃.mem, u₂.mem, u₁.mem],
      by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr]⟩

theorem writeW_readW32_apply (m m' : Mem) (a c x : Addr) :
    m.writeW a (m'.readW c 32) x =
      if (x - a).toNat < 4 then m' (c + BitVec.ofNat 64 (x - a).toNat) else m x := by
  simp only [Mem.writeW, Mem.write, Mem.readW, BitVec.setWidth_eq]
  split
  · rename_i h
    exact Mem.extractLsb'_read m' c (n := 4) h
  · rfl

/-- What a copy of `c` blocks keeps, after its first `k` bytes. -/
structure Copied (A B : Addr) (c : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  copied : ∀ t < k, s.mem (B + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t)
  frame : Frame [⟨B, 8 * c⟩] s₀.mem s.mem

/-- `mov eax, [a + d]; mov [b + d], eax`: the copy's next word. -/
theorem copyWord_wp {a b : Reg} (hbe : b ≠ .eax) {A B : BitVec 32} {c : Nat} {s₀ s : State} {j d : Nat}
    (hd : d + 4 ≤ 8) (hj : j < c) (hfA : A.toNat + 8 * c ≤ 2 ^ 32) (hfB : B.toNat + 8 * c ≤ 2 ^ 32)
    (hsep : Region.Disjoint ⟨A.setWidth 64, 8 * c⟩ ⟨B.setWidth 64, 8 * c⟩)
    (hr : InRegions (s.rd ++ s.wr) (A.setWidth 64 + BitVec.ofNat 64 (8 * j + d)) 4)
    (hw : InRegions s.wr (B.setWidth 64 + BitVec.ofNat 64 (8 * j + d)) 4)
    (h0 : s.gpr a = A + BitVec.ofNat 32 (8 * j)) (h1 : s.gpr b = B + BitVec.ofNat 32 (8 * j))
    (hi : Copied (A.setWidth 64) (B.setWidth 64) c s₀ (8 * j + d) s)
    {is : List Instr} {Q : State → Prop}
    (kont : ∀ s', Copied (A.setWidth 64) (B.setWidth 64) c s₀ (8 * j + d + 4) s' →
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.mov .eax (.mem (memOp a d)) :: .store (memOp b d) .eax :: is)) s Q := by
  have eA : addr (A + BitVec.ofNat 32 (8 * j)) d = A.setWidth 64 + BitVec.ofNat 64 (8 * j + d) := by
    rw [addr_add_ofNat, addr_eq (by omega_using [hd, hj, hfA])]
  have eB : addr (B + BitVec.ofNat 32 (8 * j)) d = B.setWidth 64 + BitVec.ofNat 64 (8 * j + d) := by
    rw [addr_add_ofNat, addr_eq (by omega_using [hd, hj, hfB])]
  show WP isa (.block (.mov .eax (.mem ⟨a, d⟩) :: .store ⟨b, d⟩ .eax :: is)) s Q
  refine wp_ldm (B := A + BitVec.ofNat 32 (8 * j)) h0 (by rw [eA]; exact hr) fun s₁ u₁ => ?_
  refine wp_stm (B := B + BitVec.ofNat 32 (8 * j)) ((u₁.other _ hbe).trans h1)
    (by rw [u₁.wr, eB]; exact hw) fun s₂ u₂ => ?_
  have m₂ : s₂.mem = s.mem.writeW (B.setWidth 64 + BitVec.ofNat 64 (8 * j + d))
      (s.mem.readW (A.setWidth 64 + BitVec.ofNat 64 (8 * j + d)) 32) := by
    rw [u₂.mem, u₁.mem, u₁.gpr, eA, eB]
  refine kont s₂ ⟨fun t ht' => ?_, hi.frame.trans fun x hx => ?_⟩
    (fun r hr' => by rw [u₂.gpr]; exact u₁.other r hr') (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
  · have hAs : ∀ t < 8 * c, s.mem (A.setWidth 64 + BitVec.ofNat 64 t) =
        s₀.mem (A.setWidth 64 + BitVec.ofNat 64 t) := fun t ht =>
      hi.frame.bytes (R := ⟨A.setWidth 64, 8 * c⟩)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
        (by simp only; omega_using [hfA]) ht
    rw [m₂, writeW_readW32_apply]
    by_cases h8 : 8 * j + d ≤ t
    · rw [ite_eq_left (by rw [off_sub_toNat _ h8 (by omega_using [hd, hj, hfA, ht'])]; omega_using [ht']),
        off_sub_toNat _ h8 (by omega_using [hd, hj, hfA, ht']), VG.Offset.add_add,
        show 8 * j + d + (t - (8 * j + d)) = t by omega_using [h8], hAs t (by omega_using [hd, hj, ht'])]
    · rw [ite_eq_right (off_sub_not _ (Or.inl (by omega_using [h8])) (by omega_using [hd, hj, hfA, ht'])
        (by omega_using []) (by omega_using [hd, hj, hfA]))]
      exact hi.copied t (by omega_using [h8])
  · rw [m₂, writeW_readW32_apply, ite_eq_right fun h =>
      hx _ (List.mem_singleton_self _) (VG.Offset.sub_base _ (show 8 * j + d + 4 ≤ 8 * c by omega_using [hd, hj]) _
        (by simp only [Region.Contains]; omega_using [h]))]

/-- Copying, after `j` of `c` blocks. -/
structure CopyInv (a b : Reg) (A B : BitVec 32) (c : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  src : s.gpr a = A + BitVec.ofNat 32 (8 * j)
  dst : s.gpr b = B + BitVec.ofNat 32 (8 * j)
  cnt : s.gpr .ecx = BitVec.ofNat 32 (c - j)
  cp : Copied (A.setWidth 64) (B.setWidth 64) c s₀ (8 * j) s
  regs : ∀ r, r ≠ a → r ≠ b → r ≠ .ecx → r ≠ .eax → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- `copyBlocks a b` copies `c ≥ 1` blocks from `a` to `b` (areas that do not
overlap), a word at a time through `eax`, counting down `ecx`, and changes
nothing else in memory. -/
theorem copyBlocks_wp {a b : Reg} (hab : a ≠ b) (hae : a ≠ .eax) (hac : a ≠ .ecx) (hbe : b ≠ .eax)
    (hbc : b ≠ .ecx) {A B : BitVec 32} {c : Nat} {s₀ : State} (hc : 0 < c) (hc32 : c ≤ 32)
    (hfA : A.toNat + 8 * c ≤ 2 ^ 32) (hfB : B.toNat + 8 * c ≤ 2 ^ 32)
    (hA : ∀ t, t + 4 ≤ 8 * c → InRegions (s₀.rd ++ s₀.wr) (A.setWidth 64 + BitVec.ofNat 64 t) 4)
    (hB : ∀ t, t + 4 ≤ 8 * c → InRegions s₀.wr (B.setWidth 64 + BitVec.ofNat 64 t) 4)
    (hsep : Region.Disjoint ⟨A.setWidth 64, 8 * c⟩ ⟨B.setWidth 64, 8 * c⟩)
    (hs : CopyInv a b A B c s₀ 0 s₀) :
    WP isa (copyBlocks a b) s₀ (CopyInv a b A B c s₀ c) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = c - j ∧ j < c ∧ CopyInv a b A B c s₀ j s)
    (fun n s hs => ?_) c s₀ ⟨0, by omega_using [], hc, hs⟩
  obtain ⟨j, rfl, hj, hi⟩ := hs
  show WP isa (.block [.mov .eax (.mem (memOp a 0)), .store (memOp b 0) .eax, .mov .eax (.mem (memOp a 4)),
    .store (memOp b 4) .eax, .alu .add a (.imm 8), .alu .add b (.imm 8), .alu .sub .ecx (.imm 1)]) s _
  refine copyWord_wp (d := 0) hbe (by decide) hj hfA hfB hsep
    (by rw [hi.rd, hi.wr]; exact hA _ (by omega_using [hj])) (by rw [hi.wr]; exact hB _ (by omega_using [hj]))
    hi.src hi.dst hi.cp fun s₁ c₁ g₁ rd₁ wr₁ => ?_
  refine copyWord_wp (d := 4) hbe (by decide) hj hfA hfB hsep
    (by rw [rd₁, wr₁, hi.rd, hi.wr]; exact hA _ (by omega_using [hj]))
    (by rw [wr₁, hi.wr]; exact hB _ (by omega_using [hj]))
    ((g₁ _ hae).trans hi.src) ((g₁ _ hbe).trans hi.dst) c₁ fun s₂ c₂ g₂ rd₂ wr₂ => ?_
  refine wp_addi fun s₃ u₃ => ?_
  refine wp_addi fun s₄ u₄ => ?_
  refine wp_subi fun s₅ u₅ _ z₅ => WP.block_nil ?_
  have g₂' : ∀ r, r ≠ .eax → s₂.gpr r = s.gpr r := fun r hr => (g₂ r hr).trans (g₁ r hr)
  have e8 : (8 : BitVec 32) = BitVec.ofNat 32 8 := rfl
  have ecx₄ : s₄.gpr .ecx = BitVec.ofNat 32 (c - j) := by
    rw [u₄.other _ (Ne.symm hbc), u₃.other _ (Ne.symm hac), g₂' _ (by decide), hi.cnt]
  have hc₅ : s₅.gpr .ecx = BitVec.ofNat 32 (c - (j + 1)) := by
    rw [u₅.gpr, ecx₄, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      VG.Offset.ofNat_sub_ofNat (by omega_using [hj]), show c - j - 1 = c - (j + 1) by omega_using []]
  have hm : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  have hinv : CopyInv a b A B c s₀ (j + 1) s₅ := by
    refine ⟨?_, ?_, hc₅, ⟨fun t ht => ?_, by rw [hm]; exact c₂.frame⟩, fun r h1 h2 h3 h4 => ?_,
      by rw [u₅.rd, u₄.rd, u₃.rd, rd₂, rd₁, hi.rd], by rw [u₅.wr, u₄.wr, u₃.wr, wr₂, wr₁, hi.wr]⟩
    · rw [u₅.other _ hac, u₄.other _ hab, u₃.gpr, g₂' _ hae, hi.src, e8, VG.Offset.add_add,
        show 8 * j + 8 = 8 * (j + 1) by omega_using []]
    · rw [u₅.other _ hbc, u₄.gpr, u₃.other _ (Ne.symm hab), g₂' _ hbe, hi.dst, e8, VG.Offset.add_add,
        show 8 * j + 8 = 8 * (j + 1) by omega_using []]
    · rw [hm]; exact c₂.copied t (by omega_using [ht])
    · rw [u₅.other r h3, u₄.other r h2, u₃.other r h1, g₂' r h4, hi.regs r h1 h2 h3 h4]
  have hz : s₅.zf = some (decide (c - (j + 1) = 0)) := by
    rw [z₅, ← u₅.gpr, hc₅, ofNat32_beq_zero (by omega_using [hc32])]
  by_cases hl : j + 1 = c
  · refine .inl ⟨(eval_ne s₅).trans (by rw [hz]; simp; omega_using [hl]),
      by rw [show j + 1 = c from hl] at hinv; exact hinv⟩
  · exact .inr ⟨(eval_ne s₅).trans (by rw [hz]; simp; omega_using [hj, hl]), c - (j + 1), by omega_using [hj],
      j + 1, rfl, by omega_using [hj, hl], hinv⟩

end VG.Proof.TripleDes.X86.Ecb

end

/-! ## `Body` -/

section

namespace VG.Proof.TripleDes.X86.Ecb
open VG VG.X86 VG.X86.Wp VG.X86.Straight VG.Spec.TripleDes VG.Impl.TripleDes.X86 VG.Impl.TripleDes.X86.Ecb
open VG.Proof.Rc2.X86 (addr32 addr_add)
open VG.Proof.TripleDes.Bitslice (blockOut wAt)
open VG.Impl.TripleDes.X86.Bitslice (bufSlot)

/-- The blocks of the working space. -/
abbrev tailA (s : State) : Addr := addr32 (s.gpr .ebp) + BitVec.ofNat 64 528

/-- What the steps of a group keep. -/
structure Held (s s' : State) : Prop where
  ebx : s'.gpr .ebx = s.gpr .ebx
  edi : s'.gpr .edi = s.gpr .edi
  ebp : s'.gpr .ebp = s.gpr .ebp
  esp : s'.gpr .esp = s.gpr .esp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Held.trans {s₁ s₂ s₃ : State} (h₁ : Held s₁ s₂) (h₂ : Held s₂ s₃) : Held s₁ s₃ :=
  ⟨h₂.ebx.trans h₁.ebx, h₂.edi.trans h₁.edi, h₂.ebp.trans h₁.ebp, h₂.esp.trans h₁.esp, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr⟩

/-- Blocks with the same bytes. -/
theorem blockAt_bytes {m m' : Mem} {p q : Addr}
    (h : ∀ i < 8, m' (p + BitVec.ofNat 64 i) = m (q + BitVec.ofNat 64 i)) : blockAt m' p = blockAt m q := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, Vector.getElem_ofFn]
  exact h i hi

theorem bufAddr_ok (s : State) :
    WP isa (.block bufAddr) s fun s' => s'.gpr .edx = s.gpr .ebp + BitVec.ofNat 32 528 ∧
      (∀ r, r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  show WP isa (.block [.mov .edx (.reg .ebp), .alu .add .edx (.imm (BitVec.ofNat 32 528))]) s _
  refine wp_mov fun s₁ u₁ => ?_
  refine wp_addi fun s₂ u₂ => WP.block_nil ⟨by rw [u₂.gpr, u₁.gpr],
    fun r hr => (u₂.other r hr).trans (u₁.other r hr), by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd],
    by rw [u₂.wr, u₁.wr]⟩

/-- The address of the working space's blocks. -/
theorem tail_addr {W : BitVec 32} (fit : W.toNat + 1024 ≤ 2 ^ 32) :
    (W + BitVec.ofNat 32 528).setWidth 64 = addr32 W + BitVec.ofNat 64 528 ∧
      (W + BitVec.ofNat 32 528).toNat = W.toNat + 528 := by
  refine ⟨addr_add (by omega_using [fit]), ?_⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 528) (by decide),
    Nat.mod_eq_of_lt (by omega_using [fit])]

/-- The group's blocks, copied to the working space. -/
theorem copyIn_ok {s : State} {n : Nat} (hn : 1 ≤ n) (bound : n < 2 ^ 32)
    (count : s.gpr .edi = BitVec.ofNat 32 n) (hp : StepPre s n) :
    WP isa copyIn s fun s' => s'.gpr .esi = s.gpr .esi + BitVec.ofNat 32 (8 * min n 32) ∧ Held s s' ∧
      Frame [⟨tailA s, 8 * min n 32⟩] s.mem s'.mem ∧
      ∀ t < 8 * min n 32, s'.mem (tailA s + BitVec.ofNat 64 t) =
        s.mem (addr32 (s.gpr .esi) + BitVec.ofNat 64 t) := by
  have hk : 0 < min n 32 := by omega_using [hn]
  have hkn : min n 32 ≤ n := Nat.min_le_left _ _
  have hk32 : min n 32 ≤ 32 := Nat.min_le_right _ _
  have fitB := hp.bufFit
  have fitD := hp.dataFit
  obtain ⟨B64, Bn⟩ := tail_addr fitB
  unfold copyIn
  apply WP.seq
  refine WP.mono (countR_ok bound count) fun s₁ ⟨c₁, o₁, m₁, rd₁, wr₁⟩ => ?_
  apply WP.seq
  refine WP.mono (bufAddr_ok s₁) fun s₂ ⟨x₂, o₂, m₂, rd₂, wr₂⟩ => ?_
  have g₂ : ∀ r, r ≠ .edx → r ≠ .ecx → s₂.gpr r = s.gpr r := fun r h1 h2 => (o₂ r h1).trans (o₁ r h2)
  have mem₂ : s₂.mem = s.mem := m₂.trans m₁
  have rd₂' : s₂.rd = s.rd := rd₂.trans rd₁
  have wr₂' : s₂.wr = s.wr := wr₂.trans wr₁
  refine WP.mono (copyBlocks_wp (a := .esi) (b := .edx) (A := s.gpr .esi)
    (B := s.gpr .ebp + BitVec.ofNat 32 528) (c := min n 32) (s₀ := s₂) (by decide) (by decide) (by decide)
    (by decide) (by decide) hk hk32 (by omega_using [fitD, hkn]) (by rw [Bn]; omega_using [fitB, hk32])
    (fun t ht => ?_) (fun t ht => ?_) ?_ ⟨?_, ?_, ?_, ⟨fun t ht => absurd ht (Nat.not_lt_zero _), Frame.refl _ _⟩,
      fun _ _ _ _ _ => rfl, rfl, rfl⟩) fun s₃ I => ?_
  · rw [rd₂', wr₂']
    exact hp.reads _ _ ⟨dataR s n, List.mem_cons_of_mem _ List.mem_cons_self,
      Offset.contains_base _ (by omega_using [ht, hkn]) (by omega_using [ht, fitD])⟩
  · rw [wr₂', B64, VG.Offset.add_add]
    exact hp.writes _ _ ⟨bufR s, List.mem_cons_of_mem _ List.mem_cons_self,
      Offset.contains_base _ (by omega_using [ht, hk32]) (by omega_using [ht, hk32])⟩
  · rw [B64]
    exact (hp.dataBuf.sub_left (Region.sub_prefix (by omega_using [hkn]))).sub_right
      (Offset.sub_base _ (by omega_using [hk32]))
  · rw [g₂ _ (by decide) (by decide), Nat.mul_zero]; exact (BitVec.add_zero _).symm
  · rw [x₂, o₁ _ (by decide), Nat.mul_zero]; exact (BitVec.add_zero _).symm
  · rw [o₂ _ (by decide), c₁]; rfl
  · refine ⟨I.src, ⟨?_, ?_, ?_, ?_, I.rd.trans rd₂', I.wr.trans wr₂'⟩, ?_, fun t ht => ?_⟩
    · exact (I.regs _ (by decide) (by decide) (by decide) (by decide)).trans (g₂ _ (by decide) (by decide))
    · exact (I.regs _ (by decide) (by decide) (by decide) (by decide)).trans (g₂ _ (by decide) (by decide))
    · exact (I.regs _ (by decide) (by decide) (by decide) (by decide)).trans (g₂ _ (by decide) (by decide))
    · exact (I.regs _ (by decide) (by decide) (by decide) (by decide)).trans (g₂ _ (by decide) (by decide))
    · have := I.cp.frame
      rw [B64, mem₂] at this; exact this
    · have := I.cp.copied t ht
      rw [B64, mem₂] at this; exact this

/-- The working space's blocks, copied back to the group's. -/
theorem copyOut_ok {s : State} {n : Nat} (hn : 1 ≤ n) (bound : n < 2 ^ 32)
    (count : s.gpr .edi = BitVec.ofNat 32 n) (hp : StepPre s n) :
    WP isa copyOut s fun s' => s'.gpr .esi = s.gpr .esi + BitVec.ofNat 32 (8 * min n 32) ∧ Held s s' ∧
      Frame [dataR s (min n 32)] s.mem s'.mem ∧
      ∀ t < 8 * min n 32, s'.mem (addr32 (s.gpr .esi) + BitVec.ofNat 64 t) =
        s.mem (tailA s + BitVec.ofNat 64 t) := by
  have hk : 0 < min n 32 := by omega_using [hn]
  have hkn : min n 32 ≤ n := Nat.min_le_left _ _
  have hk32 : min n 32 ≤ 32 := Nat.min_le_right _ _
  have fitB := hp.bufFit
  have fitD := hp.dataFit
  obtain ⟨B64, Bn⟩ := tail_addr fitB
  unfold copyOut
  apply WP.seq
  refine WP.mono (countR_ok bound count) fun s₁ ⟨c₁, o₁, m₁, rd₁, wr₁⟩ => ?_
  apply WP.seq
  refine WP.mono (bufAddr_ok s₁) fun s₂ ⟨x₂, o₂, m₂, rd₂, wr₂⟩ => ?_
  have g₂ : ∀ r, r ≠ .edx → r ≠ .ecx → s₂.gpr r = s.gpr r := fun r h1 h2 => (o₂ r h1).trans (o₁ r h2)
  have mem₂ : s₂.mem = s.mem := m₂.trans m₁
  have rd₂' : s₂.rd = s.rd := rd₂.trans rd₁
  have wr₂' : s₂.wr = s.wr := wr₂.trans wr₁
  refine WP.mono (copyBlocks_wp (a := .edx) (b := .esi) (A := s.gpr .ebp + BitVec.ofNat 32 528)
    (B := s.gpr .esi) (c := min n 32) (s₀ := s₂) (by decide) (by decide) (by decide)
    (by decide) (by decide) hk hk32 (by rw [Bn]; omega_using [fitB, hk32]) (by omega_using [fitD, hkn])
    (fun t ht => ?_) (fun t ht => ?_) ?_ ⟨?_, ?_, ?_, ⟨fun t ht => absurd ht (Nat.not_lt_zero _), Frame.refl _ _⟩,
      fun _ _ _ _ _ => rfl, rfl, rfl⟩) fun s₃ I => ?_
  · rw [rd₂', wr₂', B64, VG.Offset.add_add]
    exact hp.reads _ _ ⟨bufR s, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      Offset.contains_base _ (by omega_using [ht, hk32]) (by omega_using [ht, hk32])⟩
  · rw [wr₂']
    exact hp.writes _ _ ⟨dataR s n, List.mem_cons_self,
      Offset.contains_base _ (by omega_using [ht, hkn]) (by omega_using [ht, fitD])⟩
  · rw [B64]
    exact ((hp.dataBuf.sub_left (Region.sub_prefix (by omega_using [hkn]))).sub_right
      (Offset.sub_base _ (by omega_using [hk32]))).symm
  · rw [x₂, o₁ _ (by decide), Nat.mul_zero]; exact (BitVec.add_zero _).symm
  · rw [g₂ _ (by decide) (by decide), Nat.mul_zero]; exact (BitVec.add_zero _).symm
  · rw [o₂ _ (by decide), c₁]; rfl
  · refine ⟨I.dst, ⟨?_, ?_, ?_, ?_, I.rd.trans rd₂', I.wr.trans wr₂'⟩, ?_, fun t ht => ?_⟩
    · exact (I.regs _ (by decide) (by decide) (by decide) (by decide)).trans (g₂ _ (by decide) (by decide))
    · exact (I.regs _ (by decide) (by decide) (by decide) (by decide)).trans (g₂ _ (by decide) (by decide))
    · exact (I.regs _ (by decide) (by decide) (by decide) (by decide)).trans (g₂ _ (by decide) (by decide))
    · exact (I.regs _ (by decide) (by decide) (by decide) (by decide)).trans (g₂ _ (by decide) (by decide))
    · have := I.cp.frame
      rw [mem₂] at this; exact this
    · have := I.cp.copied t ht
      rw [B64, mem₂] at this; exact this

/-- `esi` back to the group's first block. -/
theorem rewind_ok {s : State} {n : Nat} (bound : n < 2 ^ 32) (count : s.gpr .edi = BitVec.ofNat 32 n)
    {D : BitVec 32} (hD : s.gpr .esi = D + BitVec.ofNat 32 (8 * min n 32)) :
    WP isa rewind s fun s' => s'.gpr .esi = D ∧ Held s s' ∧ s'.mem = s.mem := by
  unfold rewind
  apply WP.seq
  refine WP.mono (countR_ok bound count) fun s₁ ⟨c₁, o₁, m₁, rd₁, wr₁⟩ => ?_
  refine wp_add fun s₂ u₂ _ => ?_
  refine wp_add fun s₃ u₃ _ => ?_
  refine wp_add fun s₄ u₄ _ => ?_
  refine wp_sub fun s₅ u₅ _ => WP.block_nil ?_
  have e : s₄.gpr .ecx = BitVec.ofNat 32 (8 * min n 32) := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr, c₁, ← BitVec.ofNat_add, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    exact congrArg (BitVec.ofNat 32) (by omega_using [])
  have g : ∀ r, r ≠ .ecx → s₄.gpr r = s.gpr r := fun r hr =>
    (u₄.other r hr).trans ((u₃.other r hr).trans ((u₂.other r hr).trans (o₁ r hr)))
  have g' : ∀ r, r ≠ .ecx → r ≠ .esi → s₅.gpr r = s.gpr r := fun r h1 h2 => (u₅.other r h2).trans (g r h1)
  refine ⟨?_, ⟨g' _ (by decide) (by decide), g' _ (by decide) (by decide), g' _ (by decide) (by decide),
    g' _ (by decide) (by decide), by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁],
    by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]⟩, by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]⟩
  rw [u₅.gpr, e, g _ (by decide), hD]
  exact BitVec.add_sub_cancel _ _

/-- The blocks left. -/
theorem advance_ok {s : State} {n : Nat} (bound : n < 2 ^ 32) (count : s.gpr .edi = BitVec.ofNat 32 n) :
    WP isa advance s fun s' => s'.gpr .edi = BitVec.ofNat 32 (n - min n 32) ∧
      isa.eval .ne s' = some (decide (min n 32 < n)) ∧
      (∀ r, r ≠ .edi → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold advance
  apply WP.seq
  refine WP.mono (countR_ok bound count) fun s₁ ⟨c₁, o₁, m₁, rd₁, wr₁⟩ => ?_
  refine wp_sub fun s₂ u₂ z₂ => WP.block_nil ?_
  have e : s₁.gpr .edi - s₁.gpr .ecx = BitVec.ofNat 32 (n - min n 32) := by
    rw [o₁ _ (by decide), count, c₁, VG.Offset.ofNat_sub_ofNat (Nat.min_le_left _ _)]
  refine ⟨u₂.gpr.trans e, ?_, fun r h1 h2 => (u₂.other r h1).trans (o₁ r h2), by rw [u₂.mem, m₁],
    by rw [u₂.rd, rd₁], by rw [u₂.wr, wr₁]⟩
  rw [eval_ne, z₂, e, ofNat32_beq_zero (by omega_using [bound])]
  simp only [Option.map_some, Option.some.injEq]
  by_cases h : min n 32 < n
  · simp only [h, decide_true, Bool.not_eq_true', decide_eq_false_iff_not]; omega_using [h]
  · simp only [h, decide_false, Bool.not_eq_false', decide_eq_true_eq]; omega_using [h]

theorem StepPre.batch {s : State} {n : Nat} (hp : StepPre s n) : BatchCallPre s := by
  have sub : Region.Sub ⟨addr32 (s.gpr .ebp), 784⟩ (bufR s) := Region.sub_prefix (by decide)
  have b12 : Region.Sub (below (s.gpr .esp) 12) (below (s.gpr .esp) 16) := below_sub (by decide) hp.stackLo
  constructor
  · have hc : Covers [⟨addr32 (s.gpr .ebx), 384⟩, ⟨addr32 (s.gpr .ebp), 784⟩]
        [keyR s, dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨keyR s, by simp, 0, by simp, by simp⟩
      · exact ⟨bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.reads a n (hc a n h)
  · have hc : Covers [⟨addr32 (s.gpr .ebp), 784⟩] [dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.writes a n (hc a n h)
  · exact hp.keyBuf.sub_right sub
  · exact hp.keyFit
  · omega_using [hp.bufFit]
  · omega_using [hp.stackLo]
  · exact hp.stackKey.sub_left b12
  · exact (hp.stackBuf.sub_left b12).sub_right sub

/-- What a group does: its `min(n, 32)` blocks. -/
structure GroupPost (d : Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .esi = s.gpr .esi + BitVec.ofNat 32 (8 * min n 32)
  count : s'.gpr .edi = BitVec.ofNat 32 (n - min n 32)
  flag : isa.eval .ne s' = some (decide (min n 32 < n))
  reg : ∀ r ∈ kept, r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [dataR s (min n 32), bufR s, below (s.gpr .esp) 16] s.mem s'.mem
  saved : ∀ i < 4, s'.mem.readW (addr32 (s.gpr .ebp) + BitVec.ofNat 64 (512 + 4 * i)) 32 =
    s.mem.readW (addr32 (s.gpr .ebp) + BitVec.ofNat 64 (512 + 4 * i)) 32
  data : ∀ b < min n 32, blockAt s'.mem (wAt (addr32 (s.gpr .esi)) b) =
    blockOut (scheduleAt s.mem (addr32 (s.gpr .ebx))) d (blockAt s.mem (wAt (addr32 (s.gpr .esi)) b))

theorem group_ok (d : Direction) (s : State) (n : Nat) (hn : 1 ≤ n) (bound : n < 2 ^ 32)
    (count : s.gpr .edi = BitVec.ofNat 32 n) (hp : StepPre s n) :
    WP isa (group d) s (GroupPost d s n) := by
  have hk : 0 < min n 32 := by omega_using [hn]
  have hkn : min n 32 ≤ n := Nat.min_le_left _ _
  have hk32 : min n 32 ≤ 32 := Nat.min_le_right _ _
  have fitB := hp.bufFit
  have fitD := hp.dataFit
  have zero : ∀ x : BitVec 32, x = x + BitVec.ofNat 32 (8 * 0) := fun x => (BitVec.add_zero x).symm
  unfold group
  apply WP.seq
  refine WP.mono (copyIn_ok hn bound count hp) fun s₁ ⟨p₁, k₁, f₁, c₁⟩ => ?_
  apply WP.seq
  refine WP.mono (rewind_ok bound (k₁.edi.trans count) p₁) fun s₂ ⟨p₂, k₂, m₂⟩ => ?_
  have k₁₂ := k₁.trans k₂
  have hp₂ : StepPre s₂ n :=
    hp.slice (i := 0) (m := n) (Nat.le_of_eq (Nat.zero_add n)) hn k₁₂.rd k₁₂.wr k₁₂.ebx k₁₂.ebp k₁₂.esp (p₂.trans (zero _))
  apply WP.seq
  refine WP.mono (batchCall_ok d s₂ hp₂.batch) fun s₃ h₃ => ?_
  have k₃ : Held s₂ s₃ := ⟨h₃.callee _ (by decide), h₃.callee _ (by decide), h₃.callee _ (by decide),
    h₃.callee _ (by decide), h₃.rd, h₃.wr⟩
  have p₃ : s₃.gpr .esi = s.gpr .esi := (h₃.callee _ (by decide)).trans p₂
  have k₁₃ := k₁₂.trans k₃
  have hp₃ : StepPre s₃ n :=
    hp.slice (i := 0) (m := n) (Nat.le_of_eq (Nat.zero_add n)) hn k₁₃.rd k₁₃.wr k₁₃.ebx k₁₃.ebp k₁₃.esp (p₃.trans (zero _))
  apply WP.seq
  refine WP.mono (copyOut_ok hn bound (k₁₃.edi.trans count) hp₃) fun s₄ ⟨p₄, k₄, f₄, c₄⟩ => ?_
  have k₁₄ := k₁₃.trans k₄
  refine WP.mono (advance_ok bound (k₁₄.edi.trans count)) fun s₅ ⟨e₅, z₅, o₅, m₅, rd₅, wr₅⟩ => ?_
  -- the regions written
  have tailSub : Region.Sub ⟨tailA s, 8 * min n 32⟩ (bufR s) := Offset.sub_base _ (by omega_using [hk32])
  have dataSub : Region.Sub (dataR s (min n 32)) (dataR s n) := Region.sub_prefix (by omega_using [hkn])
  have F₁ : Frame [dataR s (min n 32), bufR s, below (s.gpr .esp) 16] s.mem s₂.mem := by
    rw [m₂]
    refine f₁.sub fun r hr => ?_
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨bufR s, by simp, tailSub⟩
  have F₃ : Frame [dataR s (min n 32), bufR s, below (s.gpr .esp) 16] s₂.mem s₃.mem := by
    refine h₃.mem.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨bufR s, by simp, by rw [k₁₂.ebp]; exact Region.sub_prefix (by decide)⟩
    · exact ⟨below (s.gpr .esp) 16, by simp, by rw [k₁₂.esp]; exact below_sub (by decide) hp.stackLo⟩
  have F₄ : Frame [dataR s (min n 32), bufR s, below (s.gpr .esp) 16] s₃.mem s₅.mem := by
    rw [m₅]
    refine f₄.sub fun r hr => ?_
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨dataR s (min n 32), by simp, by rw [dataR, p₃]; exact fun _ h => h⟩
  -- a block of the working space
  have tailBlock : ∀ b < 32, ∀ i, wordAddr (s.gpr .ebp) (bufSlot + 2 * b) + BitVec.ofNat 64 i =
      tailA s + BitVec.ofNat 64 (8 * b + i) := by
    intro b hb i
    rw [wordAddr, addr_eq (by unfold bufSlot; omega_using [fitB, hb]), VG.Offset.add_add, tailA,
      VG.Offset.add_add]
    exact congrArg (fun t => addr32 (s.gpr .ebp) + BitVec.ofNat 64 t) (by unfold bufSlot; omega_using [])
  have dataByte : ∀ b i, wAt (addr32 (s.gpr .esi)) b + BitVec.ofNat 64 i =
      addr32 (s.gpr .esi) + BitVec.ofNat 64 (8 * b + i) := fun b i => VG.Offset.add_add _ _ _
  refine ⟨(o₅ _ (by decide) (by decide)).trans (p₄.trans (by rw [p₃])), e₅, z₅, fun r hr h1 h2 => ?_,
    rd₅.trans k₁₄.rd, wr₅.trans k₁₄.wr, F₁.trans (F₃.trans F₄), fun i hi => ?_, fun b hb => ?_⟩
  · simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (o₅ _ (by decide) (by decide)).trans k₁₄.ebx
    · exact absurd rfl h1
    · exact absurd rfl h2
    · exact (o₅ _ (by decide) (by decide)).trans k₁₄.ebp
    · exact (o₅ _ (by decide) (by decide)).trans k₁₄.esp
  · have wsub : Region.Sub ⟨addr32 (s.gpr .ebp) + BitVec.ofNat 64 (512 + 4 * i), 4⟩ (bufR s) :=
      Offset.sub_base _ (by omega_using [hi])
    have e₂ : wordAddr (s₂.gpr .ebp) (128 + i) = addr32 (s.gpr .ebp) + BitVec.ofNat 64 (512 + 4 * i) := by
      rw [k₁₂.ebp, wordAddr, addr_eq (by omega_using [fitB, hi])]
      exact congrArg (fun t => addr32 (s.gpr .ebp) + BitVec.ofNat 64 t) (by omega_using [])
    have mid := h₃.mid (128 + i) (by omega_using []) (by unfold bufSlot; omega_using [hi])
    rw [e₂] at mid
    rw [m₅, f₄.readW (Region.contains_self _ _) (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        rw [dataR, p₃]
        exact ((hp.dataBuf.sub_left dataSub).sub_right wsub).symm) (by decide), mid, m₂,
      f₁.readW (Region.contains_self _ _) (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact Offset.disjoint _ (.inl (by omega_using [hi])) (by omega_using [hi]) (by omega_using [hk32]))
        (by decide)]
  · have hb32 : b < 32 := by omega_using [hb, hk32]
    have key : scheduleAt s₂.mem (addr32 (s₂.gpr .ebx)) = scheduleAt s.mem (addr32 (s.gpr .ebx)) := by
      rw [k₁₂.ebx, m₂]
      exact VG.Proof.TripleDes.scheduleAt_eq_of_frame _ f₁ fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact hp.keyBuf.sub_right tailSub
    have out : blockAt s₅.mem (wAt (addr32 (s.gpr .esi)) b) =
        blockAt s₃.mem (wordAddr (s.gpr .ebp) (bufSlot + 2 * b)) := by
      refine blockAt_bytes fun i hi => ?_
      have := c₄ (8 * b + i) (by omega_using [hb, hi])
      rw [p₃, tailA, k₁₃.ebp] at this
      rw [m₅, dataByte, this, tailBlock b hb32]
    have inp : blockAt s₂.mem (wordAddr (s.gpr .ebp) (bufSlot + 2 * b)) =
        blockAt s.mem (wAt (addr32 (s.gpr .esi)) b) := by
      refine blockAt_bytes fun i hi => ?_
      rw [m₂, tailBlock b hb32, c₁ (8 * b + i) (by omega_using [hb, hi]), dataByte]
    have blk := h₃.blocks b hb32
    rw [k₁₂.ebp, key, inp] at blk
    rw [out, blk]

end VG.Proof.TripleDes.X86.Ecb

end

/-! ## `Loop` -/

section

/-! # Correctness of the ECB loop of groups -/

namespace VG.Proof.TripleDes.X86.Ecb

open VG VG.X86 VG.Spec.TripleDes
open VG.Proof.Rc2.X86 (addr32 addr_add)
open VG.Proof.TripleDes.Bitslice (blockOut wAt wAt_wAt ecb_blocks)

def loopWrites (s : State) (n : Nat) : List Region := [dataR s n, bufR s, below (s.gpr .esp) 16]

structure LoopPost (d : Spec.TripleDes.Direction) (s : State) (n : Nat) (s' : State) : Prop where
  ptr : s'.gpr .esi = s.gpr .esi + BitVec.ofNat 32 (8 * n)
  count : s'.gpr .edi = 0
  reg : ∀ r ∈ kept, r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (loopWrites s n) s.mem s'.mem
  saved : ∀ i < 4, s'.mem.readW (addr32 (s.gpr .ebp) + BitVec.ofNat 64 (512 + 4 * i)) 32 =
    s.mem.readW (addr32 (s.gpr .ebp) + BitVec.ofNat 64 (512 + 4 * i)) 32
  data : ∀ b < n, blockAt s'.mem (wAt (addr32 (s.gpr .esi)) b) =
    blockOut (scheduleAt s.mem (addr32 (s.gpr .ebx))) d (blockAt s.mem (wAt (addr32 (s.gpr .esi)) b))

theorem LoopPost.blocks {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat} (h : LoopPost d s n s') :
    Spec.TripleDes.blocksAt s'.mem (addr32 (s.gpr .esi)) n =
      Spec.TripleDes.ecb (Spec.TripleDes.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
        (Spec.TripleDes.blocksAt s.mem (addr32 (s.gpr .esi)) n) :=
  ecb_blocks _ d _ _ _ n h.data

/-- A block of the data is apart from what a group or the loop writes
elsewhere. -/
theorem blockSep {s : State} {n : Nat} (hp : StepPre s n) {b : Nat} (hb : b < n) :
    (⟨wAt (addr32 (s.gpr .esi)) b, 8⟩ : Region).Disjoint (bufR s) ∧
      (⟨wAt (addr32 (s.gpr .esi)) b, 8⟩ : Region).Disjoint (below (s.gpr .esp) 16) := by
  have sub : Region.Sub ⟨wAt (addr32 (s.gpr .esi)) b, 8⟩ (dataR s n) :=
    Offset.sub_base _ (by omega_using [hb])
  exact ⟨hp.dataBuf.sub_left sub, (hp.stackData.sub_right sub).symm⟩

theorem loop_ok (d : Spec.TripleDes.Direction) (n : Nat) :
    ∀ s : State, 1 ≤ n → 8 * n ≤ 2 ^ 32 → StepPre s n → s.gpr .edi = BitVec.ofNat 32 n →
      WP isa (.loop (Impl.TripleDes.X86.Ecb.group d) .ne) s (LoopPost d s n) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro s hn bound hp count
    have hkn : min n 32 ≤ n := Nat.min_le_left _ _
    have hk : 0 < min n 32 := by omega_using [hn]
    obtain ⟨t₁, s₁, exec₁, h₁⟩ := group_ok d s n hn (by omega_using [bound]) count hp
    have fitD := hp.dataFit
    have dataSub : Region.Sub (dataR s (min n 32)) (dataR s n) := Region.sub_prefix (by omega_using [hkn])
    have frame₁ : Frame (loopWrites s n) s.mem s₁.mem := by
      refine h₁.mem.sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨dataR s n, by simp [loopWrites], dataSub⟩
      · exact ⟨bufR s, by simp [loopWrites], fun _ h => h⟩
      · exact ⟨below (s.gpr .esp) 16, by simp [loopWrites], fun _ h => h⟩
    by_cases hlt : min n 32 < n
    · -- more groups
      have hp₁ : StepPre s₁ (n - min n 32) :=
        hp.slice (i := min n 32) (by omega_using [hkn]) (by omega_using [hlt]) h₁.rd h₁.wr
          (h₁.reg .ebx (by decide) (by decide) (by decide))
          (h₁.reg .ebp (by decide) (by decide) (by decide))
          (h₁.reg .esp (by decide) (by decide) (by decide)) h₁.ptr
      obtain ⟨t₂, s₂, exec₂, h₂⟩ := ih (n - min n 32) (by omega_using [hk, hlt]) s₁ (by omega_using [hlt])
        (by omega_using [bound]) hp₁ h₁.count
      refine ⟨_, s₂, Exec.loopNext exec₁ ?_ exec₂, ?_⟩
      · rw [h₁.flag]; simp only [hlt, decide_true]
      have ki := h₁.reg .ebx (by decide) (by decide) (by decide)
      have bi := h₁.reg .ebp (by decide) (by decide) (by decide)
      have si := h₁.reg .esp (by decide) (by decide) (by decide)
      have ptrAddr : addr32 (s₁.gpr .esi) = addr32 (s.gpr .esi) + BitVec.ofNat 64 (8 * min n 32) := by
        rw [h₁.ptr]; exact addr_add (by omega_using [fitD, hlt])
      have rest : Region.Sub (dataR s₁ (n - min n 32)) (dataR s n) := by
        rw [dataR, ptrAddr]; exact Offset.sub_base _ (by omega_using [hkn])
      have frame₂ : Frame (loopWrites s n) s₁.mem s₂.mem := by
        refine h₂.mem.sub fun r hr => ?_
        simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨dataR s n, by simp [loopWrites], rest⟩
        · exact ⟨bufR s, by simp [loopWrites], by rw [bufR, bi]; exact fun _ h => h⟩
        · exact ⟨below (s.gpr .esp) 16, by simp [loopWrites], by rw [si]; exact fun _ h => h⟩
      have key : scheduleAt s₁.mem (addr32 (s₁.gpr .ebx)) = scheduleAt s.mem (addr32 (s.gpr .ebx)) := by
        rw [ki]
        refine VG.Proof.TripleDes.scheduleAt_eq_of_frame _ h₁.mem fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.keyData.sub_right dataSub
        · exact hp.keyBuf
        · exact hp.stackKey.symm
      refine ⟨?_, h₂.count, fun r hr hs hb => (h₂.reg r hr hs hb).trans (h₁.reg r hr hs hb),
        h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, frame₁.trans frame₂, fun i hi => ?_, fun b hb => ?_⟩
      · rw [h₂.ptr, h₁.ptr, VG.Offset.add_add]
        exact congrArg (fun t => s.gpr .esi + BitVec.ofNat 32 t) (by omega_using [hkn])
      · have := h₂.saved i hi
        rw [bi] at this
        exact this.trans (h₁.saved i hi)
      · obtain ⟨sepBuf, sepStack⟩ := blockSep hp hb
        by_cases hbk : b < min n 32
        · rw [VG.Proof.TripleDes.blockAt_eq_of_frame _ h₂.mem (by
            intro r hr
            simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl
            · rw [dataR, ptrAddr]
              exact Offset.disjoint _ (.inl (by omega_using [hbk])) (by omega_using [hb, bound])
                (by omega_using [hkn, bound])
            · rw [bufR, bi]; exact sepBuf
            · rw [si]; exact sepStack)]
          exact h₁.data b hbk
        · have e : wAt (addr32 (s.gpr .esi)) b = wAt (addr32 (s₁.gpr .esi)) (b - min n 32) := by
            rw [ptrAddr, show addr32 (s.gpr .esi) + BitVec.ofNat 64 (8 * min n 32) =
              wAt (addr32 (s.gpr .esi)) (min n 32) from rfl, wAt_wAt]
            exact congrArg (wAt _) (by omega_using [hbk])
          have d₂ := h₂.data (b - min n 32) (by omega_using [hb, hbk])
          rw [← e, key] at d₂
          rw [d₂, VG.Proof.TripleDes.blockAt_eq_of_frame _ h₁.mem (by
            intro r hr
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl
            · exact Offset.disjoint_base _ (by omega_using [hbk]) (by omega_using [hb, bound])
            · exact sepBuf
            · exact sepStack)]
    · -- the last group
      have e : min n 32 = n := by omega_using [hlt, hkn]
      refine ⟨_, s₁, Exec.loopExit exec₁ ?_, ?_⟩
      · rw [h₁.flag]; simp only [hlt, decide_false]
      refine ⟨by rw [h₁.ptr, e], by rw [h₁.count, e, Nat.sub_self]; rfl, h₁.reg, h₁.rd, h₁.wr, frame₁,
        h₁.saved, fun b hb => h₁.data b (by rw [e]; exact hb)⟩

theorem maybeLoop_ok (d : Spec.TripleDes.Direction) (s : State) (n : Nat) (bound : 8 * n ≤ 2 ^ 32)
    (hp : StepPre s n) (count : s.gpr .edi = BitVec.ofNat 32 n)
    (initialFlag : isa.eval .e s = some (decide (n = 0))) :
    WP isa (.ite .e (.block []) (.loop (Impl.TripleDes.X86.Ecb.group d) .ne)) s (LoopPost d s n) := by
  have flag' := initialFlag
  by_cases hz : n = 0
  · subst n
    apply WP.ite true (by change isa.eval .e s = some true; simpa only [decide_true] using flag')
    · intro _
      apply WP.block_nil
      exact ⟨by simp, count, fun _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _, fun _ _ => rfl,
        fun b hb => absurd hb (Nat.not_lt_zero _)⟩
    · simp
  · apply WP.ite false (by change isa.eval .e s = some false; simpa only [hz, decide_false] using flag')
    · simp
    · intro _
      exact loop_ok d n s (by omega_using [hz]) bound hp count

end VG.Proof.TripleDes.X86.Ecb

end

/-! ## `IO` -/

section

namespace VG.Proof.TripleDes.X86.Ecb
open VG VG.X86 VG.X86.Straight VG.X86.RegUpd VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (Keep addr32)

theorem subtract_zero (x : BitVec 32) : x - (0 : BitVec 32) = x := by bv_omega

def savedMem (s : State) : Mem :=
  (((s.mem.writeW (addr32 (s.gpr .eax) + BitVec.ofNat 64 512) (s.gpr .ebp)).writeW
    (addr32 (s.gpr .eax) + BitVec.ofNat 64 516) (s.gpr .ebx)).writeW
    (addr32 (s.gpr .eax) + BitVec.ofNat 64 520) (s.gpr .esi)).writeW
    (addr32 (s.gpr .eax) + BitVec.ofNat 64 524) (s.gpr .edi)

theorem save_ok (s : State) (fit : (s.gpr .eax).toNat + 1024 ≤ 2 ^ 32)
    (hw : ∀ k ∈ [512, 516, 520, 524], InRegions s.wr (addr (s.gpr .eax) k) 4) :
    ∃ s', runBlock isa Impl.TripleDes.X86.Ecb.save s = some s' ∧ Keep [] {s with mem := savedMem s} s' := by
  obtain h0 := hw 512 (by decide)
  obtain h1 := hw 516 (by decide)
  obtain h2 := hw 520 (by decide)
  obtain h3 := hw 524 (by decide)
  simp only [addr] at h0 h1 h2 h3
  refine ⟨_, by
    change runBlock isa [.store (memOp .eax 512) .ebp, .store (memOp .eax 516) .ebx,
      .store (memOp .eax 520) .esi, .store (memOp .eax 524) .edi] s = _
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store32, State.ea,
      memOp, h0, h1, h2, h3, ite_true]
    rfl, ?_⟩
  refine ⟨fun _ _ => rfl, ?_, rfl, rfl⟩
  change (((s.mem.writeW (addr (s.gpr .eax) 512) (s.gpr .ebp)).writeW
    (addr (s.gpr .eax) 516) (s.gpr .ebx)).writeW
    (addr (s.gpr .eax) 520) (s.gpr .esi)).writeW
    (addr (s.gpr .eax) 524) (s.gpr .edi) = savedMem s
  unfold savedMem
  rw [addr_eq (by omega_using [fit] : (s.gpr .eax).toNat + 512 < 2 ^ 32),
    addr_eq (by omega_using [fit] : (s.gpr .eax).toNat + 516 < 2 ^ 32),
    addr_eq (by omega_using [fit] : (s.gpr .eax).toNat + 520 < 2 ^ 32),
    addr_eq (by omega_using [fit] : (s.gpr .eax).toNat + 524 < 2 ^ 32)]
  rfl

theorem savedMem_frame (s : State) :
    Frame [⟨addr32 (s.gpr .eax), 1024⟩] s.mem (savedMem s) := by
  unfold savedMem
  apply Frame.writeW _ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  apply Frame.writeW _ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  apply Frame.writeW _ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains_base _ (by decide) (by decide))

theorem setup_ok (s : State)
    (hr : ∀ i ∈ [1, 2, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4) :
    ∃ s', runBlock isa Impl.TripleDes.X86.Ecb.setup s = some s' ∧
      s'.gpr .ebp = s.gpr .eax ∧ s'.gpr .ebx = arg s 0 ∧ s'.gpr .esi = arg s 1 ∧
      s'.gpr .edi = arg s 2 ∧ isa.eval .e s' = some (arg s 2 == 0) ∧
      Keep [.ebp, .ebx, .esi, .edi] s s' := by
  obtain h0 := hr 1 (by decide)
  obtain h1 := hr 2 (by decide)
  obtain h2 := hr 3 (by decide)
  simp only [wordAddr, addr] at h0 h1 h2
  refine ⟨_, by
    simp only [Impl.TripleDes.X86.Ecb.setup, rr, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu, readSrc, State.load32, State.ea, memOp, h0, h1, h2, ite_true,
      Option.bind_some, Option.map_some, gpr_setReg, mem_setReg, rd_setReg,
      wr_setReg, reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact (argument_word s 0).symm
  · exact (argument_word s 1).symm
  · exact (argument_word s 2).symm
  · change some (((s.mem.readW (wordAddr (s.gpr .esp) 3) 32) - (0 : BitVec 32)) == (0 : BitVec 32)) = _
    rw [← argument_word s 2]
    exact congrArg (fun x : BitVec 32 => some (x == 0)) (subtract_zero (arg s 2))
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem restore_ok (original s : State)
    (hr : ∀ k ∈ [512, 516, 520, 524], InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) k) 4)
    (hv : ∀ i < 4, s.mem.readW (addr (s.gpr .ebp) (512 + 4 * i)) 32 = original.gpr (savedReg i)) :
    ∃ s', runBlock isa Impl.TripleDes.X86.Ecb.restore s = some s' ∧
      (∀ r ∈ savedRegs, s'.gpr r = original.gpr r) ∧
      Keep (.eax :: savedRegs) s s' := by
  obtain h0 := hr 512 (by decide)
  obtain h1 := hr 516 (by decide)
  obtain h2 := hr 520 (by decide)
  obtain h3 := hr 524 (by decide)
  obtain v0 := hv 0 (by decide)
  obtain v1 := hv 1 (by decide)
  obtain v2 := hv 2 (by decide)
  obtain v3 := hv 3 (by decide)
  simp only [addr] at h0 h1 h2 h3
  refine ⟨_, by
    change runBlock isa [rr .eax .ebp, .mov .ebp (.mem (memOp .eax 512)),
      .mov .ebx (.mem (memOp .eax 516)), .mov .esi (.mem (memOp .eax 520)),
      .mov .edi (.mem (memOp .eax 524))] s = _
    simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load32, State.ea, memOp, h0, h1, h2, h3, ite_true, Option.map_some,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, reduceCtorEq, ite_false]
    rfl, ?_, ?_⟩
  · intro r hr
    simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact v0
    · exact v1
    · exact v2
    · exact v3
  · refine ⟨?_, rfl, rfl, rfl⟩
    intro r hr
    simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

theorem loadScratch_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 4) 4) :
    ∃ s', runBlock isa [.mov .eax (.mem (memOp .esp 16))] s = some s' ∧
      s'.gpr .eax = arg s 3 ∧ Keep [.eax] s s' := by
  obtain he : exec (.mov .eax (.mem (memOp .esp 16))) s = some (s.setReg .eax (arg s 3)) := by
    simp only [exec, readSrc, State.load32, State.ea, memOp]
    change (if InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 4) 4 then
      some (s.mem.readW (wordAddr (s.gpr .esp) 4) 32) else none).map (s.setReg .eax) = _
    rw [ite_eq_left hr, ← argument_word s 3, Option.map_some]
  refine ⟨s.setReg .eax (arg s 3), by simp only [runBlock_cons, he, runStep_some, runBlock_nil],
    gpr_setReg_self _ _ _, ?_⟩
  exact ⟨fun r hr => gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using hr), rfl, rfl, rfl⟩

theorem savedMem_eq (s : State) : savedMem s = VG.Proof.Rc2.X86.saveMem s.mem
    (addr32 (s.gpr .eax) + BitVec.ofNat 64 512) (fun i => s.gpr (savedReg i)) 4 := by
  simp only [VG.Proof.Rc2.X86.saveMem_succ]
  change savedMem s = (((s.mem.writeW ((addr32 (s.gpr .eax) + BitVec.ofNat 64 512) + BitVec.ofNat 64 0) (s.gpr .ebp)).writeW
    ((addr32 (s.gpr .eax) + BitVec.ofNat 64 512) + BitVec.ofNat 64 4) (s.gpr .ebx)).writeW
    ((addr32 (s.gpr .eax) + BitVec.ofNat 64 512) + BitVec.ofNat 64 8) (s.gpr .esi)).writeW
    ((addr32 (s.gpr .eax) + BitVec.ofNat 64 512) + BitVec.ofNat 64 12) (s.gpr .edi)
  simp only [Offset.add_ofNat_add_ofNat]
  rfl

theorem savedMem_read (s : State) (i : Nat) (hi : i < 4) :
    (savedMem s).readW (addr32 (s.gpr .eax) + BitVec.ofNat 64 (512 + 4 * i)) 32 =
      s.gpr (savedReg i) := by
  rw [savedMem_eq, ← Offset.add_ofNat_add_ofNat]
  exact VG.Proof.Rc2.X86.saveMem_read _ _ _ 4 (by decide) i hi

end VG.Proof.TripleDes.X86.Ecb

end

/-! ## `Contract` -/

section

namespace VG.Proof.TripleDes.X86.Ecb
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)

def contract (d : Spec.TripleDes.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨addr32 (arg s 0), 384⟩
    let data : Region := ⟨addr32 (arg s 1), 8 * (arg s 2).toNat⟩
    let buf : Region := ⟨addr32 (arg s 3), 1024⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨addr32 (s.gpr .esp), 4⟩
    let stack := below (s.gpr .esp) 16
    s.rd = [key, args] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧ args.Disjoint data ∧ args.Disjoint buf ∧
      ret.Disjoint data ∧ ret.Disjoint buf ∧ stack.Disjoint key ∧ stack.Disjoint data ∧
      stack.Disjoint buf ∧ (arg s 0).toNat + 384 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 1024 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
      16 ≤ (s.gpr .esp).toNat ∧ (arg s 1).toNat + 8 * (arg s 2).toNat ≤ 2 ^ 32
  post s s' := Spec.TripleDes.blocksAt s'.mem (addr32 (arg s 1)) (arg s 2).toNat =
    Spec.TripleDes.ecb (Spec.TripleDes.scheduleAt s.mem (addr32 (arg s 0))) d
      (Spec.TripleDes.blocksAt s.mem (addr32 (arg s 1)) (arg s 2).toNat)
  pub s t := s.gpr .esp = t.gpr .esp ∧ ∀ i < 4, arg s i = arg t i

end VG.Proof.TripleDes.X86.Ecb

end

/-! ## `Correct` -/

section

namespace VG.Proof.TripleDes.X86.Ecb
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32 argContainsCount)

theorem counter_zero (x : BitVec 32) : (x == 0) = decide (x.toNat = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact BitVec.eq_of_toNat_eq (show x.toNat = (0 : BitVec 32).toNat from h)

theorem ecb_correct (d : Spec.TripleDes.Direction) (s : State) (hs : (contract d).pre s) :
    WP isa (Impl.TripleDes.X86.Ecb.ecb d) s (fun s' => abiPreserved s s' ∧ (contract d).post s s') := by
  obtain ⟨rd, wr, keyData, keyBuf, dataBuf, argsData, argsBuf, retData, retBuf,
    stackKey, stackData, stackBuf, keyFit, bufFit, spFit, stackLo, fit⟩ := hs
  have writes (i : Nat) (hi : i + 4 ≤ 1024) : InRegions s.wr
      (addr32 (arg s 3) + BitVec.ofNat 64 i) 4 := by
    rw [wr]
    exact ⟨⟨addr32 (arg s 3), 1024⟩, by simp, Offset.contains_base _ hi (by omega_using [hi])⟩
  have argRead (i : Nat) (hlo : 1 ≤ i) (hhi : i ≤ 4) :
      InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4 := by
    rw [rd, wr, wordAddr, addr_eq (by omega_using [spFit, hhi])]
    obtain hc := argContainsCount s 4 spFit (i - 1) (by omega_using [hlo, hhi])
    rw [show 4 + 4 * (i - 1) = 4 * i by omega_using [hlo]] at hc
    exact ⟨⟨argAddr s 0, 16⟩, by simp, hc⟩
  rw [Impl.TripleDes.X86.Ecb.ecb]
  apply WP.seq
  obtain ⟨s₀, run₀, buf₀, keep₀⟩ := loadScratch_ok s (argRead 4 (by decide) (by decide))
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  have g₀ (r : Reg) (hr : r ≠ .eax) := keep₀.reg r (by simpa only [List.mem_singleton] using hr)
  apply WP.seq
  rw [WP.block_append_iff]
  obtain ⟨s₁, run₁, keep₁⟩ := save_ok s₀ (by rw [buf₀]; exact bufFit) (by
    intro k hk
    rw [keep₀.wr, buf₀, addr_eq (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> omega_using [bufFit])]
    exact writes k (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> decide))
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have g₁ (r : Reg) : s₁.gpr r = s₀.gpr r := keep₁.reg r (by simp)
  obtain sp₁ : s₁.gpr .esp = s.gpr .esp := (g₁ .esp).trans (g₀ .esp (by decide))
  obtain saveFrame : Frame [⟨addr32 (arg s 3), 1024⟩] s.mem s₁.mem := by
    rw [keep₁.mem, ← keep₀.mem, ← buf₀]; exact savedMem_frame s₀
  obtain args₁ := VG.Proof.Rc2.X86.arguments_frame 4 saveFrame sp₁ spFit
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact argsBuf)
  obtain reads₁ : ∀ i ∈ [1, 2, 3], InRegions (s₁.rd ++ s₁.wr) (wordAddr (s₁.gpr .esp) i) 4 := by
    intro i hi
    rw [keep₁.rd, keep₁.wr, keep₀.rd, keep₀.wr, sp₁]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact argRead 1 (by decide) (by decide)
    · exact argRead 2 (by decide) (by decide)
    · exact argRead 3 (by decide) (by decide)
  obtain ⟨s₂, run₂, buf₂, key₂, data₂, count₂, flag₂, keep₂⟩ := setup_ok s₁ reads₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [args₁ 0 (by decide)] at key₂
  rw [args₁ 1 (by decide)] at data₂
  rw [args₁ 2 (by decide)] at count₂ flag₂
  rw [g₁, buf₀] at buf₂
  obtain sp₂ := (keep₂.reg .esp (by decide)).trans sp₁
  obtain rd₂ := keep₂.rd.trans (keep₁.rd.trans keep₀.rd)
  obtain wr₂ := keep₂.wr.trans (keep₁.wr.trans keep₀.wr)
  obtain mem₂ : s₂.mem = savedMem s₀ := keep₂.mem.trans keep₁.mem
  obtain scratchFrame : Frame [⟨addr32 (arg s 3), 1024⟩] s.mem s₂.mem := by
    rw [mem₂, ← keep₀.mem, ← buf₀]; exact savedMem_frame s₀
  obtain initialKey := VG.Proof.TripleDes.scheduleAt_eq_of_frame (addr32 (arg s 0)) scratchFrame
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact keyBuf)
  obtain initialData := VG.Proof.TripleDes.blocksAt_frame scratchFrame (addr32 (arg s 1)) (arg s 2).toNat
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact dataBuf)
  obtain hp₂ : StepPre s₂ (arg s 2).toNat := by
    constructor
    · simp only [Covers, keyR, dataR, bufR, key₂, data₂, buf₂, rd₂, wr₂, rd, wr]
      intro a n ⟨r, hr, hc⟩
      exact ⟨r, by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with h | h | h <;> simp_all only [or_true, true_or], hc⟩
    · simp only [dataR, bufR, data₂, buf₂, wr₂, wr]
      exact fun _ _ h => h
    · simpa only [keyR, dataR, key₂, data₂] using keyData
    · simpa only [keyR, bufR, key₂, buf₂] using keyBuf
    · simpa only [dataR, bufR, data₂, buf₂] using dataBuf
    · rw [key₂]; exact keyFit
    · rw [data₂]; exact fit
    · rw [buf₂]; exact bufFit
    · rw [sp₂]; exact stackLo
    · simpa only [keyR, sp₂, key₂] using stackKey
    · simpa only [dataR, sp₂, data₂] using stackData
    · simpa only [bufR, sp₂, buf₂] using stackBuf
  apply WP.seq
  apply WP.mono (maybeLoop_ok d s₂ (arg s 2).toNat (by omega_using [fit]) hp₂
    (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using count₂)
    (flag₂.trans (congrArg some (counter_zero (arg s 2)))))
  intro s₃ h₃
  obtain rd₃ := h₃.rd.trans rd₂
  obtain wr₃ := h₃.wr.trans wr₂
  obtain buf₃ := (h₃.reg .ebp (by decide) (by decide) (by decide)).trans buf₂
  obtain reads₃ : ∀ k ∈ [512, 516, 520, 524], InRegions (s₃.rd ++ s₃.wr) (addr (s₃.gpr .ebp) k) 4 := by
    intro k hk
    obtain bound : k + 4 ≤ 1024 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> decide
    rw [rd₃, wr₃, buf₃, addr_eq (by omega_using [bufFit, bound])]
    obtain ⟨r, hr, hc⟩ := writes k bound
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain stored₃ : ∀ i < 4, s₃.mem.readW (addr (s₃.gpr .ebp) (512 + 4 * i)) 32 = s.gpr (savedReg i) := by
    intro i hi
    obtain h := h₃.saved i hi
    rw [buf₂, mem₂, ← buf₀, savedMem_read s₀ i hi] at h
    rw [buf₀] at h
    rw [buf₃, addr_eq (by omega_using [bufFit, hi])]
    obtain reg : savedReg i ≠ .eax := (show ∀ i < 4, savedReg i ≠ .eax by decide) i hi
    exact h.trans (g₀ _ reg)
  obtain ⟨s₄, run₄, saved₄, keep₄⟩ := restore_ok s s₃ reads₃ stored₃
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  constructor
  · constructor
    · intro r hr
      obtain regs : ∀ r ∈ calleeSaved, r ∈ savedRegs ∨ r = .esp := by decide
      rcases regs r hr with saved | rfl
      · exact saved₄ r saved
      · rw [keep₄.reg .esp (by decide), h₃.reg .esp (by decide) (by decide) (by decide), sp₂]
    · have stackRet : (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint (below (s.gpr .esp) 16) := by
        change (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint ⟨_, 16⟩
        rw [VG.X86.Taint.sub_setWidth stackLo]
        exact Offset.base_disjoint_below _ (by decide)
      obtain retSep : ∀ r ∈ loopWrites s₂ (arg s 2).toNat, (Region.mk (addr32 (s.gpr .esp)) 4).Disjoint r := by
        simpa only [loopWrites, dataR, bufR, data₂, buf₂, sp₂,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
          And.intro retData (And.intro retBuf stackRet)
      change s₄.mem.readW (addr32 (s.gpr .esp)) 32 = s.mem.readW (addr32 (s.gpr .esp)) 32
      rw [keep₄.mem, h₃.mem.readW (Region.contains_self _ _) retSep (by decide),
        scratchFrame.readW (Region.contains_self _ _) (by
          intro r hr; obtain rfl := List.mem_singleton.mp hr; exact retBuf) (by decide)]
  · have out := h₃.blocks
    rw [key₂, data₂, initialKey, initialData] at out
    change Spec.TripleDes.blocksAt s₄.mem (addr32 (arg s 1)) (arg s 2).toNat = _
    rw [keep₄.mem]; exact out

end VG.Proof.TripleDes.X86.Ecb

end

/-! ## `ConstantTime` -/

section

namespace VG.Proof.TripleDes.X86.Ecb
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)

theorem ecbTaint_wf {d : Spec.TripleDes.Direction} {s : State} (hs : (contract d).pre s) : VG.X86.Taint.Wf ecbTaint s := by
  obtain ⟨_, hwr, _, _, dataSep, argsData, argsScratch, retData, retScratch, _, stackData, stackBuf, _, scratchFit, spFit, stackLo, dataFit⟩ := hs
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨spFit, ?_⟩, ?_⟩ ?_
  · rw [hwr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨dataSep, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr32, BitVec.toNat_setWidth] <;> omega_arith
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [spFit]) retData argsData
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [spFit]) retScratch argsScratch
  · intro p hp
    simp only [ecbTaint, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, addr32, arg, argAddr]
  · intro _
    refine ⟨stackLo, ?_⟩
    intro r hr
    obtain e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16 =
        (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 := (VG.X86.Taint.sub_setWidth stackLo).symm
    change (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16, 16⟩ : Region).Disjoint r
    rw [e]
    simp only [hwr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact stackData
    · exact stackBuf

theorem ecbTaint_agree {d : Spec.TripleDes.Direction} {s t : State} (hs : (contract d).pre s)
    (ht : (contract d).pre t) (hp : (contract d).pub s t) :
    VG.X86.Taint.Agree ecbTaint s t := by
  obtain ⟨sp, args⟩ := hp
  obtain fit : ∀ s, (contract d).pre s → (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 := by
    intro s hs; obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _, _⟩ := hs; exact h
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, ecbTaint_wf hs,
    ecbTaint_wf ht, VG.X86.Taint.slotsOk_empty,
    VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [ecbTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · rw [hs.2.1, ht.2.1, args 1 (by decide), args 2 (by decide), args 3 (by decide)]
  · simp only [ecbTaint] at hk
    rw [show VG.X86.Taint.depth ecbTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (fit _ hs) h4 hk, VG.X86.Taint.argByte_eq (fit _ ht) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega_using [hk]))

end VG.Proof.TripleDes.X86.Ecb

end

/-! ## `Verified` -/

section

namespace VG.Proof.TripleDes.X86.Ecb
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)

def wideContract (d : Spec.TripleDes.Direction) : Contract isa :=
  { contract d with
    pre := fun s =>
    let key : Region := ⟨addr32 (arg s 0), 384⟩
    let data : Region := ⟨addr32 (arg s 1), 8 * (arg s 2).toNat⟩
    let buf : Region := ⟨addr32 (arg s 3), 1024⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨addr32 (s.gpr .esp), 4⟩
    let stack := below (s.gpr .esp) 16
    s.rd = [key] ∧ s.wr = [data, buf, args] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧ args.Disjoint data ∧ args.Disjoint buf ∧
      ret.Disjoint data ∧ ret.Disjoint buf ∧ stack.Disjoint key ∧ stack.Disjoint data ∧
      stack.Disjoint buf ∧ (arg s 0).toNat + 384 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 1024 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
      16 ≤ (s.gpr .esp).toNat ∧ (arg s 1).toNat + 8 * (arg s 2).toNat ≤ 2 ^ 32 }

def narrowRd (s : State) : List Region := [⟨addr32 (arg s 0), 384⟩, ⟨argAddr s 0, 16⟩]
def narrowWr (s : State) : List Region :=
  [⟨addr32 (arg s 1), 8 * (arg s 2).toNat⟩, ⟨addr32 (arg s 3), 1024⟩]

tactic_template "tdes_ecb_narrow" : tactic =>
  `(tactic| simp only [VG.Proof.TripleDes.X86.Ecb.contract, VG.Proof.TripleDes.X86.Ecb.wideContract,
                     VG.Proof.TripleDes.X86.Ecb.narrowRd, VG.Proof.TripleDes.X86.Ecb.narrowWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr])

tactic_template "tdes_ecb_narrow" loc:Lean.Parser.Tactic.location : tactic =>
  `(tactic| simp only [VG.Proof.TripleDes.X86.Ecb.contract, VG.Proof.TripleDes.X86.Ecb.wideContract,
                     VG.Proof.TripleDes.X86.Ecb.narrowRd, VG.Proof.TripleDes.X86.Ecb.narrowWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $loc)

theorem wide_pre (d : Spec.TripleDes.Direction) (s : State) (h : (wideContract d).pre s) :
    (contract d).pre (s.withRegions (narrowRd s) (narrowWr s)) := by
  obtain ⟨_, _, h⟩ := h
  tdes_ecb_narrow
  exact ⟨trivial, trivial, h⟩

def satState : State where
  gpr r := if r = .esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else if a = 0x4011 then 0x30 else 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 1024⟩, ⟨0x4004, 16⟩]

theorem wide_implies (d : Spec.TripleDes.Direction) :
    (wideContract d).Implies (Proof.TripleDes.ecbScratchContract abi d 16) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.TripleDes.ecbScratchContract, Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argSlots, argVal, argBytes, addr32, wideContract, contract, below] at h
    sig_split h
    sig_reduce [Proof.TripleDes.ecbScratchContract, Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argSlots, argVal, argBytes, addr32, wideContract, contract, below]
    sig_simp [Proof.TripleDes.ecbScratchContract, Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argSlots, argVal, argBytes, addr32, wideContract, contract, below] []
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (rw [Taint.sub_setWidth (by omega_arith)]; simp only [Nat.mul_comm] at *; with_reducible assumption)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.TripleDes.ecbScratchContract, Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argSlots, argVal, argBytes, addr32, wideContract, contract, below]
  · sig_implies_pub [Proof.TripleDes.ecbScratchContract, Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argSlots, argVal, argBytes, addr32, wideContract, contract, below]
  · sig_implies_sat [Proof.TripleDes.ecbScratchContract, Proof.TripleDes.ecbScratchSig, Spec.TripleDes.ecbPost, abi, argSlots, argVal, argBytes, addr32, wideContract, contract, below]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem ecb_constantTime (d : Spec.TripleDes.Direction) :
    ConstantTime isa (contract d).pre (contract d).pub (Impl.TripleDes.X86.Ecb.ecb d) := by
  cases d
  · exact ecbEncrypt_constantTime _ _ (fun _ _ h₁ h₂ hp => ecbTaint_agree h₁ h₂ hp)
  · exact ecbDecrypt_constantTime _ _ (fun _ _ h₁ h₂ hp => ecbTaint_agree h₁ h₂ hp)

theorem ecb_verified (d : Spec.TripleDes.Direction) :
    Verified target (Impl.TripleDes.X86.Ecb.ecb d) (Proof.TripleDes.ecbScratchContract abi d 16) := by
  obtain hsat := (wide_implies d).sat_left
  obtain narrowSat : ∃ s, (contract d).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wide_pre d s hs⟩
  apply Verified.of_implies _ (wide_implies d)
  refine Verified.narrowTo
    (Verified.of_correct (ecb_correct d) (ecb_constantTime d) (.refl narrowSat))
    narrowRd narrowWr (wide_pre d) ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp_all only [or_true, true_or]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp_all only [or_true, true_or]
  · intro s s' _ h
    tdes_ecb_narrow at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    tdes_ecb_narrow
    exact h

end VG.Proof.TripleDes.X86.Ecb

end
