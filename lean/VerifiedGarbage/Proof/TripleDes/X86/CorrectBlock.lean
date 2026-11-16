module

public import VerifiedGarbage.Proof.TripleDes.X86.RoundStep
public import VerifiedGarbage.Proof.TripleDes.Core
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import Batteries.Logic
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.TripleDes.X86.Save
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.TripleDes.X86.RestoredOutput
import VerifiedGarbage.Proof.Rc2.X86.BlockArgs
import VerifiedGarbage.Proof.TripleDes.X86.WordStore
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.X86.Bytes
import VerifiedGarbage.Proof.Rc2.X86.KeyIO
import VerifiedGarbage.Proof.Framework.X86.Taint

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
