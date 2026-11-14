module

public import VerifiedGarbage.Proof.TripleDes.AArch64.BlockIO
public import VerifiedGarbage.Proof.TripleDes.AArch64.Save
public import VerifiedGarbage.Proof.TripleDes.AArch64.Ready
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.AArch64.RoundLit
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.TripleDes.AArch64.Initial
import VerifiedGarbage.Proof.TripleDes.AArch64.Word
import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Proof.TripleDes.AArch64.WordState
import VerifiedGarbage.Proof.TripleDes.AArch64.Bytes
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.TripleDes.Schedule
public import VerifiedGarbage.Proof.TripleDes.AArch64.ConstantTime
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.TripleDes.AArch64.FunctionsLit

/-! ### `TripleDes.AArch64.Block`, which only this module used -/

section

/-! ### `TripleDes.AArch64.Head`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.TripleDes.AArch64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

def saveRegion (s : State) : Region := ⟨s.gpr .x2, 32⟩

structure HeadPre (keys : Nat → DesSchedule) (base : Addr) (s : State) : Prop where
  spills : Ok sboxCfg s
  pointer : s.gpr .x0 = base
  saveRead : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8
  saveWrite : ∀ i < 4, InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8
  dataRead : InRegions (s.rd ++ s.wr) (s.gpr .x1) 8
  dataSeparate : (⟨s.gpr .x1, 8⟩ : Region).Disjoint (saveRegion s)
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    InRegions (s.rd ++ s.wr) (keyAddr (componentBase base c) d j) 8
  separateWork : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (⟨keyAddr (componentBase base c) d j, 8⟩ : Region).Disjoint (spillRegion s)
  separateSave : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (⟨keyAddr (componentBase base c) d j, 8⟩ : Region).Disjoint (saveRegion s)
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (s.mem.readW (keyAddr (componentBase base c) d j) 64).setWidth 48 = roundKey (keys c) d j

structure HeadPost (keys : Nat → DesSchedule) (base : Addr) (original s : State) : Prop where
  word : WordState (Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt original.mem (original.gpr .x1)))) s
  ready : Ready keys base s
  saved : Saved original s
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  sp : s.sp = original.sp
  regs : ∀ q ∈ loadKept, s.gpr q = original.gpr q
  frame : Frame [saveRegion original] original.mem s.mem

theorem ready_afterSave {keys : Nat → DesSchedule} {base : Addr} {s t : State}
    (hp : HeadPre keys base s) (hg : t.gpr = s.gpr) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (hf : Frame [saveRegion s] s.mem t.mem) :
    Ready keys base t := by
  have hbase : t.gpr .x2 = s.gpr .x2 := congrFun hg .x2
  refine ⟨hp.spills.congr hbase hbase hrd hwr, (congrFun hg .x0).trans hp.pointer, ?_, ?_, ?_⟩
  · rw [hrd, hwr]; exact hp.read
  · rw [show spillRegion t = spillRegion s from
      congrArg (fun p => (⟨p + BitVec.ofNat 64 32, 384⟩ : Region)) hbase]
    exact hp.separateWork
  · intro c hc d j hj
    have hmem := hf.readW (a := keyAddr (componentBase base c) d j) (w := 64)
      (r := ⟨keyAddr (componentBase base c) d j, 8⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.separateSave c hc d j hj)
      (by decide)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hp.values c hc d j hj)

theorem blockHead_ok (keys : Nat → DesSchedule) (base : Addr) (s : State)
    (hp : HeadPre keys base s) :
    WP isa (.block (blockSave ++ blockLoad)) s (HeadPost keys base s) := by
  apply WP.block_append
  apply WP.mono (blockSave_ok s hp.saveWrite)
  intro s₁ hs₁
  have hready := ready_afterSave hp hs₁.gpr hs₁.rd hs₁.wr hs₁.frame
  have hread₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x1) 8 := by
    rw [hs₁.rd, hs₁.wr, hs₁.gpr]; exact hp.dataRead
  have hdata : Spec.TripleDes.blockAt s₁.mem (s₁.gpr .x1) =
      Spec.TripleDes.blockAt s.mem (s.gpr .x1) := by
    rw [hs₁.gpr]
    exact VG.Proof.TripleDes.blockAt_eq_of_frame _ hs₁.frame
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.dataSeparate)
  obtain ⟨s₂, run₂, left₂, right₂, mem₂, rd₂, wr₂, sp₂, regs₂⟩ := blockLoad_ok s₁ hread₁
  have hframe : Frame [spillRegion s₁] s₁.mem s₂.mem := by
    rw [mem₂]; exact Frame.refl _ _
  have hinput := congrArg (fun b => Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock b)) hdata
  apply WP.of_runBlock
  refine ⟨s₂, run₂, ?_, hready.congr (regs₂ .x2 (by decide)) (regs₂ .x0 (by decide)) rd₂ wr₂ hframe,
    hs₁.saved.congr (regs₂ .x2 (by decide)) hframe,
    rd₂.trans hs₁.rd, wr₂.trans hs₁.wr, sp₂.trans hs₁.sp, ?_, ?_⟩
  · exact ⟨left₂.trans (congrArg (fun x : BitVec 64 => ((x >>> 32).setWidth 32).setWidth 64) hinput),
      right₂.trans (congrArg (fun x : BitVec 64 => (x.setWidth 32).setWidth 64) hinput)⟩
  · intro q hq
    exact (regs₂ q hq).trans (congrFun hs₁.gpr q)
  · rw [mem₂]; exact hs₁.frame

end VG.Proof.TripleDes.AArch64

end

end

/-! ### `TripleDes.AArch64.Body`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (desCore)

/-- The word after the first `k` passes of the block. -/
def passesDone (keys : Nat → DesSchedule) (direction : Direction) (x : BitVec 64) :
    Nat → BitVec 64
  | 0 => x
  | k + 1 => desCore (keys (passOf direction (3 - k)).1) (passOf direction (3 - k)).2
      (passesDone keys direction x k)

def blockCore (keys : Nat → DesSchedule) (direction : Direction) (x : BitVec 64) : BitVec 64 :=
  match direction with
  | .encrypt => desCore (keys 2) .encrypt (desCore (keys 1) .decrypt (desCore (keys 0) .encrypt x))
  | .decrypt => desCore (keys 0) .decrypt (desCore (keys 1) .encrypt (desCore (keys 2) .decrypt x))

theorem blockCore_passesDone (keys : Nat → DesSchedule) (direction : Direction) (x : BitVec 64) :
    blockCore keys direction x = passesDone keys direction x 3 := by
  cases direction <;> rfl

/-- The loop's invariant, with `m` passes left. -/
structure BodyInv (keys : Nat → DesSchedule) (base : Addr) (direction : Direction)
    (x : BitVec 64) (origin : State) (m : Nat) (s : State) : Prop where
  pos : 1 ≤ m
  le : m ≤ 3
  passes : passesOf s = BitVec.ofNat 64 m
  word : WordState (passesDone keys direction x (3 - m)) s
  ready : Ready keys base s
  stable : Stable origin s

theorem blockBody_ok (keys : Nat → DesSchedule) (base : Addr) (s : State) (x : BitVec 64)
    (direction : Direction) (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (blockBody direction) s
      (fun t => WordState (blockCore keys direction x) t ∧ Ready keys base t ∧ Stable s t) := by
  let s₀ := s.write .x .x3 ((BitVec.ofNat 16 3).setWidth 64)
  let s₁ := s₀.setV .v1 (ofVDwords (s₀.gpr .x3) (s₀.gpr .x3))
  have hbase : s₁.gpr .x2 = s.gpr .x2 := by
    simp only [s₁, s₀, gpr_setV, gpr_write, reduceCtorEq, ite_false]
  have hrd : s₁.rd = s.rd := by simp only [s₁, s₀, rd_setV, rd_write]
  have hwr : s₁.wr = s.wr := by simp only [s₁, s₀, wr_setV, wr_write]
  have hsp : s₁.sp = s.sp := by simp only [s₁, s₀, sp_setV, sp_write]
  have hmem : s₁.mem = s.mem := by simp only [s₁, s₀, mem_setV, mem_write]
  have hframe : Frame [spillRegion s] s.mem s₁.mem := by rw [hmem]; exact Frame.refl _ _
  have hregs : ∀ r, r ≠ .x3 → s₁.gpr r = s.gpr r := by
    intro r hr
    simp only [s₁, s₀, gpr_setV, gpr_write, hr, ite_false]
  have hstable : Stable s s₁ := ⟨hrd, hwr, hsp,
    fun q hq => hregs q (by revert hq; cases q <;> decide), hframe⟩
  apply WP.seq
  refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
  · rw [runBlock_cons, imm, show exec (.movz .x .x3 (BitVec.ofNat 16 3) 0) s = some s₀ from rfl,
      runStep_some, runBlock_cons, show exec (.vop (.dup .d2 .v1 .x3)) s₀ = some s₁ from rfl,
      runStep_some, runBlock_nil]
  refine WP.loop (M := isa) (BodyInv keys base direction x s) ?_ 3 s₁
    ⟨by decide, by decide, ?_, ?_, hready.congr hbase (hregs .x0 (by decide)) hrd hwr hframe,
      hstable⟩
  · rintro m t ⟨hpos, hle, hpasses, hw, hr, hst⟩
    refine WP.mono (pass_word_ok keys base t _ direction ⟨hpos, hle⟩ hr hw hpasses)
      fun u ⟨hwu, hru, hsu, hpu, hzu⟩ => ?_
    have hdone : desCore (keys (passOf direction m).1) (passOf direction m).2
        (passesDone keys direction x (3 - m)) = passesDone keys direction x (3 - (m - 1)) := by
      rw [show 3 - (m - 1) = 3 - m + 1 by omega_using [hpos, hle], passesDone, show 3 - (3 - m) = m by omega_using [hle]]
    rw [hdone] at hwu
    by_cases hlast : m = 1
    · subst m
      refine Or.inl ⟨by rw [hzu]; rfl, ?_, hru, hst.trans hsu⟩
      rw [blockCore_passesDone]
      exact hwu
    · refine Or.inr ⟨by rw [hzu]; simp [hlast], m - 1, by omega_using [hpos],
        ⟨by omega_using [hpos, hlast], by omega_using [hle], hpu, hwu, hru, hst.trans hsu⟩⟩
  · rw [passesOf, v_setV_self, VG.AArch64.vdword_ofVDwords_0]
    rfl
  · exact ⟨(hregs .x19 (by decide)).trans hword.left, (hregs .x20 (by decide)).trans hword.right⟩

end VG.Proof.TripleDes.AArch64

end

end

/-! ### `TripleDes.AArch64.Tail`, which only this module used -/

section

/-! ### `TripleDes.AArch64.Store`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.TripleDes.AArch64

def packHalves : List Instr := [.lsl .x .x3 .x19 32, .logic .eor .x .x3 .x3 .x20]

theorem packHalves_ok (s : State) :
    ∃ s', runBlock isa packHalves s = some s' ∧
      s'.gpr .x3 = s.gpr .x19 <<< 32 ^^^ s.gpr .x20 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .x3 → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [packHalves, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      show (32 : Nat) < 64 from by decide, ite_true, State.read,
      BitVec.setWidth_eq, gpr_write_self]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
  · simp only [mem_write]
  · simp only [rd_write]
  · simp only [wr_write]
  · simp only [sp_write]
  · intro r hr; simp only [gpr_write, hr, ite_false]

theorem storeTail_ok (s : State) :
    ∃ s', runBlock isa [.rev .x3 .x10] s = some s' ∧
      s'.gpr .x3 = rev64 (s.gpr .x10) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .x3 → s'.gpr r = s.gpr r) := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec_rev]; rfl,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_write_self, State.read, BitVec.setWidth_eq]
  · simp only [mem_write]
  · simp only [rd_write]
  · simp only [wr_write]
  · simp only [sp_write]
  · intro r hr; simp only [gpr_write, hr, ite_false]

theorem final_preserves : loadKept.all (fun r =>
    (instrs finalPermutation.lit).all (fun op => !clobbers op r)) = true := by
  decide +kernel

theorem blockStore_ok (s : State) (l r : BitVec 32)
    (hl : s.gpr .x19 = l.setWidth 64) (hr : s.gpr .x20 = r.setWidth 64) :
    ∃ s', runBlock isa blockStore s = some s' ∧
      s'.gpr .x3 = rev64 (Spec.TripleDes.permute Spec.TripleDes.fp (l ++ r)) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ loadKept, s'.gpr q = s.gpr q) := by
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, sp₁, regs₁⟩ := packHalves_ok s
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, sp₂, mem₂, regs₂⟩ := final_raw_ok s₁
  obtain ⟨s₃, run₃, word₃, mem₃, rd₃, wr₃, sp₃, regs₃⟩ := storeTail_ok s₂
  have hword : s₁.gpr .x3 = l ++ r := by
    rw [hl, hr] at word₁
    exact word₁.trans (packHalves_shift l r)
  have hhead := runAppend_some _ _ _ _ _ run₁ run₂
  have htail := runAppend_some _ _ _ _ _ hhead run₃
  have hcode : blockStore =
      (packHalves ++ permuteCode Spec.TripleDes.fp 64 .x10 .x3 .x11 .x12) ++
      [.rev .x3 .x10] := rfl
  refine ⟨s₃, (congrArg (fun is => runBlock isa is s) hcode).trans htail, ?_,
    mem₃.trans (mem₂.trans mem₁), rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), sp₃.trans (sp₂.trans sp₁), ?_⟩
  · exact word₃.trans (congrArg rev64 (word₂.trans
      (congrArg (Spec.TripleDes.permute Spec.TripleDes.fp) hword)))
  · intro q hq
    have hno := List.all_eq_true.mp final_preserves q hq
    have hneq : q ≠ .x3 := by revert hq; cases q <;> decide
    exact (regs₃ q hneq).trans ((regs₂ q hno).trans (regs₁ q hneq))

theorem writeData_ok (s : State) (hwrite : InRegions s.wr (s.gpr .x1) 8) :
    ∃ s', runBlock isa [.str .x .x3 .x1 0] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .x1) (s.gpr .x3) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hstore := exec_str_x (t := .x3) (n := .x1) (off := 0) (by decide)
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hwrite)
  refine ⟨{s with mem := s.mem.writeW (s.gpr .x1) (s.gpr .x3)}, ?_, rfl, rfl, rfl, rfl, rfl⟩
  simp only [runBlock_cons, hstore, runStep_some, runBlock_nil, BitVec.add_zero]

end VG.Proof.TripleDes.AArch64

end

end


@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.Impl.TripleDes.AArch64

structure TailPost (original origin : State) (x : BitVec 64) (s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (origin.gpr .x1) =
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp x)
  saved : ∀ r ∈ savedRegs, s.gpr r = original.gpr r
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [⟨origin.gpr .x1, 8⟩] origin.mem s.mem

theorem blockTail_ok (original s : State) (x : BitVec 64)
    (hword : WordState x s) (hsaved : Saved original s)
    (hsavedRead : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8)
    (hwrite : InRegions s.wr (s.gpr .x1) 8) :
    WP isa (.block (blockStore ++ blockRestore ++ ([.str .x .x3 .x1 0] : List Instr)))
      s (TailPost original s x) := by
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, sp₁, regs₁⟩ :=
    blockStore_ok s ((x >>> 32).setWidth 32) (x.setWidth 32) hword.left hword.right
  have word : s₁.gpr .x3 = rev64 (Spec.TripleDes.permute Spec.TripleDes.fp x) :=
    word₁.trans (congrArg (fun v => rev64 (Spec.TripleDes.permute Spec.TripleDes.fp v))
      (VG.Proof.TripleDes.halves_append x))
  have saved₁ : Saved original s₁ := by
    intro i hi
    rw [regs₁ .x2 (by decide), mem₁]
    exact hsaved i hi
  have savedRead₁ : ∀ i < 4, InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8 := by
    rw [rd₁, wr₁, regs₁ .x2 (by decide)]
    exact hsavedRead
  apply WP.block_append
  apply WP.block_append
  apply WP.of_runBlock
  refine ⟨s₁, run₁, ?_⟩
  apply WP.mono (blockRestore_ok original s₁ saved₁ savedRead₁)
  intro s₂ hs₂
  have hnonsaved : ∀ q ∈ (.x3 :: roundStepKept), q ∉ savedRegs := by decide
  have hrax₂ : s₂.gpr .x3 = rev64 (Spec.TripleDes.permute Spec.TripleDes.fp x) :=
    (hs₂.keep.reg .x3 (hnonsaved .x3 (by decide))).trans word
  have hregs₂ : ∀ q ∈ roundStepKept, s₂.gpr q = s.gpr q := by
    intro q hq
    have hkeep : ∀ r ∈ roundStepKept, r ∈ (.x3 :: roundStepKept) ∧
      r ∈ loadKept := by decide
    exact (hs₂.keep.reg q (hnonsaved q (hkeep q hq).1)).trans (regs₁ q (hkeep q hq).2)
  have hwrite₂ : InRegions s₂.wr (s₂.gpr .x1) 8 := by
    rw [hs₂.keep.wr, wr₁, hregs₂ .x1 (by decide)]
    exact hwrite
  obtain ⟨s₃, run₃, mem₃, gpr₃, rd₃, wr₃, sp₃⟩ := writeData_ok s₂ hwrite₂
  apply WP.of_runBlock
  refine ⟨s₃, run₃, ?_, ?_, rd₃.trans (hs₂.keep.rd.trans rd₁),
    wr₃.trans (hs₂.keep.wr.trans wr₁), sp₃.trans (hs₂.sp.trans sp₁), ?_, ?_⟩
  · rw [mem₃, hs₂.keep.mem, mem₁, hregs₂ .x1 (by decide), hrax₂]
    exact blockAt_writeW s.mem (s.gpr .x1) (Spec.TripleDes.permute Spec.TripleDes.fp x)
  · intro r hr
    rw [gpr₃]
    exact hs₂.saved r hr
  · intro q hq
    rw [gpr₃]
    exact hregs₂ q hq
  · rw [mem₃, hs₂.keep.mem, mem₁, hregs₂ .x1 (by decide)]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

end VG.Proof.TripleDes.AArch64

end

end


@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.Impl.TripleDes.AArch64
open VG.Spec.TripleDes (Direction Schedule)

def blockResult (keys : Schedule) (direction : Direction) (b : Spec.TripleDes.Block) :
    Spec.TripleDes.Block :=
  match direction with
  | .encrypt => Spec.TripleDes.encryptBlock keys b
  | .decrypt => Spec.TripleDes.decryptBlock keys b

theorem blockResult_core (keys : Schedule) (direction : Direction) (b : Spec.TripleDes.Block) :
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp
      (blockCore (Spec.TripleDes.componentSchedule keys) direction
        (Spec.TripleDes.permute Spec.TripleDes.ip (Spec.TripleDes.decodeBlock b)))) =
      blockResult keys direction b := by
  cases direction
  · exact (VG.Proof.TripleDes.encryptBlock_eq_cores keys b).symm
  · exact (VG.Proof.TripleDes.decryptBlock_eq_cores keys b).symm

def blockRegions (s : State) : List Region := [⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 512⟩]

structure BlockPost (keys : Schedule) (direction : Direction) (original s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (original.gpr .x1) =
    blockResult keys direction (Spec.TripleDes.blockAt original.mem (original.gpr .x1))
  saved : ∀ r ∈ savedRegs, s.gpr r = original.gpr r
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  sp : s.sp = original.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = original.gpr q
  frame : Frame (blockRegions original) original.mem s.mem

theorem block_ok (keys : Schedule) (base : Addr) (direction : Direction) (s : State)
    (hp : HeadPre (Spec.TripleDes.componentSchedule keys) base s)
    (hwrite : InRegions s.wr (s.gpr .x1) 8) :
    WP isa (block direction) s (BlockPost keys direction s) := by
  apply WP.seq
  apply WP.mono (blockHead_ok (Spec.TripleDes.componentSchedule keys) base s hp)
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (blockBody_ok (Spec.TripleDes.componentSchedule keys) base s₁ _ direction hs₁.ready hs₁.word)
  intro s₂ hs₂
  have hregs₂ : ∀ q ∈ roundStepKept, s₂.gpr q = s.gpr q := by
    intro q hq
    have hkeep : ∀ r ∈ roundStepKept, r ∈ loadKept := by decide
    exact (hs₂.2.2.regs q hq).trans (hs₁.regs q (hkeep q hq))
  have saved₂ := hs₁.saved.congr (hs₂.2.2.regs .x2 (by decide)) hs₂.2.2.frame
  have savedRead₂ : ∀ i < 4, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8 := by
    rw [hs₂.2.2.rd, hs₂.2.2.wr, hs₁.rd, hs₁.wr, hregs₂ .x2 (by decide)]
    exact hp.saveRead
  have hwrite₂ : InRegions s₂.wr (s₂.gpr .x1) 8 := by
    rw [hs₂.2.2.wr, hs₁.wr, hregs₂ .x1 (by decide)]
    exact hwrite
  apply WP.mono (blockTail_ok s s₂ _ hs₂.1 saved₂ savedRead₂ hwrite₂)
  intro s₃ hs₃
  refine ⟨?_, hs₃.saved, hs₃.rd.trans (hs₂.2.2.rd.trans hs₁.rd),
    hs₃.wr.trans (hs₂.2.2.wr.trans hs₁.wr),
    hs₃.sp.trans (hs₂.2.2.sp.trans hs₁.sp),
    fun q hq => (hs₃.regs q hq).trans (hregs₂ q hq), ?_⟩
  · have hresult := hs₃.result
    rw [hregs₂ .x1 (by decide)] at hresult
    exact hresult.trans (blockResult_core keys direction _)
  · have hf₁ : Frame (blockRegions s) s.mem s₁.mem := hs₁.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨⟨s.gpr .x2, 512⟩, by simp [blockRegions], Region.sub_prefix (by decide)⟩)
    have hf₂ : Frame (blockRegions s) s₁.mem s₂.mem := hs₂.2.2.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨⟨s.gpr .x2, 512⟩, by simp [blockRegions], ?_⟩
      have hbase := hs₁.regs .x2 (by decide)
      change Region.Sub ⟨s₁.gpr .x2 + BitVec.ofNat 64 32, 384⟩ ⟨s.gpr .x2, 512⟩
      rw [hbase]
      exact Offset.sub_base _ (by decide))
    have hf₃ : Frame (blockRegions s) s₂.mem s₃.mem := hs₃.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      rw [hregs₂ .x1 (by decide)]
      exact ⟨⟨s.gpr .x1, 8⟩, by simp [blockRegions], fun _ h => h⟩)
    exact hf₁.trans (hf₂.trans hf₃)

end VG.Proof.TripleDes.AArch64

end

end


@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.TripleDes.AArch64
open VG.Spec.TripleDes (Direction)

def blockContract (d : Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 384⟩
    let data : Region := ⟨s.gpr .x1, 8⟩
    let scratch : Region := ⟨s.gpr .x2, 512⟩
    s.rd = [key] ∧ s.wr = [data, scratch] ∧ key.Disjoint scratch ∧ data.Disjoint scratch
  post s s' := Spec.TripleDes.blockAt s'.mem (s.gpr .x1) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (s.gpr .x0)) d (Spec.TripleDes.blockAt s.mem (s.gpr .x1))
  pub := PublicRegs [.x0, .x1, .x2]

def selectedRound (d : Direction) (j : Nat) : Nat := if d = .encrypt then j else 15 - j

theorem selectedRound_bound (d : Direction) (j : Nat) (hj : j < 16) : selectedRound d j < 16 := by
  cases d <;> simp only [selectedRound, reduceCtorEq, ite_true, ite_false] <;> omega_arith

theorem keyAddr_component (base : Addr) (c : Nat) (d : Direction) (j : Nat) :
    keyAddr (componentBase base c) d j = base + BitVec.ofNat 64 (8 * (16 * c + selectedRound d j)) := by
  unfold keyAddr componentBase selectedRound
  rw [Offset.add_ofNat_add_ofNat]
  exact congrArg (fun n => base + BitVec.ofNat 64 n) (by omega_using [])

/-- The block function's precondition, from its 512 bytes of scratch at
`x2` writable, the schedule at `x0` readable and the block at `x1`
writable, neither in the scratch. -/
theorem headPre_of (s : State)
    (scratchWrites : ∀ i < 64, InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8)
    (keyReads : ∀ i < 48, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (8 * i)) 8)
    (dataWrite : InRegions s.wr (s.gpr .x1) 8)
    (keySep : Region.Disjoint ⟨s.gpr .x0, 384⟩ ⟨s.gpr .x2, 512⟩)
    (dataSep : Region.Disjoint ⟨s.gpr .x1, 8⟩ ⟨s.gpr .x2, 512⟩) :
    HeadPre (Spec.TripleDes.componentSchedule (Spec.TripleDes.scheduleAt s.mem (s.gpr .x0)))
      (s.gpr .x0) s := by
  have inRd : ∀ {a n}, InRegions s.wr a n → InRegions (s.rd ++ s.wr) a n := fun ⟨r, h1, h2⟩ =>
    ⟨r, List.mem_append_right _ h1, h2⟩
  have spills : Ok sboxCfg s := by
    refine ⟨scratchWrites, ?_, by decide, ?_⟩
    · intro k hk; change k < 0 at hk; omega
    · intro k hk j hj; change j < 0 at hj; omega
  have keySub : ∀ c < 3, ∀ direction : Direction, ∀ j < 16,
      Region.Sub ⟨keyAddr (componentBase (s.gpr .x0) c) direction j, 8⟩ ⟨s.gpr .x0, 384⟩ := by
    intro c hc direction j hj
    rw [keyAddr_component]
    have hindex := selectedRound_bound direction j hj
    exact Offset.sub_base _ (by omega_using [hc, hindex])
  have workSub : Region.Sub (spillRegion s) ⟨s.gpr .x2, 512⟩ := Offset.sub_base _ (by decide)
  have saveSub : Region.Sub (saveRegion s) ⟨s.gpr .x2, 512⟩ := Region.sub_prefix (by decide)
  refine ⟨spills, rfl, (fun i hi => inRd (scratchWrites i (by omega_using [hi]))),
    (fun i hi => scratchWrites i (by omega_using [hi])), inRd dataWrite, dataSep.sub_right saveSub, ?_, ?_, ?_, ?_⟩
  · intro c hc direction j hj
    rw [keyAddr_component]
    exact keyReads _ (by have := selectedRound_bound direction j hj; omega_using [hc, this])
  · intro c hc direction j hj
    exact (keySep.sub_left (keySub c hc direction j hj)).sub_right workSub
  · intro c hc direction j hj
    exact (keySep.sub_left (keySub c hc direction j hj)).sub_right saveSub
  · intro c hc direction j hj
    rw [keyAddr_component]
    exact (VG.Proof.TripleDes.componentSchedule_readW s.mem (s.gpr .x0) c
      (selectedRound direction j) hc (selectedRound_bound direction j hj)).symm

theorem headPre_of_contract (d : Direction) (s : State) (hs : (blockContract d).pre s) :
    HeadPre (Spec.TripleDes.componentSchedule (Spec.TripleDes.scheduleAt s.mem (s.gpr .x0)))
      (s.gpr .x0) s := by
  obtain ⟨hrd, hwr, keySep, dataSep⟩ := hs
  refine headPre_of s (fun i hi => ?_) (fun i hi => ?_) ?_ keySep dataSep
  · rw [hwr]
    exact ⟨⟨s.gpr .x2, 512⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  · rw [hrd, hwr]
    exact ⟨⟨s.gpr .x0, 384⟩, by simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  · rw [hwr]
    exact ⟨⟨s.gpr .x1, 8⟩, by simp, Region.contains_self _ _⟩


end VG.Proof.TripleDes.AArch64
