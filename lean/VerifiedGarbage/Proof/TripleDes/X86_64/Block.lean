module

import VerifiedGarbage.Proof.TripleDes.X86_64.BlockIO
public import VerifiedGarbage.Proof.TripleDes.X86_64.Save
public import VerifiedGarbage.Proof.TripleDes.X86_64.Ready
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.TripleDes.X86_64.RoundLit
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Impl.TripleDes.X86_64.Block
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Proof.TripleDes.X86_64.Initial
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
public import VerifiedGarbage.Proof.TripleDes.X86_64.WordState
import VerifiedGarbage.Proof.TripleDes.X86_64.Bytes
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `TripleDes.X86_64.Head`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

def saveRegion (s : State) : Region := ⟨s.gpr .rdx, 56⟩

structure HeadPre (keys : Nat → DesSchedule) (base : Addr) (s : State) : Prop where
  spills : Ok sboxCfg s
  pointer : s.gpr .rdi = base
  saveRead : ∀ i < 7, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8
  saveWrite : ∀ i < 7, InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8
  countRead : InRegions (s.rd ++ s.wr) (countAddr s) 8
  countWrite : InRegions s.wr (countAddr s) 8
  stepWrite : InRegions s.wr (stepAddr s) 8
  passesRead : InRegions (s.rd ++ s.wr) (passesAddr s) 8
  passesWrite : InRegions s.wr (passesAddr s) 8
  dataRead : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 8
  dataSeparate : (⟨s.gpr .rsi, 8⟩ : Region).Disjoint (saveRegion s)
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    InRegions (s.rd ++ s.wr) (keyAddr (componentBase base c) d j) 8
  separateWork : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (⟨keyAddr (componentBase base c) d j, 8⟩ : Region).Disjoint (workRegion s)
  separateSave : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (⟨keyAddr (componentBase base c) d j, 8⟩ : Region).Disjoint (saveRegion s)
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (s.mem.readW (keyAddr (componentBase base c) d j) 64).setWidth 48 = roundKey (keys c) d j

structure HeadPost (keys : Nat → DesSchedule) (base : Addr) (original s : State) : Prop where
  word : WordState (Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt original.mem (original.gpr .rsi)))) s
  ready : Ready keys base s
  saved : Saved original s
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  regs : ∀ q ∈ [Reg.rdi, .rsi, .rdx, .rsp], s.gpr q = original.gpr q
  frame : Frame [saveRegion original] original.mem s.mem

theorem ready_afterSave {keys : Nat → DesSchedule} {base : Addr} {s t : State}
    (hp : HeadPre keys base s) (hg : t.gpr = s.gpr) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (hsaved : Saved s t) (hf : Frame [saveRegion s] s.mem t.mem) :
    Ready keys base t := by
  have hbase : t.gpr .rdx = s.gpr .rdx := congrFun hg .rdx
  refine ⟨hp.spills.congr hbase hbase hrd hwr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hsaved 6 (by decide)).trans hp.pointer
  · rw [hrd, hwr, show savedKeyAddr t = savedKeyAddr s from congrArg (· + BitVec.ofNat 64 48) hbase]
    exact hp.saveRead 6 (by decide)
  · rw [hrd, hwr, show countAddr t = countAddr s from congrArg (· + BitVec.ofNat 64 56) hbase]
    exact hp.countRead
  · rw [hwr, show countAddr t = countAddr s from congrArg (· + BitVec.ofNat 64 56) hbase]
    exact hp.countWrite
  · rw [hwr, show stepAddr t = stepAddr s from congrArg (· + BitVec.ofNat 64 448) hbase]
    exact hp.stepWrite
  · rw [hrd, hwr, show passesAddr t = passesAddr s from congrArg (· + BitVec.ofNat 64 456) hbase]
    exact hp.passesRead
  · rw [hwr, show passesAddr t = passesAddr s from congrArg (· + BitVec.ofNat 64 456) hbase]
    exact hp.passesWrite
  · rw [hrd, hwr]; exact hp.read
  · rw [show workRegion t = workRegion s from
      congrArg (fun p => (⟨p + BitVec.ofNat 64 56, 408⟩ : Region)) hbase]
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
  have hready := ready_afterSave hp hs₁.1 hs₁.2.1 hs₁.2.2.1 hs₁.2.2.2.1 hs₁.2.2.2.2
  have hread₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsi) 8 := by
    rw [hs₁.2.1, hs₁.2.2.1, hs₁.1]; exact hp.dataRead
  have hdata : Spec.TripleDes.blockAt s₁.mem (s₁.gpr .rsi) =
      Spec.TripleDes.blockAt s.mem (s.gpr .rsi) := by
    rw [hs₁.1]
    exact VG.Proof.TripleDes.blockAt_eq_of_frame _ hs₁.2.2.2.2
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.dataSeparate)
  obtain ⟨s₂, run₂, left₂, right₂, mem₂, rd₂, wr₂, regs₂⟩ := blockLoad_ok s₁ hread₁
  have hframe : Frame [workRegion s₁] s₁.mem s₂.mem := by
    rw [mem₂]; exact Frame.refl _ _
  have hinput := congrArg (fun b => Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock b)) hdata
  apply WP.of_runBlock
  refine ⟨s₂, run₂, ?_, hready.congr (regs₂ .rdx (by decide)) rd₂ wr₂ hframe,
    hs₁.2.2.2.1.congr (regs₂ .rdx (by decide)) hframe,
    rd₂.trans hs₁.2.1, wr₂.trans hs₁.2.2.1, ?_, ?_⟩
  · exact ⟨left₂.trans (congrArg (fun x : BitVec 64 => ((x >>> 32).setWidth 32).setWidth 64) hinput),
      right₂.trans (congrArg (fun x : BitVec 64 => (x.setWidth 32).setWidth 64) hinput)⟩
  · intro q hq
    exact (regs₂ q hq).trans (congrFun hs₁.1 q)
  · rw [mem₂]; exact hs₁.2.2.2.2

end VG.Proof.TripleDes.X86_64

end

end

/-! ### `TripleDes.X86_64.Body`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64
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

theorem passesInit_ok (s : State) (hwrite : InRegions s.wr (passesAddr s) 8) :
    ∃ s', runBlock isa [imm .rax 3, .store (memOp .rdx 456) .rax] s = some s' ∧
      s'.mem = s.mem.writeW (passesAddr s) (BitVec.ofNat 64 3) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) := by
  unfold passesAddr at hwrite
  have hoff : BitVec.ofInt 64 (Int.ofNat 456) = BitVec.ofNat 64 456 := rfl
  refine ⟨_, by
    simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.ea,
      memOp, hoff, State.store64, gpr_setReg, mem_setReg, wr_setReg, reduceCtorEq,
      ite_false, ite_true, hwrite, Option.map_some]
    rfl, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · intro r hr
    simp only [gpr_setReg, hr, ite_false]

/-- The loop's invariant, with `m` passes left. -/
structure BodyInv (keys : Nat → DesSchedule) (base : Addr) (direction : Direction)
    (x : BitVec 64) (origin : State) (m : Nat) (s : State) : Prop where
  pos : 1 ≤ m
  le : m ≤ 3
  passes : s.mem.readW (passesAddr s) 64 = BitVec.ofNat 64 m
  word : WordState (passesDone keys direction x (3 - m)) s
  ready : Ready keys base s
  stable : Stable origin s

theorem blockBody_ok (keys : Nat → DesSchedule) (base : Addr) (s : State) (x : BitVec 64)
    (direction : Direction) (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (blockBody direction) s
      (fun t => WordState (blockCore keys direction x) t ∧ Ready keys base t ∧ Stable s t) := by
  obtain ⟨s₁, run₁, mem₁, rd₁, wr₁, regs₁⟩ := passesInit_ok s hready.passesWrite
  have hbase : s₁.gpr .rdx = s.gpr .rdx := regs₁ .rdx (by decide)
  have hframe : Frame [workRegion s] s.mem s₁.mem := by
    rw [mem₁]
    exact (countWrite_frame _ _ _).sub (by
      intro q hq
      obtain rfl := List.mem_singleton.mp hq
      exact ⟨_, List.mem_singleton_self _, passes_sub_work s⟩)
  have hstable : Stable s s₁ := ⟨rd₁, wr₁, fun q hq => regs₁ q (by revert hq; cases q <;> decide),
    hframe⟩
  apply WP.seq
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  refine WP.loop (M := isa) (BodyInv keys base direction x s) ?_ 3 s₁
    ⟨by decide, by decide, ?_, ?_, hready.congr hbase rd₁ wr₁ hframe, hstable⟩
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
  · rw [show passesAddr s₁ = passesAddr s from congrArg (· + BitVec.ofNat 64 456) hbase, mem₁]
    exact Mem.readW_writeW_self64 _ _ _
  · exact ⟨(regs₁ .r12 (by decide)).trans hword.left, (regs₁ .r13 (by decide)).trans hword.right⟩

end VG.Proof.TripleDes.X86_64

end

end

/-! ### `TripleDes.X86_64.Tail`, which only this module used -/

section

/-! ### `TripleDes.X86_64.Store`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64

theorem packHalves_ok (s : State) :
    ∃ s', runBlock isa [rr .rax .r12, .shift .ror .rax 32, .alu .xor .rax (.reg .r13)] s = some s' ∧
      s'.gpr .rax = (s.gpr .r12).rotateRight 32 ^^^ s.gpr .r13 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [rr, runBlock_cons, runStep_some, reduceExec, execShift,
      readSrc, Option.map_some, gpr_setReg, ite_true]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact gpr_setReg_self _ _ _
  · simp only [mem_setReg, mem_setFlags, mem_arithFlags]
  · simp only [rd_setReg, rd_setFlags, rd_arithFlags]
  · simp only [wr_setReg, wr_setFlags, wr_arithFlags]
  · intro r hr
    simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, hr, ite_false]

theorem storeTail_ok (s : State) :
    ∃ s', runBlock isa [.bswap .rbx, rr .rax .rbx] s = some s' ∧
      s'.gpr .rax = bswap64 (s.gpr .rbx) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [rr, runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc,
      Option.map_some, gpr_setReg_self]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact gpr_setReg_self _ _ _
  · simp only [mem_setReg]
  · simp only [rd_setReg]
  · simp only [wr_setReg]
  · intro r hrax hrbx
    simp only [gpr_setReg, hrax, hrbx, ite_false]


theorem blockStore_run (s s₁ s₂ s₃ : State)
    (h₁ : runBlock isa [rr .rax .r12, .shift .ror .rax 32, .alu .xor .rax (.reg .r13)] s = some s₁)
    (h₂ : runBlock isa (permuteCode Spec.TripleDes.fp 64 .rbx .rax .rbp) s₁ = some s₂)
    (h₃ : runBlock isa [.bswap .rbx, rr .rax .rbx] s₂ = some s₃) :
    runBlock isa blockStore s = some s₃ := by
  have hhead := runAppend_some _ _ _ _ _ h₁ h₂
  have htail := runAppend_some _ _ _ _ _ hhead h₃
  have hcode : blockStore =
      (([rr .rax .r12, .shift .ror .rax 32, .alu .xor .rax (.reg .r13)] : List Instr) ++
        permuteCode Spec.TripleDes.fp 64 .rbx .rax .rbp) ++ [.bswap .rbx, rr .rax .rbx] := rfl
  exact (congrArg (fun is => runBlock isa is s) hcode).trans htail

theorem blockStore_ok (s : State) (l r : BitVec 32)
    (hl : s.gpr .r12 = l.setWidth 64) (hr : s.gpr .r13 = r.setWidth 64) :
    ∃ s', runBlock isa blockStore s = some s' ∧
      s'.gpr .rax = bswap64 (Spec.TripleDes.permute Spec.TripleDes.fp (l ++ r)) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q ∈ [Reg.rdi, .rsi, .rdx, .rsp], s'.gpr q = s.gpr q) := by
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, regs₁⟩ := packHalves_ok s
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, mem₂, regs₂⟩ := final_raw_ok s₁
  obtain ⟨s₃, run₃, word₃, mem₃, rd₃, wr₃, regs₃⟩ := storeTail_ok s₂
  have hword : s₁.gpr .rax = l ++ r := by
    rw [hl, hr] at word₁
    exact word₁.trans (VG.Proof.TripleDes.packHalves_word l r)
  refine ⟨s₃, blockStore_run s s₁ s₂ s₃ run₁ run₂ run₃, ?_,
    mem₃.trans (mem₂.trans mem₁), rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), ?_⟩
  · exact word₃.trans (congrArg bswap64 (word₂.trans
      (congrArg (Spec.TripleDes.permute Spec.TripleDes.fp) hword)))
  · intro q hq
    have hneq : ∀ q ∈ [Reg.rdi, .rsi, .rdx, .rsp], q ≠ .rax ∧ q ≠ .rbx ∧ q ≠ .rbp := by decide
    have hdst : (instrs finalPermutation.lit).all
        (fun op => op.dst == some Reg.rbx || op.dst == some Reg.rbp) = true := by decide +kernel
    have hno : (instrs finalPermutation.lit).all (fun op => op.dst != some q) = true := by
      apply List.all_eq_true.mpr
      intro op hop
      have h := List.all_eq_true.mp hdst op hop
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h
      · rw [h, bne_iff_ne]
        intro he
        exact (hneq q hq).2.1 (Option.some.inj he).symm
      · rw [h, bne_iff_ne]
        intro he
        exact (hneq q hq).2.2 (Option.some.inj he).symm
    exact (regs₃ q (hneq q hq).1 (hneq q hq).2.1).trans
      ((regs₂ q hno).trans (regs₁ q (hneq q hq).1))


theorem writeData_ok (s : State) (hwrite : InRegions s.wr (s.gpr .rsi) 8) :
    ∃ s', runBlock isa [.store (memOp .rsi 0) .rax] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .rsi) (s.gpr .rax) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have haddr : s.gpr .rsi + BitVec.ofInt 64 (Int.ofNat 0) = s.gpr .rsi := BitVec.add_zero _
  refine ⟨{ s with mem := s.mem.writeW (s.gpr .rsi) (s.gpr .rax) }, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, State.store64,
      State.ea, memOp, haddr, hwrite, ite_true], rfl, rfl, rfl, rfl⟩

end VG.Proof.TripleDes.X86_64

end

end


@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.Impl.TripleDes.X86_64

structure TailPost (original origin : State) (x : BitVec 64) (s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (origin.gpr .rsi) =
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp x)
  saved : ∀ r ∈ savedRegs ++ [Reg.rdi], s.gpr r = original.gpr r
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s.gpr q = origin.gpr q
  frame : Frame [⟨origin.gpr .rsi, 8⟩] origin.mem s.mem

theorem blockTail_ok (original s : State) (x : BitVec 64)
    (hword : WordState x s) (hsaved : Saved original s)
    (hsavedRead : ∀ i < 7, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8)
    (hwrite : InRegions s.wr (s.gpr .rsi) 8) :
    WP isa (.block (blockStore ++ blockRestore ++ ([.store (memOp .rsi 0) .rax] : List Instr)))
      s (TailPost original s x) := by
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, regs₁⟩ :=
    blockStore_ok s ((x >>> 32).setWidth 32) (x.setWidth 32) hword.left hword.right
  have word : s₁.gpr .rax = bswap64 (Spec.TripleDes.permute Spec.TripleDes.fp x) :=
    word₁.trans (congrArg (fun v => bswap64 (Spec.TripleDes.permute Spec.TripleDes.fp v))
      (VG.Proof.TripleDes.halves_append x))
  have saved₁ : Saved original s₁ := by
    intro i hi
    rw [regs₁ .rdx (by decide), mem₁]
    exact hsaved i hi
  have savedRead₁ : ∀ i < 7, InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8 := by
    rw [rd₁, wr₁, regs₁ .rdx (by decide)]
    exact hsavedRead
  apply WP.block_append
  apply WP.block_append
  apply WP.of_runBlock
  refine ⟨s₁, run₁, ?_⟩
  apply WP.mono (blockRestore_ok original s₁ saved₁ savedRead₁)
  intro s₂ hs₂
  have hnonsaved : ∀ q ∈ [Reg.rax, .rsi, .rdx, .rsp], q ∉ savedRegs ++ [Reg.rdi] := by decide
  have hrax₂ : s₂.gpr .rax = bswap64 (Spec.TripleDes.permute Spec.TripleDes.fp x) :=
    (hs₂.2.reg .rax (hnonsaved .rax (by decide))).trans word
  have hregs₂ : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s₂.gpr q = s.gpr q := by
    intro q hq
    have hkeep : ∀ r ∈ [Reg.rsi, .rdx, .rsp], r ∈ [Reg.rax, .rsi, .rdx, .rsp] ∧
      r ∈ [Reg.rdi, .rsi, .rdx, .rsp] := by decide
    exact (hs₂.2.reg q (hnonsaved q (hkeep q hq).1)).trans (regs₁ q (hkeep q hq).2)
  have hwrite₂ : InRegions s₂.wr (s₂.gpr .rsi) 8 := by
    rw [hs₂.2.wr, wr₁, hregs₂ .rsi (by decide)]
    exact hwrite
  obtain ⟨s₃, run₃, mem₃, gpr₃, rd₃, wr₃⟩ := writeData_ok s₂ hwrite₂
  apply WP.of_runBlock
  refine ⟨s₃, run₃, ?_, ?_, rd₃.trans (hs₂.2.rd.trans rd₁),
    wr₃.trans (hs₂.2.wr.trans wr₁), ?_, ?_⟩
  · rw [mem₃, hs₂.2.mem, mem₁, hregs₂ .rsi (by decide), hrax₂]
    exact blockAt_writeW s.mem (s.gpr .rsi) (Spec.TripleDes.permute Spec.TripleDes.fp x)
  · intro r hr
    rw [gpr₃]
    exact hs₂.1 r hr
  · intro q hq
    rw [gpr₃]
    exact hregs₂ q hq
  · rw [mem₃, hs₂.2.mem, mem₁, hregs₂ .rsi (by decide)]
    exact countWrite_frame s.mem (s.gpr .rsi) (s₂.gpr .rax)

end VG.Proof.TripleDes.X86_64

end

end


@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.Impl.TripleDes.X86_64
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

def blockRegions (s : State) : List Region := [⟨s.gpr .rsi, 8⟩, ⟨s.gpr .rdx, 512⟩]

structure BlockPost (keys : Schedule) (direction : Direction) (original s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (original.gpr .rsi) =
    blockResult keys direction (Spec.TripleDes.blockAt original.mem (original.gpr .rsi))
  saved : ∀ r ∈ savedRegs ++ [Reg.rdi], s.gpr r = original.gpr r
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  regs : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s.gpr q = original.gpr q
  frame : Frame (blockRegions original) original.mem s.mem

theorem block_ok (keys : Schedule) (base : Addr) (direction : Direction) (s : State)
    (hp : HeadPre (Spec.TripleDes.componentSchedule keys) base s)
    (hwrite : InRegions s.wr (s.gpr .rsi) 8) :
    WP isa (block direction) s (BlockPost keys direction s) := by
  apply WP.seq
  apply WP.mono (blockHead_ok (Spec.TripleDes.componentSchedule keys) base s hp)
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (blockBody_ok (Spec.TripleDes.componentSchedule keys) base s₁ _ direction hs₁.ready hs₁.word)
  intro s₂ hs₂
  have hregs₂ : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s₂.gpr q = s.gpr q := by
    intro q hq
    have hkeep : ∀ r ∈ [Reg.rsi, .rdx, .rsp], r ∈ [Reg.rdi, .rsi, .rdx, .rsp] := by decide
    exact (hs₂.2.2.regs q hq).trans (hs₁.regs q (hkeep q hq))
  have saved₂ := hs₁.saved.congr (hs₂.2.2.regs .rdx (by decide)) hs₂.2.2.frame
  have savedRead₂ : ∀ i < 7, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8 := by
    rw [hs₂.2.2.rd, hs₂.2.2.wr, hs₁.rd, hs₁.wr, hregs₂ .rdx (by decide)]
    exact hp.saveRead
  have hwrite₂ : InRegions s₂.wr (s₂.gpr .rsi) 8 := by
    rw [hs₂.2.2.wr, hs₁.wr, hregs₂ .rsi (by decide)]
    exact hwrite
  apply WP.mono (blockTail_ok s s₂ _ hs₂.1 saved₂ savedRead₂ hwrite₂)
  intro s₃ hs₃
  refine ⟨?_, hs₃.saved, hs₃.rd.trans (hs₂.2.2.rd.trans hs₁.rd),
    hs₃.wr.trans (hs₂.2.2.wr.trans hs₁.wr),
    fun q hq => (hs₃.regs q hq).trans (hregs₂ q hq), ?_⟩
  · have hresult := hs₃.result
    rw [hregs₂ .rsi (by decide)] at hresult
    exact hresult.trans (blockResult_core keys direction _)
  · have hf₁ : Frame (blockRegions s) s.mem s₁.mem := hs₁.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨⟨s.gpr .rdx, 512⟩, by simp [blockRegions], Region.sub_prefix (by decide)⟩)
    have hf₂ : Frame (blockRegions s) s₁.mem s₂.mem := hs₂.2.2.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨⟨s.gpr .rdx, 512⟩, by simp [blockRegions], ?_⟩
      have hbase := hs₁.regs .rdx (by decide)
      change Region.Sub ⟨s₁.gpr .rdx + BitVec.ofNat 64 56, 408⟩ ⟨s.gpr .rdx, 512⟩
      rw [hbase]
      exact Offset.sub_base _ (by decide))
    have hf₃ : Frame (blockRegions s) s₂.mem s₃.mem := hs₃.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      rw [hregs₂ .rsi (by decide)]
      exact ⟨⟨s.gpr .rsi, 8⟩, by simp [blockRegions], fun _ h => h⟩)
    exact hf₁.trans (hf₂.trans hf₃)

end VG.Proof.TripleDes.X86_64
