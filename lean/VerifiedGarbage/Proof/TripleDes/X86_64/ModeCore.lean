module

import VerifiedGarbage.Proof.TripleDes.Schedule
public import VerifiedGarbage.Proof.TripleDes.X86_64.ConstantTime
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.X86_64.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.X86_64.RoundLit
public import VerifiedGarbage.Proof.Modes.X86_64.Core
import VerifiedGarbage.Proof.Modes.X86_64.Words
public import VerifiedGarbage.Impl.TripleDes.X86_64.Cbc
public import VerifiedGarbage.Proof.TripleDes.CbcBlocks
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Impl.TripleDes.X86_64.Block
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.TripleDes.X86_64.Bytes
import VerifiedGarbage.Proof.TripleDes.X86_64.Box
public import VerifiedGarbage.Proof.TripleDes.X86_64.Lit
import VerifiedGarbage.Proof.TripleDes.X86_64.Permutation
public import VerifiedGarbage.Proof.TripleDes.Core
public import VerifiedGarbage.Proof.Rc2.X86_64.Save
public import VerifiedGarbage.Proof.TripleDes.X86_64.RoundStep
import VerifiedGarbage.Proof.TripleDes.X86_64.RoundBody

/-! ### `TripleDes.X86_64.Block`, which only this module used -/

section

/-! ### `TripleDes.X86_64.Ready`, which only this module used -/

section

/-! ### `TripleDes.X86_64.WordState`, which this module and modules that import it used -/

section

/-! ### `TripleDes.X86_64.Pass`, which only this module used -/

section

/-! ### `TripleDes.X86_64.PassStart`, which only this module used -/

section

/-! ### `TripleDes.X86_64.Loop`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix feistelStep)

def keyAddr (base : Addr) (direction : Direction) (j : Nat) : Addr :=
  base + BitVec.ofNat 64 (8 * (if direction = .encrypt then j else 15 - j))

/-- The key step of a pass, in scratch slot 56. -/
def stepVal (direction : Direction) : BitVec 64 := if direction = .encrypt then 8 else -8

theorem keyAddr_step (base : Addr) (direction : Direction) (j : Nat) (hj : j < 15) :
    keyAddr base direction j + stepVal direction = keyAddr base direction (j + 1) := by
  cases direction
  · change base + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 8 =
      base + BitVec.ofNat 64 (8 * (j + 1))
    rw [Offset.add_ofNat_add_ofNat]
    exact congrArg (fun i => base + BitVec.ofNat 64 i) (by omega_using [])
  · change base + BitVec.ofNat 64 (8 * (15 - j)) + -BitVec.ofNat 64 8 =
      base + BitVec.ofNat 64 (8 * (15 - (j + 1)))
    rw [← BitVec.sub_eq_add_neg, Offset.add_ofNat_sub _ (by omega_using [hj])]
    exact congrArg (fun i => base + BitVec.ofNat 64 i) (by omega_using [])

structure LoopInv (keys : DesSchedule) (direction : Direction) (base : Addr)
    (origin : State) (v : BitVec 32 × BitVec 32) (n : Nat) (s : State) : Prop where
  positive : 1 ≤ n
  bounded : n ≤ 16
  left : s.gpr .r12 = (roundPrefix keys direction (16 - n) v).1.setWidth 64
  right : s.gpr .r13 = (roundPrefix keys direction (16 - n) v).2.setWidth 64
  counter : s.mem.readW (countAddr s) 64 = BitVec.ofNat 64 n
  pointer : s.gpr .rdi = keyAddr base direction (16 - n)
  step : s.mem.readW (stepAddr s) 64 = stepVal direction
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s.gpr q = origin.gpr q
  frame : Frame [roundRegion origin] origin.mem s.mem

structure LoopPost (keys : DesSchedule) (direction : Direction)
    (origin : State) (v : BitVec 32 × BitVec 32) (s : State) : Prop where
  left : s.gpr .r12 = (roundPrefix keys direction 16 v).1.setWidth 64
  right : s.gpr .r13 = (roundPrefix keys direction 16 v).2.setWidth 64
  counter : s.mem.readW (countAddr s) 64 = 0
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s.gpr q = origin.gpr q
  frame : Frame [roundRegion origin] origin.mem s.mem

theorem loopStep (keys : DesSchedule) (direction : Direction) (base : Addr)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hcountRead : InRegions (origin.rd ++ origin.wr) (countAddr origin) 8)
    (hcountWrite : InRegions origin.wr (countAddr origin) 8)
    (hstepRead : InRegions (origin.rd ++ origin.wr) (stepAddr origin) 8)
    (hread : ∀ j < 16, InRegions (origin.rd ++ origin.wr) (keyAddr base direction j) 8)
    (hsep : ∀ j < 16, (⟨keyAddr base direction j, 8⟩ : Region).Disjoint (roundRegion origin))
    (hkeys : ∀ j < 16, (origin.mem.readW (keyAddr base direction j) 64).setWidth 48 =
      roundKey keys direction j)
    (n : Nat) (s : State) (hs : LoopInv keys direction base origin v n s) :
    WP isa (.block (roundBody ++ roundAdvance)) s (fun s' =>
      (isa.eval .ne s' = some false ∧ LoopPost keys direction origin v s') ∨
      (isa.eval .ne s' = some true ∧ ∃ m < n, LoopInv keys direction base origin v m s')) := by
  obtain hj : 16 - n < 16 := by omega_using [hs.positive]
  obtain haddr : countAddr s = countAddr origin := by
    simp only [countAddr, hs.regs .rdx (by decide)]
  obtain hwork : roundRegion s = roundRegion origin := by
    simp only [roundRegion, hs.regs .rdx (by decide)]
  obtain hstepAddr : stepAddr s = stepAddr origin := by
    simp only [stepAddr, hs.regs .rdx (by decide)]
  obtain hstepS : InRegions (s.rd ++ s.wr) (stepAddr s) 8 := by
    rw [hs.rd, hs.wr, hstepAddr]; exact hstepRead
  have hokS : Ok sboxCfg s := hok.congr
    (hs.regs .rdx (by decide)) (hs.regs .rdx (by decide)) hs.rd hs.wr
  obtain hreadS : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 8 := by
    rw [hs.rd, hs.wr, hs.pointer]; exact hread _ hj
  obtain hsepS : (⟨s.gpr .rdi, 8⟩ : Region).Disjoint (spillRegion s) := by
    rw [hs.pointer]
    intro a ha hb
    apply hsep _ hj a ha
    rw [← hwork]
    exact spill_sub_work s a hb
  obtain hreadCountS : InRegions (s.rd ++ s.wr) (countAddr s) 8 := by
    rw [hs.rd, hs.wr, haddr]; exact hcountRead
  obtain hwriteCountS : InRegions s.wr (countAddr s) 8 := by
    rw [hs.wr, haddr]; exact hcountWrite
  obtain hk : (s.mem.readW (s.gpr .rdi) 64).setWidth 48 = roundKey keys direction (16 - n) := by
    rw [hs.pointer]
    obtain hmem := hs.frame.readW (a := keyAddr base direction (16 - n)) (w := 64)
      (r := ⟨keyAddr base direction (16 - n), 8⟩)
      (Region.contains_self _ _) (fun q hq => by
        obtain rfl := List.mem_singleton.mp hq
        exact hsep _ hj) (by decide)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hkeys _ hj)
  obtain ⟨s', run, left, right, ptr, count, flag, rd, wr, regs, frame⟩ :=
    roundStep_ok s _ _ (s.mem.readW (s.gpr .rdi) 64) n hs.positive
      (by omega_using [hs.bounded]) hs.left hs.right rfl hokS hreadS hsepS
      hs.counter hreadCountS hwriteCountS hstepS
  obtain hstep' : s'.mem.readW (stepAddr s') 64 = stepVal direction := by
    obtain hsa : stepAddr s' = stepAddr s := by
      simp only [stepAddr, regs .rdx (by decide)]
    rw [hsa]
    refine Eq.trans (frame.readW (r := ⟨stepAddr s, 8⟩) (Region.contains_self _ _) ?_ (by decide)) hs.step
    intro q hq
    obtain rfl := List.mem_singleton.mp hq
    exact step_round_disjoint s
  obtain hidx : 16 - (n - 1) = 16 - n + 1 := by
    omega_using [hs.positive, hs.bounded]
  obtain hleft : s'.gpr .r12 = (roundPrefix keys direction (16 - (n - 1)) v).1.setWidth 64 := by
    rw [hidx]
    exact left.trans (congrArg (fun pair => pair.1.setWidth 64)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  obtain hright : s'.gpr .r13 = (roundPrefix keys direction (16 - (n - 1)) v).2.setWidth 64 := by
    rw [hidx]
    obtain hval := congrArg (fun key =>
      ((roundPrefix keys direction (16 - n) v).1 ^^^
        Spec.TripleDes.roundFunction (roundPrefix keys direction (16 - n) v).2 key).setWidth 64) hk
    exact (right.trans hval).trans (congrArg (fun pair => pair.2.setWidth 64)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  obtain hframe : Frame [roundRegion origin] origin.mem s'.mem := by
    rw [hwork] at frame
    exact hs.frame.trans frame
  obtain hregs : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s'.gpr q = origin.gpr q :=
    fun q hq => (regs q hq).trans (hs.regs q hq)
  refine WP.of_runBlock ⟨s', run, ?_⟩
  by_cases hlast : n = 1
  · left
    refine ⟨?_, ?_⟩
    · simpa only [hlast, ne_eq, not_true_eq_false, decide_false] using flag
    · subst n
      exact ⟨hleft, hright, count, rd.trans hs.rd, wr.trans hs.wr, hregs, hframe⟩
  · right
    refine ⟨?_, n - 1, by omega_using [hs.positive], ?_⟩
    · simpa only [hlast, ne_eq, not_false_eq_true, decide_true] using flag
    · refine ⟨by omega_using [hs.positive, hlast], by omega_using [hs.bounded],
        hleft, hright, count, ?_, hstep', rd.trans hs.rd, wr.trans hs.wr, hregs, hframe⟩
      rw [ptr, hs.pointer, hs.step, keyAddr_step base direction (16 - n) (by
        omega_using [hs.positive, hlast]), ← hidx]

/-- The complete sixteen-round loop, in either key order. -/
theorem roundsLoop_ok (keys : DesSchedule) (direction : Direction) (base : Addr)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hl : origin.gpr .r12 = v.1.setWidth 64) (hr : origin.gpr .r13 = v.2.setWidth 64)
    (hptr : origin.gpr .rdi = keyAddr base direction 0)
    (hcount : origin.mem.readW (countAddr origin) 64 = BitVec.ofNat 64 16)
    (hcountRead : InRegions (origin.rd ++ origin.wr) (countAddr origin) 8)
    (hcountWrite : InRegions origin.wr (countAddr origin) 8)
    (hstep : origin.mem.readW (stepAddr origin) 64 = stepVal direction)
    (hstepRead : InRegions (origin.rd ++ origin.wr) (stepAddr origin) 8)
    (hread : ∀ j < 16, InRegions (origin.rd ++ origin.wr) (keyAddr base direction j) 8)
    (hsep : ∀ j < 16, (⟨keyAddr base direction j, 8⟩ : Region).Disjoint (roundRegion origin))
    (hkeys : ∀ j < 16, (origin.mem.readW (keyAddr base direction j) 64).setWidth 48 =
      roundKey keys direction j) :
    WP isa (.loop (.block (roundBody ++ roundAdvance)) .ne)
      origin (LoopPost keys direction origin v) := by
  apply WP.loop (M := isa) (body := .block (roundBody ++ roundAdvance))
    (c := .ne) (Q := LoopPost keys direction origin v) (LoopInv keys direction base origin v)
    (loopStep keys direction base origin v hok hcountRead hcountWrite hstepRead hread hsep hkeys)
    16 origin
  exact ⟨by decide, by decide, hl, hr, hcount, hptr, hstep, rfl, rfl,
    fun _ _ => rfl, Frame.refl _ _⟩

end VG.Proof.TripleDes.X86_64

end

end


@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction)

def savedKeyAddr (s : State) : Addr := s.gpr .rdx + BitVec.ofNat 64 48

def passOffset (component : Nat) (direction : Direction) : Nat :=
  128 * component + if direction = .encrypt then 0 else 120

theorem passOffset_signExtend (component : Nat) (hc : component < 3) (direction : Direction) :
    (BitVec.ofNat 32 (passOffset component direction)).signExtend 64 =
      BitVec.ofNat 64 (passOffset component direction) := by
  obtain h : ∀ c < 3,
      ((BitVec.ofNat 32 (passOffset c .encrypt)).signExtend 64 =
        BitVec.ofNat 64 (passOffset c .encrypt)) ∧
      ((BitVec.ofNat 32 (passOffset c .decrypt)).signExtend 64 =
        BitVec.ofNat 64 (passOffset c .decrypt)) := by decide +kernel
  cases direction
  · exact (h component hc).1
  · exact (h component hc).2

theorem stepImm_signExtend (direction : Direction) :
    (if direction = .encrypt then (8 : BitVec 32) else BitVec.ofInt 32 (-8)).signExtend 64 =
      stepVal direction := by
  cases direction <;> decide

theorem passStart_ok (component : Nat) (hc : component < 3) (direction : Direction)
    (s : State) (hread : InRegions (s.rd ++ s.wr) (savedKeyAddr s) 8)
    (hwrite : InRegions s.wr (countAddr s) 8) (hstep : InRegions s.wr (stepAddr s) 8) :
    ∃ s', runBlock isa (passStart component direction) s = some s' ∧
      s'.gpr .rdi = s.mem.readW (savedKeyAddr s) 64 +
        BitVec.ofNat 64 (passOffset component direction) ∧
      s'.mem = (s.mem.writeW (countAddr s) (BitVec.ofNat 64 16)).writeW (stepAddr s)
        (stepVal direction) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → s'.gpr r = s.gpr r) := by
  unfold savedKeyAddr at hread
  unfold countAddr at hwrite
  unfold stepAddr at hstep
  have h48 : BitVec.ofInt 64 (Int.ofNat 48) = BitVec.ofNat 64 48 := rfl
  have h56 : BitVec.ofInt 64 (Int.ofNat 56) = BitVec.ofNat 64 56 := rfl
  have h448 : BitVec.ofInt 64 (Int.ofNat 448) = BitVec.ofNat 64 448 := rfl
  refine ⟨_, by
    simp only [passStart, imm, runBlock_cons, runStep_some, runBlock_nil, exec,
      execAlu, readSrc, State.ea, memOp, h48, h56, h448, State.load64, State.store64,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, gpr_arithFlags, mem_arithFlags,
      rd_arithFlags, wr_arithFlags, reduceCtorEq, ite_false, ite_true,
      hread, hwrite, hstep, Option.map_some, Option.bind_some]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
    exact congrArg (s.mem.readW (savedKeyAddr s) 64 + ·)
      (passOffset_signExtend component hc direction)
  · simp only [stepImm_signExtend]
    rfl
  · rfl
  · rfl
  · intro r hrax hrdi
    simp only [gpr_setReg, gpr_arithFlags, hrax, hrdi, ite_false]

end VG.Proof.TripleDes.X86_64

end

end


@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix)

def passesAddr (s : State) : Addr := s.gpr .rdx + BitVec.ofNat 64 456

theorem passes_round_disjoint (s : State) :
    (⟨passesAddr s, 8⟩ : Region).Disjoint (roundRegion s) :=
  Offset.disjoint (s.gpr .rdx) (by decide) (by decide) (by decide)

theorem passes_step_disjoint (s : State) :
    (⟨passesAddr s, 8⟩ : Region).Disjoint ⟨stepAddr s, 8⟩ :=
  Offset.disjoint (s.gpr .rdx) (by decide) (by decide) (by decide)

theorem step_sub_work (s : State) : Region.Sub ⟨stepAddr s, 8⟩ (workRegion s) :=
  Offset.sub (s.gpr .rdx) (by decide) (by decide)

theorem passes_sub_work (s : State) : Region.Sub ⟨passesAddr s, 8⟩ (workRegion s) :=
  Offset.sub (s.gpr .rdx) (by decide) (by decide)

theorem passCountAdvance_ok (s : State)
    (hread : InRegions (s.rd ++ s.wr) (passesAddr s) 8)
    (hwrite : InRegions s.wr (passesAddr s) 8) :
    ∃ s', runBlock isa passCountAdvance s = some s' ∧
      s'.mem = s.mem.writeW (passesAddr s) (s.mem.readW (passesAddr s) 64 - 1) ∧
      s'.zf = some ((s.mem.readW (passesAddr s) 64 - 1) == 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) := by
  unfold passesAddr at hread hwrite
  have hoff : BitVec.ofInt 64 (Int.ofNat 456) = BitVec.ofNat 64 456 := rfl
  refine ⟨_, by
    simp only [passCountAdvance, runBlock_cons, runStep_some, runBlock_nil, exec,
      execAlu, readSrc, State.ea, memOp, hoff, State.load64, State.store64,
      gpr_setReg, mem_setReg, rd_setReg, wr_setReg, gpr_arithFlags, mem_arithFlags,
      rd_arithFlags, wr_arithFlags, reduceCtorEq, ite_false, ite_true,
      hread, hwrite, Option.map_some, Option.bind_some]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [zf_setReg, zf_arithFlags]
    rfl
  · rfl
  · rfl
  · intro r hr
    simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]

/-- What choosing and starting the pass of component `c` and direction `d` leaves. -/
structure StartPost (c : Nat) (d : Direction) (s t : State) : Prop where
  ptr : t.gpr .rdi = s.mem.readW (savedKeyAddr s) 64 + BitVec.ofNat 64 (passOffset c d)
  mem : t.mem = (s.mem.writeW (countAddr s) (BitVec.ofNat 64 16)).writeW (stepAddr s) (stepVal d)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  regs : ∀ r, r ≠ .rax → r ≠ .rdi → t.gpr r = s.gpr r

theorem passOf_lt (d : Direction) (p : Nat) : (passOf d p).1 < 3 := by
  cases d <;> (rcases p with _ | _ | _ | _ | p) <;> simp [passOf]

/-- The comparison of `rax` with an immediate. -/
def cmpState (s : State) (v : BitVec 32) : State :=
  arithFlags s (s.gpr .rax - v.signExtend 64) (decide ((s.gpr .rax).toNat < (v.signExtend 64).toNat))
    (subOverflow (s.gpr .rax) (v.signExtend 64) (s.gpr .rax - v.signExtend 64))

theorem cmp_run (s : State) (v : BitVec 32) :
    runBlock isa [.alu .cmp .rax (.imm v)] s = some (cmpState s v) := by
  rw [runBlock_cons]
  rfl

theorem select_ok (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) (s : State)
    (hpasses : s.mem.readW (passesAddr s) 64 = BitVec.ofNat 64 p)
    (hpRead : InRegions (s.rd ++ s.wr) (passesAddr s) 8)
    (hread : InRegions (s.rd ++ s.wr) (savedKeyAddr s) 8)
    (hwrite : InRegions s.wr (countAddr s) 8) (hstep : InRegions s.wr (stepAddr s) 8) :
    WP isa (passSelect d) s (StartPost (passOf d p).1 (passOf d p).2 s) := by
  -- a branch, from a state that differs from `s` in `rax` and the flags only
  obtain branch : ∀ (t : State) (q : Nat), q = p → t.mem = s.mem → t.rd = s.rd → t.wr = s.wr →
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) →
      WP isa (.block (passStart (passOf d q).1 (passOf d q).2)) t
        (StartPost (passOf d p).1 (passOf d p).2 s) := by
    intro t q hq hm hrd hwr hg
    subst hq
    obtain hdx : t.gpr .rdx = s.gpr .rdx := hg .rdx (by decide)
    obtain hsaved : savedKeyAddr t = savedKeyAddr s := by simp only [savedKeyAddr, hdx]
    obtain hcount : countAddr t = countAddr s := by simp only [countAddr, hdx]
    obtain hstepA : stepAddr t = stepAddr s := by simp only [stepAddr, hdx]
    obtain ⟨u, run, ptr, mem, rd, wr, regs⟩ := passStart_ok (passOf d q).1 (passOf_lt d q)
      (passOf d q).2 t (by rw [hrd, hwr, hsaved]; exact hread) (by rw [hwr, hcount]; exact hwrite)
      (by rw [hwr, hstepA]; exact hstep)
    refine WP.of_runBlock ⟨u, run, ?_, ?_, rd.trans hrd, wr.trans hwr, ?_⟩
    · rw [ptr, hm, hsaved]
    · rw [mem, hm, hcount, hstepA]
    · intro r hrax hrdi
      exact (regs r hrax hrdi).trans (hg r hrax)
  let v := s.mem.readW (passesAddr s) 64
  let s₁ := s.setReg .rax v
  obtain e₁ : exec (.mov .rax (.mem (memOp .rdx 456))) s = some s₁ := by
    unfold passesAddr at hpRead
    have hoff : BitVec.ofInt 64 (Int.ofNat 456) = BitVec.ofNat 64 456 := rfl
    simp only [exec, readSrc, State.ea, memOp, hoff, State.load64, hpRead]
    rfl
  let t₁ := cmpState s₁ 3
  obtain hrax₁ : t₁.gpr .rax = BitVec.ofNat 64 p := by
    simp only [t₁, cmpState, gpr_arithFlags, s₁, gpr_setReg_self, v, hpasses]
  obtain hg₁ : ∀ r, r ≠ .rax → t₁.gpr r = s.gpr r := by
    intro r hr
    simp only [t₁, cmpState, gpr_arithFlags, s₁, gpr_setReg_of_ne (s := s) v hr]
  obtain hm₁ : t₁.mem = s.mem := by simp only [t₁, cmpState, mem_arithFlags, s₁, mem_setReg]
  obtain hrd₁ : t₁.rd = s.rd := by simp only [t₁, cmpState, rd_arithFlags, s₁, rd_setReg]
  obtain hwr₁ : t₁.wr = s.wr := by simp only [t₁, cmpState, wr_arithFlags, s₁, wr_setReg]
  apply WP.seq
  refine WP.of_runBlock ⟨t₁, by rw [runBlock_cons, e₁, runStep_some, cmp_run], ?_⟩
  obtain zf₁ : isa.eval .e t₁ = some (p == 3) := by
    change t₁.zf = _
    simp only [t₁, cmpState, zf_arithFlags, s₁, gpr_setReg_self, v, hpasses]
    rcases hp with ⟨h1, h3⟩
    rcases p with _ | _ | _ | _ | p <;> first | omega | decide
  apply WP.ite (p == 3) zf₁
  · intro h3
    exact branch t₁ 3 (by simpa using h3 : p = 3).symm hm₁ hrd₁ hwr₁ hg₁
  · intro h3
    obtain hp3 : p ≠ 3 := by simpa using h3
    apply WP.seq
    let t₂ := cmpState t₁ 2
    refine WP.of_runBlock ⟨t₂, cmp_run t₁ 2, ?_⟩
    obtain zf₂ : isa.eval .e t₂ = some (p == 2) := by
      change t₂.zf = _
      simp only [t₂, cmpState, zf_arithFlags, hrax₁]
      rcases hp with ⟨h1, h3⟩
      rcases p with _ | _ | _ | _ | p <;> first | omega | decide
    obtain hg₂ : ∀ r, r ≠ .rax → t₂.gpr r = s.gpr r := by
      intro r hr
      simp only [t₂, cmpState, gpr_arithFlags]
      exact hg₁ r hr
    obtain hm₂ : t₂.mem = s.mem := by simp only [t₂, cmpState, mem_arithFlags, hm₁]
    obtain hrd₂ : t₂.rd = s.rd := by simp only [t₂, cmpState, rd_arithFlags, hrd₁]
    obtain hwr₂ : t₂.wr = s.wr := by simp only [t₂, cmpState, wr_arithFlags, hwr₁]
    apply WP.ite (p == 2) zf₂
    · intro h2
      exact branch t₂ 2 (by simpa using h2 : p = 2).symm hm₂ hrd₂ hwr₂ hg₂
    · intro h2
      obtain hp2 : p ≠ 2 := by simpa using h2
      exact branch t₂ 1 (by omega_using [hp, hp3, hp2]) hm₂ hrd₂ hwr₂ hg₂

structure PassPost (keys : DesSchedule) (direction : Direction)
    (origin : State) (v : BitVec 32 × BitVec 32) (n : Nat) (s : State) : Prop where
  left : s.gpr .r12 = (roundPrefix keys direction 16 v).2.setWidth 64
  right : s.gpr .r13 = (roundPrefix keys direction 16 v).1.setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s.gpr q = origin.gpr q
  frame : Frame [workRegion origin] origin.mem s.mem
  passes : s.mem.readW (passesAddr s) 64 = BitVec.ofNat 64 (n - 1)
  zf : isa.eval .ne s = some (decide (n ≠ 1))

/-- A complete DES pass: the choice of its keys by the passes left, its
sixteen rounds, the final half swap and the passes left counted down. -/
theorem pass_ok (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3)
    (keys : DesSchedule) (base : Addr) (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hl : origin.gpr .r12 = v.1.setWidth 64) (hr : origin.gpr .r13 = v.2.setWidth 64)
    (hpasses : origin.mem.readW (passesAddr origin) 64 = BitVec.ofNat 64 p)
    (hpRead : InRegions (origin.rd ++ origin.wr) (passesAddr origin) 8)
    (hpWrite : InRegions origin.wr (passesAddr origin) 8)
    (hptr : origin.mem.readW (savedKeyAddr origin) 64 +
      BitVec.ofNat 64 (passOffset (passOf d p).1 (passOf d p).2) = keyAddr base (passOf d p).2 0)
    (hsavedRead : InRegions (origin.rd ++ origin.wr) (savedKeyAddr origin) 8)
    (hcountRead : InRegions (origin.rd ++ origin.wr) (countAddr origin) 8)
    (hcountWrite : InRegions origin.wr (countAddr origin) 8)
    (hstepWrite : InRegions origin.wr (stepAddr origin) 8)
    (hread : ∀ j < 16, InRegions (origin.rd ++ origin.wr) (keyAddr base (passOf d p).2 j) 8)
    (hsep : ∀ j < 16, (⟨keyAddr base (passOf d p).2 j, 8⟩ : Region).Disjoint (workRegion origin))
    (hkeys : ∀ j < 16, (origin.mem.readW (keyAddr base (passOf d p).2 j) 64).setWidth 48 =
      roundKey keys (passOf d p).2 j) :
    WP isa (pass d) origin (PassPost keys (passOf d p).2 origin v p) := by
  apply WP.seq
  refine WP.mono (select_ok d hp origin hpasses hpRead hsavedRead hcountWrite hstepWrite)
    fun s hs => ?_
  generalize (passOf d p).2 = dir at hs hptr hread hsep hkeys ⊢
  obtain hbase : s.gpr .rdx = origin.gpr .rdx := hs.regs .rdx (by decide) (by decide)
  obtain hcountAddr : countAddr s = countAddr origin := by simp only [countAddr, hbase]
  obtain hstepAddr : stepAddr s = stepAddr origin := by simp only [stepAddr, hbase]
  obtain hpassesAddr : passesAddr s = passesAddr origin := by simp only [passesAddr, hbase]
  obtain hroundR : roundRegion s = roundRegion origin := by simp only [roundRegion, hbase]
  obtain hsepR : ∀ j < 16, (⟨keyAddr base dir j, 8⟩ : Region).Disjoint (roundRegion origin) :=
    fun j hj => (hsep j hj).sub_right (round_sub_work origin)
  obtain hsepStep : ∀ j < 16, (⟨keyAddr base dir j, 8⟩ : Region).Disjoint ⟨stepAddr origin, 8⟩ :=
    fun j hj => (hsep j hj).sub_right (step_sub_work origin)
  -- what the start writes
  obtain hframe : Frame [roundRegion origin, ⟨stepAddr origin, 8⟩] origin.mem s.mem := by
    rw [hs.mem]
    refine Frame.trans ((countWrite_frame _ _ _).sub ?_) ((countWrite_frame _ _ _).sub ?_)
    · intro q hq
      obtain rfl := List.mem_singleton.mp hq
      exact ⟨_, List.mem_cons_self .., count_sub_work origin⟩
    · intro q hq
      obtain rfl := List.mem_singleton.mp hq
      exact ⟨_, by simp, fun _ h => h⟩
  obtain hframeDisj : ∀ (r : Region), r.Disjoint (roundRegion origin) →
      r.Disjoint ⟨stepAddr origin, 8⟩ → ∀ r' ∈ [roundRegion origin, ⟨stepAddr origin, 8⟩],
      r.Disjoint r' := by
    intro r h1 h2 r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact h1
    · exact h2
  obtain hkeysS : ∀ j < 16, (s.mem.readW (keyAddr base dir j) 64).setWidth 48 =
      roundKey keys dir j := by
    intro j hj
    obtain hmem := hframe.readW (a := keyAddr base dir j) (w := 64)
      (r := ⟨keyAddr base dir j, 8⟩) (Region.contains_self _ _)
      (hframeDisj _ (hsepR j hj) (hsepStep j hj)) (by decide)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hkeys j hj)
  obtain hcountS : s.mem.readW (countAddr s) 64 = BitVec.ofNat 64 16 := by
    rw [hs.mem, hcountAddr]
    obtain hsepCS : (⟨countAddr origin, 8⟩ : Region).Disjoint ⟨stepAddr origin, 8⟩ :=
      Offset.disjoint (origin.gpr .rdx) (by decide) (by decide) (by decide)
    rw [((countWrite_frame (origin.mem.writeW (countAddr origin) (BitVec.ofNat 64 16))
      (stepAddr origin) (stepVal dir)).readW (r := ⟨countAddr origin, 8⟩)
      (Region.contains_self _ _) (fun q hq => by
        obtain rfl := List.mem_singleton.mp hq; exact hsepCS) (by decide))]
    exact Mem.readW_writeW_self64 _ _ _
  obtain hstepS : s.mem.readW (stepAddr s) 64 = stepVal dir := by
    rw [hs.mem, hstepAddr]
    exact Mem.readW_writeW_self64 _ _ _
  obtain hpassesS : s.mem.readW (passesAddr s) 64 = BitVec.ofNat 64 p := by
    rw [hpassesAddr, hframe.readW (r := ⟨passesAddr origin, 8⟩) (Region.contains_self _ _)
      (hframeDisj _ (passes_round_disjoint origin) (passes_step_disjoint origin)) (by decide)]
    exact hpasses
  obtain hloop := roundsLoop_ok keys dir base s v
    (hok.congr hbase hbase hs.rd hs.wr)
    ((hs.regs .r12 (by decide) (by decide)).trans hl)
    ((hs.regs .r13 (by decide) (by decide)).trans hr)
    (hs.ptr.trans hptr) hcountS
    (by rw [hs.rd, hs.wr, hcountAddr]; exact hcountRead)
    (by rw [hs.wr, hcountAddr]; exact hcountWrite) hstepS
    (by rw [hs.rd, hs.wr, hstepAddr]
        exact ⟨_, hstepWrite.choose_spec.1 |> List.mem_append_right _,
          hstepWrite.choose_spec.2⟩)
    (by rw [hs.rd, hs.wr]; exact hread)
    (by rw [hroundR]; exact hsepR) hkeysS
  apply WP.seq
  refine WP.mono hloop fun s₂ hs₂ => ?_
  obtain hbase₂ : s₂.gpr .rdx = origin.gpr .rdx := (hs₂.regs .rdx (by decide)).trans hbase
  obtain ⟨s₃, run₃, left₃, right₃, rd₃, wr₃, mem₃, regs₃⟩ := swapHalves_ok s₂
  obtain hbase₃ : s₃.gpr .rdx = origin.gpr .rdx := (regs₃ .rdx (by decide)).trans hbase₂
  obtain hpassesAddr₃ : passesAddr s₃ = passesAddr origin := by simp only [passesAddr, hbase₃]
  obtain ⟨s₄, run₄, mem₄, zf₄, rd₄, wr₄, regs₄⟩ := passCountAdvance_ok s₃
    (by rw [rd₃, wr₃, hs₂.rd, hs₂.wr, hs.rd, hs.wr, hpassesAddr₃]; exact hpRead)
    (by rw [wr₃, hs₂.wr, hs.wr, hpassesAddr₃]; exact hpWrite)
  obtain hp₃ : s₃.mem.readW (passesAddr s₃) 64 = BitVec.ofNat 64 p := by
    rw [mem₃, hpassesAddr₃, ← hpassesAddr, hs₂.frame.readW (r := ⟨passesAddr s, 8⟩)
      (Region.contains_self _ _) (fun q hq => by
        obtain rfl := List.mem_singleton.mp hq; exact passes_round_disjoint s) (by decide)]
    exact hpassesS
  obtain ⟨hsub, hzero⟩ := countDown_rules p (by omega_using [hp]) hp.1
  refine WP.of_runBlock ⟨s₄, by simp only [runBoxes_append, run₃, Option.bind_some, run₄], ?_⟩
  refine ⟨?_, ?_, rd₄.trans (rd₃.trans (hs₂.rd.trans hs.rd)),
    wr₄.trans (wr₃.trans (hs₂.wr.trans hs.wr)), ?_, ?_, ?_, ?_⟩
  · exact (regs₄ .r12 (by decide)).trans (left₃.trans hs₂.right)
  · exact (regs₄ .r13 (by decide)).trans (right₃.trans hs₂.left)
  · intro q hq
    obtain hq' : q ∈ roundOuterKept := by revert hq; cases q <;> decide
    obtain hrax : q ≠ .rax := by revert hq; cases q <;> decide
    obtain hrdi : q ≠ .rdi := by revert hq; cases q <;> decide
    exact (regs₄ q hrax).trans ((regs₃ q hq').trans ((hs₂.regs q hq).trans (hs.regs q hrax hrdi)))
  · have hf₁ : Frame [workRegion origin] origin.mem s.mem := hframe.sub (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact ⟨_, List.mem_singleton_self _, round_sub_work origin⟩
      · exact ⟨_, List.mem_singleton_self _, step_sub_work origin⟩)
    obtain hf₂ : Frame [workRegion origin] s.mem s₂.mem := hs₂.frame.sub (by
      intro q hq
      obtain rfl := List.mem_singleton.mp hq
      exact ⟨_, List.mem_singleton_self _, by rw [hroundR]; exact round_sub_work origin⟩)
    obtain hf₄ : Frame [workRegion origin] s₃.mem s₄.mem := by
      rw [mem₄]
      exact (countWrite_frame _ _ _).sub (by
        intro q hq
        obtain rfl := List.mem_singleton.mp hq
        exact ⟨_, List.mem_singleton_self _, by rw [hpassesAddr₃]; exact passes_sub_work origin⟩)
    rw [mem₃] at hf₄
    exact hf₁.trans (hf₂.trans hf₄)
  · have hpassesAddr₄ : passesAddr s₄ = passesAddr s₃ := by
      simp only [passesAddr, regs₄ .rdx (by decide)]
    rw [hpassesAddr₄, mem₄, Mem.readW_writeW_self64, hp₃, hsub]
  · change VG.X86_64.eval .ne s₄ = some (decide (p ≠ 1))
    simp only [VG.X86_64.eval, zf₄, hp₃, hzero, Option.map_some]
    simp

end VG.Proof.TripleDes.X86_64

end

end


@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.Impl.TripleDes.X86_64
open VG.Proof.TripleDes (desCore roundPrefix)

/-- A DES word held as two zero-extended 32-bit Feistel registers. -/
structure WordState (x : BitVec 64) (s : State) : Prop where
  left : s.gpr .r12 = ((x >>> 32).setWidth 32).setWidth 64
  right : s.gpr .r13 = (x.setWidth 32).setWidth 64

theorem PassPost.wordState {keys : Spec.TripleDes.DesSchedule}
    {direction : Spec.TripleDes.Direction} {origin s : State} {x : BitVec 64} {n : Nat}
    (hs : PassPost keys direction origin ((x >>> 32).setWidth 32, x.setWidth 32) n s) :
    WordState (desCore keys direction x) s := by
  obtain hcore := VG.Proof.TripleDes.desCore_roundPrefix keys direction x
  let halves := roundPrefix keys direction 16 ((x >>> 32).setWidth 32, x.setWidth 32)
  obtain hleft : ((desCore keys direction x >>> 32).setWidth 32).setWidth 64 = halves.2.setWidth 64 :=
    (congrArg (fun v : BitVec 64 => ((v >>> 32).setWidth 32).setWidth 64) hcore).trans
      (congrArg (BitVec.setWidth 64) (VG.Proof.TripleDes.appended_left halves.2 halves.1))
  obtain hright : ((desCore keys direction x).setWidth 32).setWidth 64 = halves.1.setWidth 64 :=
    (congrArg (fun v : BitVec 64 => (v.setWidth 32).setWidth 64) hcore).trans
      (congrArg (BitVec.setWidth 64) (VG.Proof.TripleDes.appended_right halves.2 halves.1))
  exact ⟨hs.left.trans hleft.symm, hs.right.trans hright.symm⟩

end VG.Proof.TripleDes.X86_64

end

end

@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

def componentBase (base : Addr) (component : Nat) : Addr :=
  base + BitVec.ofNat 64 (128 * component)

structure Ready (keys : Nat → DesSchedule) (base : Addr) (s : State) : Prop where
  spills : Ok sboxCfg s
  saved : s.mem.readW (savedKeyAddr s) 64 = base
  savedRead : InRegions (s.rd ++ s.wr) (savedKeyAddr s) 8
  countRead : InRegions (s.rd ++ s.wr) (countAddr s) 8
  countWrite : InRegions s.wr (countAddr s) 8
  stepWrite : InRegions s.wr (stepAddr s) 8
  passesRead : InRegions (s.rd ++ s.wr) (passesAddr s) 8
  passesWrite : InRegions s.wr (passesAddr s) 8
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    InRegions (s.rd ++ s.wr) (keyAddr (componentBase base c) d j) 8
  separate : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (⟨keyAddr (componentBase base c) d j, 8⟩ : Region).Disjoint (workRegion s)
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (s.mem.readW (keyAddr (componentBase base c) d j) 64).setWidth 48 = roundKey (keys c) d j

theorem saved_work_disjoint (s : State) :
    (⟨savedKeyAddr s, 8⟩ : Region).Disjoint (workRegion s) :=
  Offset.disjoint (s.gpr .rdx) (by decide) (by decide) (by decide)

theorem Ready.congr {keys : Nat → DesSchedule} {base : Addr} {s t : State}
    (hs : Ready keys base s) (hbase : t.gpr .rdx = s.gpr .rdx)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hf : Frame [workRegion s] s.mem t.mem) : Ready keys base t := by
  have hsave : savedKeyAddr t = savedKeyAddr s := congrArg (· + BitVec.ofNat 64 48) hbase
  have hcount : countAddr t = countAddr s := congrArg (· + BitVec.ofNat 64 56) hbase
  have hwork : workRegion t = workRegion s :=
    congrArg (fun p => (⟨p + BitVec.ofNat 64 56, 408⟩ : Region)) hbase
  have hstep : stepAddr t = stepAddr s := congrArg (· + BitVec.ofNat 64 448) hbase
  have hpasses : passesAddr t = passesAddr s := congrArg (· + BitVec.ofNat 64 456) hbase
  refine ⟨hs.spills.congr hbase hbase hrd hwr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsave]
    have hmem := hf.readW (a := savedKeyAddr s) (w := 64)
      (r := ⟨savedKeyAddr s, 8⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact saved_work_disjoint s) (by decide)
    exact hmem.trans hs.saved
  · rw [hrd, hwr, hsave]; exact hs.savedRead
  · rw [hrd, hwr, hcount]; exact hs.countRead
  · rw [hwr, hcount]; exact hs.countWrite
  · rw [hwr, hstep]; exact hs.stepWrite
  · rw [hrd, hwr, hpasses]; exact hs.passesRead
  · rw [hwr, hpasses]; exact hs.passesWrite
  · rw [hrd, hwr]; exact hs.read
  · rw [hwork]; exact hs.separate
  · intro c hc d j hj
    have hmem := hf.readW (a := keyAddr (componentBase base c) d j) (w := 64)
      (r := ⟨keyAddr (componentBase base c) d j, 8⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hs.separate c hc d j hj) (by decide)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hs.values c hc d j hj)

theorem passPointer (base : Addr) (c : Nat) (d : Direction) :
    base + BitVec.ofNat 64 (passOffset c d) = keyAddr (componentBase base c) d 0 := by
  cases d
  · change base + BitVec.ofNat 64 (128 * c + 0) = base + BitVec.ofNat 64 (128 * c) + (0 : BitVec 64)
    exact (congrArg (fun n => base + BitVec.ofNat 64 n) (Nat.add_zero (128 * c))).trans
      (BitVec.add_zero (base + BitVec.ofNat 64 (128 * c))).symm
  · simp only [passOffset, keyAddr, componentBase, reduceCtorEq, ite_false]
    rw [Offset.add_ofNat_add_ofNat]


structure Stable (origin s : State) : Prop where
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ [Reg.rsi, .rdx, .rsp], s.gpr q = origin.gpr q
  frame : Frame [workRegion origin] origin.mem s.mem

theorem Stable.trans {s t u : State} (hs : Stable s t) (ht : Stable t u) : Stable s u := by
  have hwork : workRegion t = workRegion s :=
    congrArg (fun p => (⟨p + BitVec.ofNat 64 56, 408⟩ : Region)) (hs.regs .rdx (by decide))
  have hf := ht.frame
  rw [hwork] at hf
  exact ⟨ht.rd.trans hs.rd, ht.wr.trans hs.wr,
    fun q hq => (ht.regs q hq).trans (hs.regs q hq), hs.frame.trans hf⟩

theorem pass_word_ok (keys : Nat → DesSchedule) (base : Addr) (s : State) (x : BitVec 64)
    (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3)
    (hready : Ready keys base s) (hword : WordState x s)
    (hpasses : s.mem.readW (passesAddr s) 64 = BitVec.ofNat 64 p) :
    WP isa (pass d) s (fun t =>
      WordState (VG.Proof.TripleDes.desCore (keys (passOf d p).1) (passOf d p).2 x) t ∧
      Ready keys base t ∧ Stable s t ∧
      t.mem.readW (passesAddr t) 64 = BitVec.ofNat 64 (p - 1) ∧
      isa.eval .ne t = some (decide (p ≠ 1))) := by
  have hc := passOf_lt d p
  have hptr : s.mem.readW (savedKeyAddr s) 64 +
      BitVec.ofNat 64 (passOffset (passOf d p).1 (passOf d p).2) =
      keyAddr (componentBase base (passOf d p).1) (passOf d p).2 0 := by
    rw [hready.saved]
    exact passPointer base _ _
  apply WP.mono (pass_ok d hp (keys (passOf d p).1) (componentBase base (passOf d p).1) s
    ((x >>> 32).setWidth 32, x.setWidth 32) hready.spills hword.left hword.right
    hpasses hready.passesRead hready.passesWrite hptr hready.savedRead hready.countRead
    hready.countWrite hready.stepWrite
    (hready.read _ hc _) (hready.separate _ hc _) (hready.values _ hc _))
  intro t ht
  exact ⟨ht.wordState,
    hready.congr (ht.regs .rdx (by decide)) ht.rd ht.wr ht.frame,
    ⟨ht.rd, ht.wr, ht.regs, ht.frame⟩, ht.passes, ht.zf⟩

end VG.Proof.TripleDes.X86_64

end

end

/-! ### `TripleDes.X86_64.Save`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.Impl.TripleDes.X86_64

/-- The six callee-saved registers and the schedule pointer, in slot order. -/
def savedReg (i : Nat) : Reg := (savedRegs ++ [Reg.rdi]).getD i .rdi

theorem blockSave_eq : blockSave = VG.Proof.Rc2.X86_64.saveCode .rdx savedReg 7 := by
  decide +kernel

theorem blockRestore_eq : blockRestore = VG.Proof.Rc2.X86_64.restoreCode .rdx savedReg (List.range 7) := by
  decide +kernel

def Saved (original current : State) : Prop :=
  ∀ i < 7, current.mem.readW (current.gpr .rdx + BitVec.ofNat 64 (8 * i)) 64 =
    original.gpr (savedReg i)

theorem blockSave_ok (s : State)
    (hw : ∀ i < 7, InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block blockSave) s (fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Saved s s' ∧
      Frame [⟨s.gpr .rdx, 56⟩] s.mem s'.mem) := by
  rw [blockSave_eq]
  apply WP.mono (VG.Proof.Rc2.X86_64.saveCode_ok s .rdx savedReg 7 hw)
  intro s' hs
  refine ⟨hs.1, hs.2.1, hs.2.2.1, ?_, ?_⟩
  · intro i hi
    rw [hs.1, hs.2.2.2]
    exact VG.Proof.Rc2.X86_64.saveMem_read _ _ _ 7 (by decide) i hi
  · rw [hs.2.2.2]
    exact VG.Proof.Rc2.X86_64.saveMem_frame _ _ _ 7 (by decide)

theorem savedReg_separate : ∀ i < 7, savedReg i ≠ .rdx := by decide +kernel

theorem blockRestore_ok (original s : State) (hsaved : Saved original s)
    (hread : ∀ i < 7, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block blockRestore) s (fun s' =>
      (∀ r ∈ savedRegs ++ [Reg.rdi], s'.gpr r = original.gpr r) ∧
      VG.Proof.Rc2.X86_64.Keep (savedRegs ++ [Reg.rdi]) s s') := by
  rw [blockRestore_eq]
  have hregs : (List.range 7).map savedReg = savedRegs ++ [Reg.rdi] := by decide +kernel
  have h := VG.Proof.Rc2.X86_64.restoreCode_ok s .rdx savedReg (List.range 7) original.gpr
    (fun i hi => savedReg_separate i (List.mem_range.mp hi))
    (fun i hi => hread i (List.mem_range.mp hi))
    (fun i hi => hsaved i (List.mem_range.mp hi))
  rw [hregs] at h
  exact h


theorem savedSlot_work_disjoint (s : State) (i : Nat) (hi : i < 7) :
    (⟨s.gpr .rdx + BitVec.ofNat 64 (8 * i), 8⟩ : Region).Disjoint (workRegion s) :=
  Offset.disjoint (s.gpr .rdx) (by omega_using [hi]) (by omega_using [hi]) (by decide)

theorem Saved.congr {original s t : State} (hs : Saved original s)
    (hbase : t.gpr .rdx = s.gpr .rdx) (hf : Frame [workRegion s] s.mem t.mem) :
    Saved original t := by
  intro i hi
  have hmem := hf.readW (a := s.gpr .rdx + BitVec.ofNat 64 (8 * i)) (w := 64)
    (r := ⟨s.gpr .rdx + BitVec.ofNat 64 (8 * i), 8⟩) (Region.contains_self _ _)
    (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact savedSlot_work_disjoint s i hi)
    (by decide)
  rw [hbase]
  exact hmem.trans (hs i hi)

end VG.Proof.TripleDes.X86_64

end

end

/-! ### `TripleDes.X86_64.BlockIO`, which only this module used -/

section

/-! ### `TripleDes.X86_64.Initial`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.X86_64
open VG VG.X86_64 VG.Impl.TripleDes.X86_64

theorem initial_ok (s : State) :
    ∃ s', runBlock isa (instrs initialPermutation.lit) s = some s' ∧
      s'.gpr .rbx = (Spec.TripleDes.permute Spec.TripleDes.ip
        ((s.gpr .rax).setWidth 64)).zeroExtend 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs initialPermutation.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) :=
  fixedPermutation_ok Spec.TripleDes.ip (by decide) (by decide)
    VG.Proof.TripleDes.ip_bounds (instrs initialPermutation.lit) initialPermutation_check s
end VG.Proof.TripleDes.X86_64
namespace VG.Proof.TripleDes.X86_64
open VG VG.X86_64 VG.Impl.TripleDes.X86_64

theorem initial_raw_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.ip 64 .rbx .rax .rbp) s = some s' ∧
      s'.gpr .rbx = Spec.TripleDes.permute Spec.TripleDes.ip (s.gpr .rax) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs initialPermutation.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, word, rd, wr, mem, regs⟩ := initial_ok s
  have hcode : permuteCode Spec.TripleDes.ip 64 .rbx .rax .rbp =
      instrs initialPermutation.lit := congrArg instrs initialPermutation.lit_eq
  refine ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, ?_, rd, wr, mem, regs⟩
  exact word.trans ((BitVec.setWidth_eq _).trans
    (congrArg (Spec.TripleDes.permute Spec.TripleDes.ip) (BitVec.setWidth_eq _)))
end VG.Proof.TripleDes.X86_64

namespace VG.Proof.TripleDes.X86_64
open VG VG.X86_64 VG.Impl.TripleDes.X86_64
theorem final_ok (s : State) :
    ∃ s', runBlock isa (instrs finalPermutation.lit) s = some s' ∧
      s'.gpr .rbx = (Spec.TripleDes.permute Spec.TripleDes.fp
        ((s.gpr .rax).setWidth 64)).zeroExtend 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs finalPermutation.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) :=
  fixedPermutation_ok Spec.TripleDes.fp (by decide) (by decide)
    VG.Proof.TripleDes.fp_bounds (instrs finalPermutation.lit) finalPermutation_check s

theorem final_raw_ok (s : State) :
    ∃ s', runBlock isa (permuteCode Spec.TripleDes.fp 64 .rbx .rax .rbp) s = some s' ∧
      s'.gpr .rbx = Spec.TripleDes.permute Spec.TripleDes.fp (s.gpr .rax) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, ((instrs finalPermutation.lit).all fun op => op.dst != some r) = true →
        s'.gpr r = s.gpr r) := by
  obtain ⟨s', run, word, rd, wr, mem, regs⟩ := final_ok s
  have hcode : permuteCode Spec.TripleDes.fp 64 .rbx .rax .rbp =
      instrs finalPermutation.lit := congrArg instrs finalPermutation.lit_eq
  refine ⟨s', (congrArg (fun is => runBlock isa is s) hcode).trans run, ?_, rd, wr, mem, regs⟩
  exact word.trans ((BitVec.setWidth_eq _).trans
    (congrArg (Spec.TripleDes.permute Spec.TripleDes.fp) (BitVec.setWidth_eq _)))

end VG.Proof.TripleDes.X86_64

end

end

@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64

theorem readData_ok (s : State)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 8) :
    ∃ s', runBlock isa
      [.mov .rax (.mem (memOp .rsi 0)), .bswap .rax] s = some s' ∧
      s'.gpr .rax = Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .rsi)) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) := by
  have haddr : s.gpr .rsi + BitVec.ofInt 64 (Int.ofNat 0) = s.gpr .rsi :=
    BitVec.add_zero _
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
      State.ea, memOp, haddr, hread, ite_true, Option.map_some,
      gpr_setReg_self]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg_self]
    exact (decodeBlock_readW s.mem (s.gpr .rsi)).symm
  · simp only [mem_setReg]
  · simp only [rd_setReg]
  · simp only [wr_setReg]
  · intro r hr
    simp only [gpr_setReg, hr, ite_false]

theorem splitHalves_ok (s : State) :
    ∃ s', runBlock isa [rr .r12 .rbx, .shift .shr .r12 32, .mov32 .r13 (.reg .rbx)] s = some s' ∧
      s'.gpr .r12 = s.gpr .rbx >>> 32 ∧
      s'.gpr .r13 = ((s.gpr .rbx).setWidth 32).setWidth 64 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r12 → r ≠ .r13 → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [rr, runBlock_cons, runStep_some, exec, readSrc, execShift,
      Option.map_some, gpr_setReg, ite_true]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.setReg32, gpr_setReg, gpr_setFlags, reduceCtorEq, ite_true, ite_false]
  · exact gpr_setReg_self _ _ _
  · simp only [State.setReg32, mem_setReg, mem_setFlags]
  · simp only [State.setReg32, rd_setReg, rd_setFlags]
  · simp only [State.setReg32, wr_setReg, wr_setFlags]
  · intro r h12 h13
    simp only [State.setReg32, gpr_setReg, gpr_setFlags, h12, h13, ite_false]


theorem upperHalf_extend (x : BitVec 64) :
    x >>> 32 = ((x >>> 32).setWidth 32).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  by_cases h : j < 32
  · simp only [h, hj, decide_true, Bool.true_and]
  · have hz : x.getLsbD (32 + j) = false := BitVec.getLsbD_of_ge _ _ (by omega_using [h])
    simp only [h, hj, decide_false, decide_true, Bool.false_and, Bool.true_and, hz]

theorem runAppend_some (xs ys : List Instr) (s t u : State)
    (hx : runBlock isa xs s = some t) (hy : runBlock isa ys t = some u) :
    runBlock isa (xs ++ ys) s = some u := by
  calc
    runBlock isa (xs ++ ys) s = (runBlock isa xs s).bind (runBlock isa ys) :=
      runBoxes_append xs ys s
    _ = (some t).bind (runBlock isa ys) := congrArg (fun v => v.bind (runBlock isa ys)) hx
    _ = runBlock isa ys t := Option.bind_some t (runBlock isa ys)
    _ = some u := hy

theorem blockLoad_run (s s₁ s₂ s₃ : State)
    (h₁ : runBlock isa [.mov .rax (.mem (memOp .rsi 0)), .bswap .rax] s = some s₁)
    (h₂ : runBlock isa (permuteCode Spec.TripleDes.ip 64 .rbx .rax .rbp) s₁ = some s₂)
    (h₃ : runBlock isa [rr .r12 .rbx, .shift .shr .r12 32, .mov32 .r13 (.reg .rbx)] s₂ = some s₃) :
    runBlock isa blockLoad s = some s₃ := by
  have hhead := runAppend_some _ _ _ _ _ h₁ h₂
  have htail := runAppend_some _ _ _ _ _ hhead h₃
  have hcode : blockLoad =
      (([.mov .rax (.mem (memOp .rsi 0)), .bswap .rax] : List Instr) ++
        permuteCode Spec.TripleDes.ip 64 .rbx .rax .rbp) ++
      [rr .r12 .rbx, .shift .shr .r12 32, .mov32 .r13 (.reg .rbx)] := rfl
  exact (congrArg (fun is => runBlock isa is s) hcode).trans htail

theorem blockLoad_ok (s : State)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 8) :
    ∃ s', runBlock isa blockLoad s = some s' ∧
      s'.gpr .r12 =
        (((Spec.TripleDes.permute Spec.TripleDes.ip
          (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .rsi)))) >>> 32).setWidth 32).setWidth 64 ∧
      s'.gpr .r13 =
        ((Spec.TripleDes.permute Spec.TripleDes.ip
          (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .rsi)))).setWidth 32).setWidth 64 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rsp], s'.gpr r = s.gpr r) := by
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, regs₁⟩ := readData_ok s hread
  obtain ⟨s₂, run₂raw, word₂, rd₂, wr₂, mem₂, regs₂⟩ := initial_raw_ok s₁
  obtain ⟨s₃, run₃, left₃, right₃, mem₃, rd₃, wr₃, regs₃⟩ := splitHalves_ok s₂
  have hword : s₂.gpr .rbx = Spec.TripleDes.permute Spec.TripleDes.ip
      (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .rsi))) := by
    exact word₂.trans (congrArg (Spec.TripleDes.permute Spec.TripleDes.ip) word₁)
  refine ⟨s₃, ?_, ?_, ?_, mem₃.trans (mem₂.trans mem₁),
    rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), ?_⟩
  · exact blockLoad_run s s₁ s₂ s₃ run₁ run₂raw run₃
  · exact left₃.trans ((congrArg (fun x : BitVec 64 => x >>> 32) hword).trans
      (upperHalf_extend _))
  · exact right₃.trans (congrArg (fun x : BitVec 64 => (x.setWidth 32).setWidth 64) hword)
  · intro r hr
    have hdst : (instrs initialPermutation.lit).all
        (fun op => op.dst == some Reg.rbx || op.dst == some Reg.rbp) = true := by
      decide +kernel
    have hneDst : r ≠ .rbx ∧ r ≠ .rbp := by
      have hfinite : ∀ q ∈ [Reg.rdi, .rsi, .rdx, .rsp], q ≠ .rbx ∧ q ≠ .rbp := by decide
      exact hfinite r hr
    have hno : (instrs initialPermutation.lit).all
        (fun op => op.dst != some r) = true := by
      apply List.all_eq_true.mpr
      intro op hop
      have h := List.all_eq_true.mp hdst op hop
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h
      · rw [h, bne_iff_ne]
        intro he
        exact hneDst.1 (Option.some.inj he).symm
      · rw [h, bne_iff_ne]
        intro he
        exact hneDst.2 (Option.some.inj he).symm
    have hne : r ≠ .rax ∧ r ≠ .r12 ∧ r ≠ .r13 := by
      have hfinite : ∀ q ∈ [Reg.rdi, .rsi, .rdx, .rsp],
          q ≠ .rax ∧ q ≠ .r12 ∧ q ≠ .r13 := by decide
      exact hfinite r hr
    exact (regs₃ r hne.2.1 hne.2.2).trans ((regs₂ r hno).trans (regs₁ r hne.1))


end VG.Proof.TripleDes.X86_64

end

end

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

end

end

/-! ### `TripleDes.X86_64.Pre`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction)

def selectedRound (d : Direction) (j : Nat) : Nat := if d = .encrypt then j else 15 - j

theorem selectedRound_bound (d : Direction) (j : Nat) (hj : j < 16) : selectedRound d j < 16 := by
  cases d <;> simp only [selectedRound, reduceCtorEq, ite_true, ite_false] <;> omega_arith

theorem keyAddr_component (base : Addr) (c : Nat) (d : Direction) (j : Nat) :
    keyAddr (componentBase base c) d j = base + BitVec.ofNat 64 (8 * (16 * c + selectedRound d j)) := by
  unfold keyAddr componentBase selectedRound
  rw [Offset.add_ofNat_add_ofNat]
  exact congrArg (fun n => base + BitVec.ofNat 64 n) (by omega_using [])

/-- The block function's precondition, from its 512 bytes of scratch at
`rdx` writable, the schedule at `rdi` readable and the block at `rsi`
writable, neither in the scratch. -/
theorem headPre_of (s : State)
    (scratchWrites : ∀ i < 64, InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8)
    (keyReads : ∀ i < 48, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (8 * i)) 8)
    (dataWrite : InRegions s.wr (s.gpr .rsi) 8)
    (keySep : Region.Disjoint ⟨s.gpr .rdi, 384⟩ ⟨s.gpr .rdx, 512⟩)
    (dataSep : Region.Disjoint ⟨s.gpr .rsi, 8⟩ ⟨s.gpr .rdx, 512⟩) :
    HeadPre (Spec.TripleDes.componentSchedule (Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi)))
      (s.gpr .rdi) s := by
  have inRd : ∀ {a n}, InRegions s.wr a n → InRegions (s.rd ++ s.wr) a n := fun ⟨r, h1, h2⟩ =>
    ⟨r, List.mem_append_right _ h1, h2⟩
  have scratchReads : ∀ i < 64, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8 :=
    fun i hi => inRd (scratchWrites i hi)
  have spills : Ok sboxCfg s := by
    refine ⟨scratchWrites, ?_, by decide, ?_⟩
    · intro k hk; change k < 0 at hk; omega
    · intro k hk j hj; change j < 0 at hj; omega
  have keySub : ∀ c < 3, ∀ direction : Direction, ∀ j < 16,
      Region.Sub ⟨keyAddr (componentBase (s.gpr .rdi) c) direction j, 8⟩ ⟨s.gpr .rdi, 384⟩ := by
    intro c hc direction j hj
    rw [keyAddr_component]
    have hindex := selectedRound_bound direction j hj
    exact Offset.sub_base _ (by omega_using [hc, hindex])
  have workSub : Region.Sub (workRegion s) ⟨s.gpr .rdx, 512⟩ := Offset.sub_base _ (by decide)
  have saveSub : Region.Sub (saveRegion s) ⟨s.gpr .rdx, 512⟩ := Region.sub_prefix (by decide)
  refine ⟨spills, rfl, (fun i hi => scratchReads i (by omega_using [hi])),
    (fun i hi => scratchWrites i (by omega_using [hi])), scratchReads 7 (by decide),
    scratchWrites 7 (by decide), scratchWrites 56 (by decide), scratchReads 57 (by decide),
    scratchWrites 57 (by decide), inRd dataWrite, dataSep.sub_right saveSub, ?_, ?_, ?_, ?_⟩
  · intro c hc direction j hj
    rw [keyAddr_component]
    exact keyReads _ (by have := selectedRound_bound direction j hj; omega_using [hc, this])
  · intro c hc direction j hj
    exact (keySep.sub_left (keySub c hc direction j hj)).sub_right workSub
  · intro c hc direction j hj
    exact (keySep.sub_left (keySub c hc direction j hj)).sub_right saveSub
  · intro c hc direction j hj
    rw [keyAddr_component]
    exact (VG.Proof.TripleDes.componentSchedule_readW s.mem (s.gpr .rdi) c
      (selectedRound direction j) hc (selectedRound_bound direction j hj)).symm

end VG.Proof.TripleDes.X86_64

end

end


/-!
# Triple DES's core for the modes on x86-64

`dirCoreSpec d`: Triple DES's core for the direction `d`
(`Impl.TripleDes.X86_64.dirCore d`) meets what the modes need of a core of
one-word blocks (`Proof.Modes.X86_64.BlockSpec`), with the key a schedule,
its cipher `Spec.TripleDes.cipher` for encryption and
`Spec.TripleDes.invCipher` for decryption, and the key ready when its copy
in the core's slots is the schedule. `crypt` is the block function
(`block_ok`) on the buffer.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.TripleDes.X86_64
open VG.Impl.Aes.X86_64 (sb)
open VG.Proof.Modes (over over_at over_frame)
open VG.Proof.Modes.X86_64 (ScrIn coreRegion blkRegion blkAddr BlockSpec copyN_wp movR_ok addImm_ok
  signExtend_small runBlock_app addr_add)
open VG.Spec.TripleDes (Direction)

/-- The schedule's copy, with the scratch buffer at `B`. -/
abbrev schedAddr (B : Addr) : Addr := B + BitVec.ofNat 64 (8 * schedSlot)

/-- The schedule at `rdi`, outside the regions `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.TripleDes.Schedule) : Prop :=
  ∃ p : Addr, s.gpr .rdi = p ∧ k = Spec.TripleDes.scheduleAt s.mem p ∧ (⟨p, 384⟩ : Region) ∈ s.rd ∧
    p.toNat + 384 ≤ 2 ^ 64 ∧ ∀ r ∈ rs, Region.Disjoint ⟨p, 384⟩ r

/-- The schedule's copy is `k`. -/
def ReadyAt (m : Mem) (B : Addr) (k : Spec.TripleDes.Schedule) : Prop :=
  Spec.TripleDes.scheduleAt m (schedAddr B) = k

/-- The core's blocks are one word. -/
@[simp] theorem dirCore_bw (d : Direction) : (dirCore d).bw = 1 := rfl

theorem dirCipher_bytes (d : Direction) (k : Spec.TripleDes.Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (Spec.Aes.bytesAt m p 8) = (blockResult k d (Spec.TripleDes.blockAt m p)).toList := by
  cases d <;> simp only [dirCipher, Spec.TripleDes.cipher, Spec.TripleDes.invCipher, blockResult, ofFn_bytesAt]

/-- The core's slots, its buffer and the schedule's copy. -/
theorem core_eq (d : Direction) (B : Addr) : coreRegion (dirCore d) B = ⟨B, 904⟩ := rfl
theorem blk_eq (d : Direction) (B : Addr) : blkRegion (dirCore d) B = ⟨B + BitVec.ofNat 64 512, 8⟩ := rfl
theorem total_eq (d : Direction) : (dirCore d).total = 121 := rfl

theorem sched_sub (B : Addr) : Region.Sub ⟨schedAddr B, 384⟩ ⟨B, 904⟩ := Offset.sub_base B (by decide)

theorem readyAt_frame {d : Direction} {m m' : Mem} {B : Addr} {k : Spec.TripleDes.Schedule} {rs : List Region}
    (h : ReadyAt m B k) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore d) B) r ∨ Region.Sub r (blkRegion (dirCore d) B)) :
    ReadyAt m' B k := by
  rw [ReadyAt, scheduleAt_eq_of_frame _ hf fun r hr => ?_]
  · exact h
  rcases hd r hr with h' | h'
  · rw [core_eq] at h'; exact h'.sub_left (sched_sub B)
  · rw [blk_eq] at h'
    exact (Offset.disjoint B (.inr (by decide)) (by decide) (by decide)).sub_right h'

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.TripleDes.Schedule} (h : KeyArgs s rs k)
    (hr : ∀ r ∈ [Reg.rdi], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (_ : s'.wr = s.wr)
    (hf : Frame rs s.mem s'.mem) : KeyArgs s' rs k := by
  obtain ⟨p, hp, hk, hin, hfit, hdis⟩ := h
  refine ⟨p, by rw [hr .rdi List.mem_cons_self, hp], ?_, by rw [hrd]; exact hin, hfit, hdis⟩
  rw [hk]
  exact (scheduleAt_eq_of_frame p hf hdis).symm

theorem prepare_wp (d : Direction) {s : State} {B : Addr} {rs : List Region} {k : Spec.TripleDes.Schedule}
    (hB : s.gpr sb = B) (hs : ScrIn s B (dirCore d).total) (hR : (⟨B, 8 * (dirCore d).total⟩ : Region) ∈ rs)
    (hk : KeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => ReadyAt s'.mem B k ∧ s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .r12 = s.gpr .r12 ∧ s'.gpr .r13 = s.gpr .r13 ∧
      Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, rfl, hin, hfit, hdis⟩ := hk
  have hfB := hs.fit
  rw [total_eq] at hfB
  have hsep : Region.Disjoint ⟨p, 384⟩ ⟨B, 904⟩ := (hdis _ hR).sub_right (Region.sub_prefix (by rw [total_eq]; decide))
  refine WP.mono (copyN_wp (k := 48) (P := schedAddr B) (Q := p) ⟨by rw [hB], by rw [hp]; simp, by decide,
    by decide, fun w hw => ⟨_, hs.wr, by
      rw [addr_add, total_eq]; exact Offset.contains_base B (by simp only [schedSlot]; omega_using [hw]) (by simp only [schedSlot]; omega_using [hw])⟩,
    fun w hw => ⟨_, List.mem_append_left _ hin, Offset.contains_base p (by omega_using [hw]) (by omega_using [hw])⟩,
    (hsep.sub_right (sched_sub B)).symm, by omega_using []⟩) fun s' h => ?_
  refine ⟨scheduleAt_copy fun i hi => by rw [h.mem, over_at hi (by omega_using [])], by rw [h.regs _ (by decide), hB],
    h.regs _ (by decide), h.regs _ (by decide), h.regs _ (by decide), ?_, h.rd, h.wr⟩
  rw [h.mem, core_eq]
  exact (over_frame _ _ _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, sched_sub B⟩

theorem crypt_wp (d : Direction) {s : State} {B : Addr} {k : Spec.TripleDes.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B (dirCore d).total) (hr : ReadyAt s.mem B k) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .r12 = s.gpr .r12 ∧ s'.gpr .r13 = s.gpr .r13 ∧ ReadyAt s'.mem B k ∧
      Frame [coreRegion (dirCore d) B] s.mem s'.mem ∧
      (∀ j < (dirCore d).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore d) B j) (8 * (dirCore d).bw) =
        dirCipher d k (Spec.Aes.bytesAt s.mem (blkAddr (dirCore d) B j) (8 * (dirCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfB := hs.fit
  rw [total_eq] at hfB
  have hss : schedSlot = 65 := rfl
  have hw := hs.wr
  rw [total_eq] at hw
  -- `rdi`, `rsi` and `rdx` to the schedule's copy, the buffer and the block function's slots.
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s .rdi sb
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := addImm_ok s₁ .rdi (BitVec.ofNat 32 (8 * schedSlot))
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ .rsi sb
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := addImm_ok s₃ .rsi (BitVec.ofNat 32 (8 * cbcBuf))
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := movR_ok s₄ .rdx sb
  have g₅ : ∀ x, x ≠ .rdi → x ≠ .rsi → x ≠ .rdx → s₅.gpr x = s.gpr x := fun x h1 h2 h3 => by
    rw [o₅ x h3, o₄ x h2, o₃ x h2, o₂ x h1, o₁ x h1]
  have sb₅ : ∀ x, x ≠ sb → s₅.gpr sb = B := fun _ _ => by rw [g₅ _ (by decide) (by decide) (by decide), hB]
  have rdi₅ : s₅.gpr .rdi = schedAddr B := by
    rw [o₅ _ (by decide), o₄ _ (by decide), o₃ _ (by decide), r₂, r₁, hB, signExtend_small (by decide)]
  have rsi₅ : s₅.gpr .rsi = B + BitVec.ofNat 64 512 := by
    rw [o₅ _ (by decide), r₄, r₃, o₂ _ (by decide), o₁ _ (by decide), hB, signExtend_small (by decide)]; rfl
  have rdx₅ : s₅.gpr .rdx = B := by
    rw [r₅, o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide), hB]
  have mem₅ : s₅.mem = s.mem := by rw [m₅, m₄, m₃, m₂, m₁]
  have rd₅' : s₅.rd = s.rd := by rw [rd₅, rd₄, rd₃, rd₂, rd₁]
  have wr₅' : s₅.wr = s.wr := by rw [wr₅, wr₄, wr₃, wr₂, wr₁]
  rw [show (dirCore d).crypt = .seq (.block [movR .rdi sb, .alu .add .rdi (.imm (BitVec.ofNat 32 (8 * schedSlot))),
      movR .rsi sb, .alu .add .rsi (.imm (BitVec.ofNat 32 (8 * cbcBuf))), movR .rdx sb])
      (.seq (block d) (.block [movR sb .rdx])) by cases d <;> rfl]
  refine WP.seq (WP.of_runBlock ⟨s₅, by
    rw [show ([movR .rdi sb, .alu .add .rdi (.imm (BitVec.ofNat 32 (8 * schedSlot))), movR .rsi sb,
        .alu .add .rsi (.imm (BitVec.ofNat 32 (8 * cbcBuf))), movR .rdx sb] : List Instr) =
        [Impl.Aes.X86_64.movR .rdi sb] ++ ([.alu .add .rdi (.imm (BitVec.ofNat 32 (8 * schedSlot)))] ++
        ([Impl.Aes.X86_64.movR .rsi sb] ++ ([.alu .add .rsi (.imm (BitVec.ofNat 32 (8 * cbcBuf)))] ++
        ([Impl.Aes.X86_64.movR .rdx sb] : List Instr)))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some,
      runBlock_app, e₄, Option.bind_some, e₅], ?_⟩)
  -- The block.
  have inS : ∀ {t}, t + 8 ≤ 968 → InRegions s₅.wr (B + BitVec.ofNat 64 t) 8 := fun ht =>
    ⟨_, by rw [wr₅']; exact hw, Offset.contains_base B (by omega_using [ht]) (by omega_using [ht])⟩
  have hp := headPre_of s₅ (fun i hi => by rw [rdx₅]; exact inS (by omega_using [hi]))
    (fun i hi => by
      rw [rdi₅, addr_add]
      obtain ⟨r, h1, h2⟩ := inS (t := 8 * schedSlot + 8 * i) (by simp only [schedSlot]; omega_using [hi])
      exact ⟨r, List.mem_append_right _ h1, h2⟩)
    (by rw [rsi₅]; exact inS (by decide))
    (by rw [rdi₅, rdx₅]; exact Offset.disjoint_base B (by decide) (by omega_using [hss]))
    (by rw [rsi₅, rdx₅]; exact Offset.disjoint_base B (by decide) (by omega_using []))
  rw [rdi₅, mem₅, hr] at hp
  refine WP.seq (WP.mono (block_ok k (schedAddr B) d s₅ hp (by rw [rsi₅]; exact inS (by decide)))
    fun s₆ h₆ => ?_)
  obtain ⟨s₇, e₇, r₇, o₇, m₇, rd₇, wr₇⟩ := movR_ok s₆ sb .rdx
  refine WP.of_runBlock ⟨s₇, by rw [show ([movR sb .rdx] : List Instr) = [Impl.Aes.X86_64.movR sb .rdx] from rfl,
    e₇], ?_⟩
  have rdx₆ : s₆.gpr .rdx = B := by rw [h₆.regs .rdx (by decide), rdx₅]
  have sv12 : s₇.gpr .r12 = s.gpr .r12 := by
    rw [o₇ _ (by decide), h₆.saved _ (by decide), g₅ _ (by decide) (by decide) (by decide)]
  have sv13 : s₇.gpr .r13 = s.gpr .r13 := by
    rw [o₇ _ (by decide), h₆.saved _ (by decide), g₅ _ (by decide) (by decide) (by decide)]
  have fB : Frame [⟨B, 904⟩] s₅.mem s₆.mem := h₆.frame.sub fun r hr => by
    simp only [blockRegions, rsi₅, rdx₅, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, Offset.sub_base B (by decide)⟩
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  refine ⟨by rw [r₇, rdx₆], by rw [o₇ _ (by decide), h₆.regs .rsp (by decide), g₅ _ (by decide) (by decide)
    (by decide)], sv12, sv13, ?_, by rw [m₇, core_eq, ← mem₅]; exact fB,
    fun j hj => ?_, by rw [rd₇, h₆.rd, rd₅'], by rw [wr₇, h₆.wr, wr₅']⟩
  · rw [ReadyAt, m₇, scheduleAt_eq_of_frame _ h₆.frame fun r hr => ?_, mem₅, hr]
    simp only [blockRegions, rsi₅, rdx₅, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint B (.inr (by decide)) (by decide) (by decide)
    · exact Offset.disjoint_base B (by decide) (by omega_using [hss])
  · have hj0 : j = 0 := by simp only [dirCore] at hj; omega_using [hj]
    subst hj0
    have ea : blkAddr (dirCore d) B 0 = s₅.gpr .rsi := by rw [rsi₅]; rfl
    rw [dirCore_bw, ea, dirCipher_bytes, bytesAt_eq, m₇, h₆.result, mem₅]

/-- Triple DES's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Direction) : BlockSpec (dirCore d) where
  Key := Spec.TripleDes.Schedule
  cipher := dirCipher d
  KeyArgs := KeyArgs
  Ready s B k := ReadyAt s.mem B k
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.TripleDes.cipher, Spec.TripleDes.invCipher]
  layout := ⟨by simp only [dirCore]; decide, by simp only [dirCore]; decide, by simp only [dirCore]; decide,
    by simp only [dirCore]; decide, by simp only [dirCore]; decide, by simp only [dirCore]; decide⟩
  keyRegs_ok := by simp only [dirCore]; decide
  regs_ok := by simp only [dirCore, Modes.X86_64.regsOk]; decide
  keyArgs_congr h hr hrd hwr _ hf := keyArgs_congr h hr hrd hwr hf
  ready_frame h hf hd _ _ := readyAt_frame h hf hd
  prepare_wp := prepare_wp d
  crypt_wp := crypt_wp d

end VG.Proof.TripleDes.X86_64
