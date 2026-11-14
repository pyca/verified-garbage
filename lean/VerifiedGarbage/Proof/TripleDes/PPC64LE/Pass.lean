module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.Spills
import VerifiedGarbage.Proof.TripleDes.PPC64LE.RoundBody
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Write
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Block
public import VerifiedGarbage.Proof.TripleDes.Core
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.TripleDes.PPC64LE.RoundLit
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `TripleDes.PPC64LE.PassStart`, which only this module used -/

section

/-! ### `TripleDes.PPC64LE.Loop`, which only this module used -/

section

/-! ### `TripleDes.PPC64LE.RoundStep`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.TripleDes.PPC64LE

/-- The registers a round and the step to the next keep. -/
def roundStepKept : List Reg := [.r2, .r3, .r4, .r5, .r18, .r19, .r29, .r30, .r31]

theorem countDown_rules : ∀ n < 17, 1 ≤ n →
    (BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1)) ∧
    ((BitVec.ofNat 64 n - 1) != 0) = decide (n ≠ 1) := by
  decide +kernel

theorem roundAdvance_ok (s : State) :
    ∃ s', runBlock isa roundAdvance s = some s' ∧
      s'.gpr .r17 = s.gpr .r17 + s.gpr .r18 ∧
      s'.gpr .r16 = s.gpr .r16 - 1 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .r16 → r ≠ .r17 → s'.gpr r = s.gpr r) := by
  let s₁ := s.write .r17 (s.gpr .r17 + s.gpr .r18)
  let s₂ := s₁.write .r16 (s₁.gpr .r16 - BitVec.ofNat 64 1)
  refine ⟨s₂, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · rw [roundAdvance, runBlock_cons, exec_add, runStep_some, runBlock_cons,
      exec_subi (by decide) (by decide), runStep_some, runBlock_nil]
  · simp only [s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false]
  · simp only [s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false]
    rfl
  · intro r h16 h17
    simp only [s₂, s₁, gpr_write, h16, h17, ite_false]

theorem roundStep_ok (s : State)
    (l r : BitVec 32) (k : BitVec 64) (n : Nat) (hn : 1 ≤ n) (hn' : n < 17)
    (hl : s.gpr .r14 = l.setWidth 64) (hr : s.gpr .r15 = r.setWidth 64)
    (hk : s.mem.readW (s.gpr .r17) 64 = k) (hok : Ok scratchCfg s) (hc : ConstsAt s)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .r17) 8)
    (hcount : s.gpr .r16 = BitVec.ofNat 64 n) :
    ∃ s', runBlock isa (roundBody ++ roundAdvance) s = some s' ∧
      s'.gpr .r14 = r.setWidth 64 ∧
      s'.gpr .r15 = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)).setWidth 64 ∧
      s'.gpr .r17 = s.gpr .r17 + s.gpr .r18 ∧
      s'.gpr .r16 = BitVec.ofNat 64 (n - 1) ∧
      isa.eval (.nonzero .d .r16) s' = some (decide (n ≠ 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q ∈ roundStepKept, s'.gpr q = s.gpr q) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, left₁, right₁, rd₁, wr₁, keep₁, mem₁⟩ :=
    roundBody_ok s l r k hl hr hk hok hc hread
  obtain ⟨s₂, run₂, ptr₂, count₂, rd₂, wr₂, mem₂, keep₂⟩ := roundAdvance_ok s₁
  obtain ⟨hsub, hzero⟩ := countDown_rules n hn' hn
  have hcount₁ : s₁.gpr .r16 = BitVec.ofNat 64 n := (keep₁ .r16 (by decide)).trans hcount
  refine ⟨s₂, ?_, ?_, ?_, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, ?_, ?_⟩
  · simp only [runBoxes_append, run₁, Option.bind_some, run₂]
  · exact (keep₂ .r14 (by decide) (by decide)).trans left₁
  · exact (keep₂ .r15 (by decide) (by decide)).trans right₁
  · rw [ptr₂, keep₁ .r17 (by decide), keep₁ .r18 (by decide)]
  · rw [count₂, hcount₁, hsub]
  · change VG.PPC64LE.eval (.nonzero .d .r16) s₂ = _
    simp only [VG.PPC64LE.eval, State.read, Size.bits, BitVec.setWidth_eq, count₂, hcount₁, hzero]
  · intro q hq
    have hq' : q ∈ roundOuterKept := by revert hq; cases q <;> decide
    have hneq : q ≠ .r16 ∧ q ≠ .r17 := by revert hq; cases q <;> decide
    exact (keep₂ q hneq.1 hneq.2).trans (keep₁ q hq')
  · rw [mem₂, mem₁]; exact Frame.refl _ _

end VG.Proof.TripleDes.PPC64LE

end

end


@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.TripleDes.PPC64LE
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix feistelStep)

def keyAddr (base : Addr) (direction : Direction) (j : Nat) : Addr :=
  base + BitVec.ofNat 64 (8 * (if direction = .encrypt then j else 15 - j))

/-- The key step of a pass, in `r18`. -/
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
  left : s.gpr .r14 = (roundPrefix keys direction (16 - n) v).1.setWidth 64
  right : s.gpr .r15 = (roundPrefix keys direction (16 - n) v).2.setWidth 64
  counter : s.gpr .r16 = BitVec.ofNat 64 n
  pointer : s.gpr .r17 = keyAddr base direction (16 - n)
  step : s.gpr .r18 = stepVal direction
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem

structure LoopPost (keys : DesSchedule) (direction : Direction)
    (origin : State) (v : BitVec 32 × BitVec 32) (s : State) : Prop where
  left : s.gpr .r14 = (roundPrefix keys direction 16 v).1.setWidth 64
  right : s.gpr .r15 = (roundPrefix keys direction 16 v).2.setWidth 64
  counter : s.gpr .r16 = 0
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem

theorem loopStep (keys : DesSchedule) (direction : Direction) (base : Addr)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok scratchCfg origin) (hc : ConstsAt origin)
    (hread : ∀ j < 16, InRegions (origin.rd ++ origin.wr) (keyAddr base direction j) 8)
    (hsep : ∀ j < 16, (⟨keyAddr base direction j, 8⟩ : Region).Disjoint (spillRegion origin))
    (hkeys : ∀ j < 16, (origin.mem.readW (keyAddr base direction j) 64).setWidth 48 =
      roundKey keys direction j)
    (n : Nat) (s : State) (hs : LoopInv keys direction base origin v n s) :
    WP isa (.block (roundBody ++ roundAdvance)) s (fun s' =>
      (isa.eval (.nonzero .d .r16) s' = some false ∧ LoopPost keys direction origin v s') ∨
      (isa.eval (.nonzero .d .r16) s' = some true ∧ ∃ m < n, LoopInv keys direction base origin v m s')) := by
  have hj : 16 - n < 16 := by omega_using [hs.positive]
  have hwork : spillRegion s = spillRegion origin := by
    simp only [spillRegion, hs.regs .r5 (by decide)]
  have hokS : Ok scratchCfg s := hok.congr
    (hs.regs .r5 (by decide)) (hs.regs .r5 (by decide)) hs.rd hs.wr
  have hreadS : InRegions (s.rd ++ s.wr) (s.gpr .r17) 8 := by
    rw [hs.rd, hs.wr, hs.pointer]; exact hread _ hj
  have hcS : ConstsAt s := hc.of_frame (hs.regs .r5 (by decide)) hs.frame
  have hk : (s.mem.readW (s.gpr .r17) 64).setWidth 48 = roundKey keys direction (16 - n) := by
    rw [hs.pointer]
    have hmem := hs.frame.readW (a := keyAddr base direction (16 - n)) (w := 64)
      (r := ⟨keyAddr base direction (16 - n), 8⟩)
      (Region.contains_self _ _) (fun q hq => by
        obtain rfl := List.mem_singleton.mp hq
        exact hsep _ hj) (by decide)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hkeys _ hj)
  obtain ⟨s', run, left, right, ptr, count, flag, rd, wr, regs, frame⟩ :=
    roundStep_ok s _ _ (s.mem.readW (s.gpr .r17) 64) n hs.positive
      (by omega_using [hs.bounded]) hs.left hs.right rfl hokS hcS hreadS
      hs.counter
  have hidx : 16 - (n - 1) = 16 - n + 1 := by
    omega_using [hs.positive, hs.bounded]
  have hleft : s'.gpr .r14 = (roundPrefix keys direction (16 - (n - 1)) v).1.setWidth 64 := by
    rw [hidx]
    exact left.trans (congrArg (fun pair => pair.1.setWidth 64)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  have hright : s'.gpr .r15 = (roundPrefix keys direction (16 - (n - 1)) v).2.setWidth 64 := by
    rw [hidx]
    have hval := congrArg (fun key =>
      ((roundPrefix keys direction (16 - n) v).1 ^^^
        Spec.TripleDes.roundFunction (roundPrefix keys direction (16 - n) v).2 key).setWidth 64) hk
    exact (right.trans hval).trans (congrArg (fun pair => pair.2.setWidth 64)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  have hframe : Frame [spillRegion origin] origin.mem s'.mem := by
    rw [hwork] at frame
    exact hs.frame.trans frame
  have hregs : ∀ q ∈ roundStepKept, s'.gpr q = origin.gpr q :=
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
        hleft, hright, count, ?_, (regs .r18 (by decide)).trans hs.step,
        rd.trans hs.rd, wr.trans hs.wr, hregs, hframe⟩
      rw [ptr, hs.pointer, hs.step, keyAddr_step base direction (16 - n) (by
        omega_using [hs.positive, hlast]), ← hidx]

/-- The complete sixteen-round loop, in either key order. -/
theorem roundsLoop_ok (keys : DesSchedule) (direction : Direction) (base : Addr)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok scratchCfg origin) (hc : ConstsAt origin)
    (hl : origin.gpr .r14 = v.1.setWidth 64) (hr : origin.gpr .r15 = v.2.setWidth 64)
    (hptr : origin.gpr .r17 = keyAddr base direction 0)
    (hcount : origin.gpr .r16 = BitVec.ofNat 64 16)
    (hstep : origin.gpr .r18 = stepVal direction)
    (hread : ∀ j < 16, InRegions (origin.rd ++ origin.wr) (keyAddr base direction j) 8)
    (hsep : ∀ j < 16, (⟨keyAddr base direction j, 8⟩ : Region).Disjoint (spillRegion origin))
    (hkeys : ∀ j < 16, (origin.mem.readW (keyAddr base direction j) 64).setWidth 48 =
      roundKey keys direction j) :
    WP isa (.loop (.block (roundBody ++ roundAdvance)) (.nonzero .d .r16))
      origin (LoopPost keys direction origin v) := by
  apply WP.loop (M := isa) (body := .block (roundBody ++ roundAdvance))
    (c := .nonzero .d .r16) (Q := LoopPost keys direction origin v) (LoopInv keys direction base origin v)
    (loopStep keys direction base origin v hok hc hread hsep hkeys)
    16 origin
  exact ⟨by decide, by decide, hl, hr, hcount, hptr, hstep, rfl, rfl,
    fun _ _ => rfl, Frame.refl _ _⟩

end VG.Proof.TripleDes.PPC64LE

end

end


@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.Impl.TripleDes.PPC64LE
open VG.Spec.TripleDes (Direction)

def passOffset (component : Nat) (direction : Direction) : Nat :=
  128 * component + if direction = .encrypt then 0 else 120

theorem passOffset_bound : ∀ c < 3, ∀ d : Direction, passOffset c d < 2 ^ 15 := by
  intro c hc d
  cases d <;> simp only [passOffset, reduceCtorEq, ite_true, ite_false] <;> omega_using [hc]

theorem passStart_ok (component : Nat) (hc : component < 3) (direction : Direction)
    (s : State) :
    ∃ s', runBlock isa (passStart component direction) s = some s' ∧
      s'.gpr .r17 = s.gpr .r3 + BitVec.ofNat 64 (passOffset component direction) ∧
      s'.gpr .r16 = BitVec.ofNat 64 16 ∧ s'.mem = s.mem ∧
      s'.gpr .r18 = stepVal direction ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r16 → r ≠ .r17 → r ≠ .r18 → s'.gpr r = s.gpr r) := by
  have hb := passOffset_bound component hc direction
  let s₁ := s.write .r17 (s.gpr .r3 + BitVec.ofNat 64 (passOffset component direction))
  let s₂ := s₁.write .r16 (BitVec.ofNat 64 16)
  let s₃ := s₂.write .r18 (BitVec.ofNat 64 0)
  let s₄ := s₃.write .r18 (stepVal direction)
  have e₄ : exec (if direction = .encrypt then .addi .r18 .r18 8 else .subi .r18 .r18 8) s₃ =
      some s₄ := by
    cases direction
    · rw [ite_eq_left rfl, exec_addi (by decide) (by decide)]
      simp only [s₄, s₃, gpr_write, ite_true, stepVal]
      rfl
    · rw [ite_eq_right (by decide), exec_subi (by decide) (by decide)]
      simp only [s₄, s₃, gpr_write, ite_true, stepVal, reduceCtorEq, ite_false]
      rfl
  refine ⟨s₄, ?_, ?_, ?_, rfl, ?_, rfl, rfl, ?_⟩
  · rw [passStart, runBlock_cons, show (128 * component + if direction = .encrypt then 0 else 120)
        = passOffset component direction from rfl,
      exec_addi (by decide) hb, runStep_some, runBlock_cons, imm, exec_li (by decide),
      runStep_some, runBlock_cons, imm, exec_li (by decide), runStep_some, runBlock_cons, e₄,
      runStep_some, runBlock_nil]
  · simp only [s₄, s₃, s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false]
  · simp only [s₄, s₃, s₂, s₁, gpr_write, reduceCtorEq, ite_true, ite_false]
  · simp only [s₄, gpr_write, ite_true]
  · intro r h16 h17 h18
    simp only [s₄, s₃, s₂, s₁, gpr_write, h16, h17, h18, ite_false]

end VG.Proof.TripleDes.PPC64LE

end

end


@[expose] public section

namespace VG.Proof.TripleDes.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.TripleDes.PPC64LE
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix)

/-- What choosing and starting the pass of component `c` and direction `d` leaves. -/
structure StartPost (c : Nat) (d : Direction) (s t : State) : Prop where
  ptr : t.gpr .r17 = s.gpr .r3 + BitVec.ofNat 64 (passOffset c d)
  count : t.gpr .r16 = BitVec.ofNat 64 16
  mem : t.mem = s.mem
  step : t.gpr .r18 = stepVal d
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  regs : ∀ r, r ≠ .r16 → r ≠ .r17 → r ≠ .r18 → r ≠ .r20 → t.gpr r = s.gpr r

theorem passOf_lt (d : Direction) (p : Nat) : (passOf d p).1 < 3 := by
  cases d <;> (rcases p with _ | _ | _ | _ | p) <;> simp [passOf]

theorem subi_zero (x : BitVec 64) (p k : Nat) (hx : x = BitVec.ofNat 64 p) (hp : 1 ≤ p ∧ p ≤ 3)
    (hk : k ≤ 3) : ((x - BitVec.ofNat 64 k) == 0) = (p == k) := by
  subst hx
  rcases hp with ⟨h1, h3⟩
  rcases p with _ | _ | _ | _ | p <;> (try omega) <;>
    rcases k with _ | _ | _ | _ | k <;> first | omega | decide

theorem select_ok (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) (s : State)
    (hpasses : s.gpr .r19 = BitVec.ofNat 64 p) :
    WP isa (passSelect d) s (StartPost (passOf d p).1 (passOf d p).2 s) := by
  have branch : ∀ (t : State) (q : Nat), q = p → t.mem = s.mem → t.rd = s.rd →
      t.wr = s.wr → (∀ r, r ≠ .r20 → t.gpr r = s.gpr r) →
      WP isa (.block (passStart (passOf d q).1 (passOf d q).2)) t
        (StartPost (passOf d p).1 (passOf d p).2 s) := by
    intro t q hq hm hrd hwr hg
    subst hq
    obtain ⟨u, run, ptr, count, mem, step, rd, wr, regs⟩ := passStart_ok (passOf d q).1
      (passOf_lt d q) (passOf d q).2 t
    refine WP.of_runBlock ⟨u, run, ?_, count, mem.trans hm, step, rd.trans hrd, wr.trans hwr, ?_⟩
    · rw [ptr, hg .r3 (by decide)]
    · intro r h16 h17 h18 h20
      exact (regs r h16 h17 h18).trans (hg r h20)
  let t₁ := s.write .r20 (s.gpr .r19 - BitVec.ofNat 64 3)
  have hg₁ : ∀ r, r ≠ .r20 → t₁.gpr r = s.gpr r := fun r h => gpr_write_of_ne _ _ h
  apply WP.seq
  refine WP.of_runBlock ⟨t₁, by
    rw [runBlock_cons, exec_subi (by decide) (by decide), runStep_some, runBlock_nil], ?_⟩
  have zf₁ : isa.eval (.zero .d .r20) t₁ = some (p == 3) := by
    change VG.PPC64LE.eval (.zero .d .r20) t₁ = _
    simp only [VG.PPC64LE.eval, State.read, Size.bits, BitVec.setWidth_eq, t₁, gpr_write_self]
    rw [subi_zero _ p 3 hpasses hp (by decide)]
  apply WP.ite (p == 3) zf₁
  · intro h3
    exact branch t₁ 3 (by simpa using h3 : p = 3).symm rfl rfl rfl hg₁
  · intro h3
    apply WP.seq
    let t₂ := t₁.write .r20 (t₁.gpr .r19 - BitVec.ofNat 64 2)
    refine WP.of_runBlock ⟨t₂, by
      rw [runBlock_cons, exec_subi (by decide) (by decide), runStep_some, runBlock_nil], ?_⟩
    have zf₂ : isa.eval (.zero .d .r20) t₂ = some (p == 2) := by
      change VG.PPC64LE.eval (.zero .d .r20) t₂ = _
      simp only [VG.PPC64LE.eval, State.read, Size.bits, BitVec.setWidth_eq, t₂, gpr_write_self]
      rw [subi_zero _ p 2 ((hg₁ .r19 (by decide)).trans hpasses) hp (by decide)]
    have hg₂ : ∀ r, r ≠ .r20 → t₂.gpr r = s.gpr r := fun r h =>
      (gpr_write_of_ne _ _ h).trans (hg₁ r h)
    apply WP.ite (p == 2) zf₂
    · intro h2
      exact branch t₂ 2 (by simpa using h2 : p = 2).symm rfl rfl rfl hg₂
    · intro h2
      have hp3 : p ≠ 3 := by simpa using h3
      have hp2 : p ≠ 2 := by simpa using h2
      exact branch t₂ 1 (by omega_using [hp, hp3, hp2]) rfl rfl rfl hg₂

/-- The registers a pass keeps. -/
def passKept : List Reg := [.r2, .r3, .r4, .r5, .r29, .r30, .r31]

structure PassPost (keys : DesSchedule) (direction : Direction)
    (origin : State) (v : BitVec 32 × BitVec 32) (n : Nat) (s : State) : Prop where
  left : s.gpr .r14 = (roundPrefix keys direction 16 v).2.setWidth 64
  right : s.gpr .r15 = (roundPrefix keys direction 16 v).1.setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  regs : ∀ q ∈ passKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem
  passes : s.gpr .r19 = BitVec.ofNat 64 (n - 1)
  zf : isa.eval (.nonzero .d .r19) s = some (decide (n ≠ 1))

theorem passCountAdvance_ok (s : State) :
    ∃ s', runBlock isa passCountAdvance s = some s' ∧
      s'.gpr .r19 = s.gpr .r19 - 1 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .r19 → s'.gpr r = s.gpr r) :=
  ⟨s.write .r19 (s.gpr .r19 - BitVec.ofNat 64 1), by
    rw [passCountAdvance, runBlock_cons, exec_subi (by decide) (by decide), runStep_some,
      runBlock_nil], gpr_write_self _ _ _, rfl, rfl, rfl, fun _ h => gpr_write_of_ne _ _ h⟩

/-- A complete DES pass: the choice of its keys by the passes left, its
sixteen rounds, the final half swap and the passes left counted down. -/
theorem pass_ok (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3)
    (keys : DesSchedule) (base : Addr) (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok scratchCfg origin) (hc : ConstsAt origin)
    (hl : origin.gpr .r14 = v.1.setWidth 64) (hr : origin.gpr .r15 = v.2.setWidth 64)
    (hpasses : origin.gpr .r19 = BitVec.ofNat 64 p)
    (hptr : origin.gpr .r3 + BitVec.ofNat 64 (passOffset (passOf d p).1 (passOf d p).2) =
      keyAddr base (passOf d p).2 0)
    (hread : ∀ j < 16, InRegions (origin.rd ++ origin.wr) (keyAddr base (passOf d p).2 j) 8)
    (hsep : ∀ j < 16, (⟨keyAddr base (passOf d p).2 j, 8⟩ : Region).Disjoint (spillRegion origin))
    (hkeys : ∀ j < 16, (origin.mem.readW (keyAddr base (passOf d p).2 j) 64).setWidth 48 =
      roundKey keys (passOf d p).2 j) :
    WP isa (pass d) origin (PassPost keys (passOf d p).2 origin v p) := by
  apply WP.seq
  refine WP.mono (select_ok d hp origin hpasses) fun s hs => ?_
  generalize (passOf d p).2 = dir at hs hptr hread hsep hkeys ⊢
  have hbase : s.gpr .r5 = origin.gpr .r5 := hs.regs .r5 (by decide) (by decide) (by decide)
    (by decide)
  have hspill : spillRegion s = spillRegion origin := by simp only [spillRegion, hbase]
  have hloop := roundsLoop_ok keys dir base s v
    (hok.congr hbase hbase hs.rd hs.wr) (hc.congr hbase hs.mem)
    ((hs.regs .r14 (by decide) (by decide) (by decide) (by decide)).trans hl)
    ((hs.regs .r15 (by decide) (by decide) (by decide) (by decide)).trans hr)
    (hs.ptr.trans hptr) hs.count hs.step
    (by rw [hs.rd, hs.wr]; exact hread)
    (by rw [hspill]; exact hsep) (by rw [hs.mem]; exact hkeys)
  apply WP.seq
  refine WP.mono hloop fun s₂ hs₂ => ?_
  obtain ⟨s₃, run₃, left₃, right₃, rd₃, wr₃, mem₃, regs₃⟩ := swapHalves_ok s₂
  obtain ⟨s₄, run₄, p₄, rd₄, wr₄, mem₄, regs₄⟩ := passCountAdvance_ok s₃
  have hp₃ : s₃.gpr .r19 = BitVec.ofNat 64 p :=
    (regs₃ .r19 (by decide)).trans ((hs₂.regs .r19 (by decide)).trans
      ((hs.regs .r19 (by decide) (by decide) (by decide) (by decide)).trans hpasses))
  obtain ⟨hsub, hzero⟩ := countDown_rules p (by omega_using [hp]) hp.1
  refine WP.of_runBlock ⟨s₄, by simp only [runBoxes_append, run₃, Option.bind_some, run₄], ?_⟩
  refine ⟨?_, ?_, rd₄.trans (rd₃.trans (hs₂.rd.trans hs.rd)),
    wr₄.trans (wr₃.trans (hs₂.wr.trans hs.wr)), ?_, ?_, ?_, ?_⟩
  · exact (regs₄ .r14 (by decide)).trans (left₃.trans hs₂.right)
  · exact (regs₄ .r15 (by decide)).trans (right₃.trans hs₂.left)
  · intro q hq
    have hq' : q ∈ roundOuterKept := by revert hq; cases q <;> decide
    have hq'' : q ∈ roundStepKept := by revert hq; cases q <;> decide
    have hne : q ≠ .r16 ∧ q ≠ .r17 ∧ q ≠ .r18 ∧ q ≠ .r19 ∧ q ≠ .r20 := by
      revert hq; cases q <;> decide
    exact (regs₄ q hne.2.2.2.1).trans ((regs₃ q hq').trans ((hs₂.regs q hq'').trans
      (hs.regs q hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.2)))
  · have hf := hs₂.frame
    rw [hspill, hs.mem] at hf
    rw [mem₄, mem₃]
    exact hf
  · rw [p₄, hp₃, hsub]
  · change VG.PPC64LE.eval (.nonzero .d .r19) s₄ = some (decide (p ≠ 1))
    simp only [VG.PPC64LE.eval, State.read, Size.bits, BitVec.setWidth_eq, p₄, hp₃]
    rw [hsub]
    rcases hp with ⟨h1, h3⟩
    rcases p with _ | _ | _ | _ | p <;> first | omega | decide

end VG.Proof.TripleDes.PPC64LE
