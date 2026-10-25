module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Loop
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd

/-!
# A DES pass

`pass_ok`: the choice of the pass's keys by the passes left, its sixteen
rounds, the final half swap and the passes left counted down.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.RegUpd VG.Impl.TripleDes.RISCV64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix)

def passOffset (component : Nat) (direction : Direction) : Nat :=
  keyOff + 128 * component + if direction = .encrypt then 0 else 120

theorem passOffset_bound : ∀ c < 3, ∀ d : Direction, passOffset c d < 2048 := by
  intro c hc d
  cases d <;> simp only [passOffset, keyOff, reduceCtorEq, ite_true, ite_false] <;> omega

theorem passStart_ok (component : Nat) (hc : component < 3) (direction : Direction)
    (s : State) :
    ∃ s', runBlock isa (passStart component direction) s = some s' ∧
      s'.gpr kp = s.gpr sb + BitVec.ofNat 64 (passOffset component direction) ∧
      s'.gpr cnt = BitVec.ofNat 64 16 ∧ s'.mem = s.mem ∧
      s'.gpr kstep = stepVal direction ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ cnt → r ≠ kp → r ≠ kstep → s'.gpr r = s.gpr r) := by
  have hb := passOffset_bound component hc direction
  let s₁ := s.write kp (s.gpr sb + BitVec.ofInt 64 (passOffset component direction : Nat))
  let s₂ := s₁.write cnt (BitVec.ofInt 64 16)
  let s₃ := s₂.write kstep (stepVal direction)
  have e₃ : exec (.li kstep (if direction = .encrypt then 8 else -8)) s₂ = some s₃ := by
    rw [exec_li (by cases direction <;> decide)]
    rfl
  refine ⟨s₃, ?_, ?_, ?_, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · rw [passStart, runBlock_cons, show (keyOff + 128 * component +
        if direction = .encrypt then 0 else 120) = passOffset component direction from rfl,
      exec_addi (by constructor <;> omega), runStep_some, runBlock_cons, exec_li (by decide),
      runStep_some, runBlock_cons, e₃, runStep_some, runBlock_nil]
  · simp only [s₃, s₂, s₁, gpr_write, kp, cnt, kstep, sb, reduceCtorEq, ite_true, ite_false,
      BitVec.ofInt_natCast]
  · simp only [s₃, s₂, s₁, gpr_write, kp, cnt, kstep, reduceCtorEq, ite_true, ite_false]
    rfl
  · simp only [s₃, gpr_write, ite_true]
  · intro r h16 h17 h18
    simp only [s₃, s₂, s₁, gpr_write, h16, h17, h18, ite_false]

/-- What choosing and starting the pass of component `c` and direction `d` leaves. -/
structure StartPost (c : Nat) (d : Direction) (s t : State) : Prop where
  ptr : t.gpr kp = s.gpr sb + BitVec.ofNat 64 (passOffset c d)
  count : t.gpr cnt = BitVec.ofNat 64 16
  mem : t.mem = s.mem
  stp : t.gpr kstep = stepVal d
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  regs : ∀ r, r ≠ cnt → r ≠ kp → r ≠ kstep → r ≠ .t6 → t.gpr r = s.gpr r

theorem passOf_lt (d : Direction) (p : Nat) : (passOf d p).1 < 3 := by
  cases d <;> (rcases p with _ | _ | _ | _ | p) <;> simp [passOf]

theorem subi_zero (x : BitVec 64) (p k : Nat) (hx : x = BitVec.ofNat 64 p) (hp : 1 ≤ p ∧ p ≤ 3)
    (hk : k ≤ 3) : ((x + BitVec.ofInt 64 (-(k : Int))) == 0) = (p == k) := by
  subst hx
  rcases hp with ⟨h1, h3⟩
  rcases p with _ | _ | _ | _ | p <;> (try omega) <;>
    rcases k with _ | _ | _ | _ | k <;> first | omega | decide

theorem select_ok (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) (s : State)
    (hpasses : s.gpr passes = BitVec.ofNat 64 p) :
    WP isa (passSelect d) s (StartPost (passOf d p).1 (passOf d p).2 s) := by
  have branch : ∀ (t : State) (q : Nat), q = p → t.mem = s.mem → t.rd = s.rd →
      t.wr = s.wr → t.sp = s.sp → (∀ r, r ≠ .t6 → t.gpr r = s.gpr r) →
      WP isa (.block (passStart (passOf d q).1 (passOf d q).2)) t
        (StartPost (passOf d p).1 (passOf d p).2 s) := by
    intro t q hq hm hrd hwr hsp hg
    subst hq
    obtain ⟨u, run, ptr, count, mem, kst, rd, wr, sp, regs⟩ := passStart_ok (passOf d q).1
      (passOf_lt d q) (passOf d q).2 t
    refine WP.of_runBlock ⟨u, run, ?_, count, mem.trans hm, kst, rd.trans hrd, wr.trans hwr,
      sp.trans hsp, ?_⟩
    · rw [ptr, hg sb (by decide)]
    · intro r h16 h17 h18 h20
      exact (regs r h16 h17 h18).trans (hg r h20)
  let t₁ := s.write .t6 (s.gpr passes + BitVec.ofInt 64 (-3))
  have hg₁ : ∀ r, r ≠ .t6 → t₁.gpr r = s.gpr r := fun r h => gpr_write_of_ne _ _ h
  apply WP.seq
  refine WP.of_runBlock ⟨t₁, by
    rw [runBlock_cons, exec_addi (by decide), runStep_some, runBlock_nil], ?_⟩
  have zf₁ : isa.eval (.zero .t6) t₁ = some (p == 3) := by
    change VG.RISCV64.eval (.zero .t6) t₁ = _
    simp only [VG.RISCV64.eval, t₁, gpr_write_self]
    rw [show BitVec.ofInt 64 (-3) = BitVec.ofInt 64 (-((3 : Nat) : Int)) from rfl,
      subi_zero _ p 3 hpasses hp (by decide)]
  apply WP.ite (p == 3) zf₁
  · intro h3
    exact branch t₁ 3 (by simpa using h3 : p = 3).symm rfl rfl rfl rfl hg₁
  · intro h3
    apply WP.seq
    let t₂ := t₁.write .t6 (t₁.gpr passes + BitVec.ofInt 64 (-2))
    refine WP.of_runBlock ⟨t₂, by
      rw [runBlock_cons, exec_addi (by decide), runStep_some, runBlock_nil], ?_⟩
    have zf₂ : isa.eval (.zero .t6) t₂ = some (p == 2) := by
      change VG.RISCV64.eval (.zero .t6) t₂ = _
      simp only [VG.RISCV64.eval, t₂, gpr_write_self]
      rw [show BitVec.ofInt 64 (-2) = BitVec.ofInt 64 (-((2 : Nat) : Int)) from rfl,
        subi_zero _ p 2 ((hg₁ passes (by decide)).trans hpasses) hp (by decide)]
    have hg₂ : ∀ r, r ≠ .t6 → t₂.gpr r = s.gpr r := fun r h =>
      (gpr_write_of_ne _ _ h).trans (hg₁ r h)
    apply WP.ite (p == 2) zf₂
    · intro h2
      exact branch t₂ 2 (by simpa using h2 : p = 2).symm rfl rfl rfl rfl hg₂
    · intro h2
      have hp3 : p ≠ 3 := by simpa using h3
      have hp2 : p ≠ 2 := by simpa using h2
      exact branch t₂ 1 (by omega) rfl rfl rfl rfl hg₂

/-- The registers a pass keeps. -/
def passKept : List Reg := [.ra, .s1, .s2, .s3, .s4, .a0]

structure PassPost (keys : DesSchedule) (direction : Direction)
    (origin : State) (v : BitVec 32 × BitVec 32) (n : Nat) (s : State) : Prop where
  left : s.gpr lReg = (roundPrefix keys direction 16 v).2.setWidth 64
  right : s.gpr rReg = (roundPrefix keys direction 16 v).1.setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ passKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem
  pcount : s.gpr passes = BitVec.ofNat 64 (n - 1)
  zf : isa.eval (.nonzero passes) s = some (decide (n ≠ 1))

theorem passCountAdvance_ok (s : State) :
    ∃ s', runBlock isa passCountAdvance s = some s' ∧
      s'.gpr passes = s.gpr passes + BitVec.ofInt 64 (-1) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ (∀ r, r ≠ passes → s'.gpr r = s.gpr r) :=
  ⟨s.write passes (s.gpr passes + BitVec.ofInt 64 (-1)), by
    rw [passCountAdvance, runBlock_cons, exec_addi (by decide), runStep_some,
      runBlock_nil], gpr_write_self _ _ _, rfl, rfl, rfl, rfl, fun _ h => gpr_write_of_ne _ _ h⟩

/-- A complete DES pass. -/
theorem pass_ok (d : Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3)
    (keys : DesSchedule) (base : Addr) (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hl : origin.gpr lReg = v.1.setWidth 64) (hr : origin.gpr rReg = v.2.setWidth 64)
    (hpasses : origin.gpr passes = BitVec.ofNat 64 p)
    (hptr : origin.gpr sb + BitVec.ofNat 64 (passOffset (passOf d p).1 (passOf d p).2) =
      keyAddr base (passOf d p).2 0)
    (hkeys : KeysAt keys (passOf d p).2 base origin) :
    WP isa (pass d) origin (PassPost keys (passOf d p).2 origin v p) := by
  apply WP.seq
  refine WP.mono (select_ok d hp origin hpasses) fun s hs => ?_
  generalize (passOf d p).2 = dir at hs hptr hkeys ⊢
  have hbase : s.gpr sb = origin.gpr sb := hs.regs sb (by decide) (by decide) (by decide)
    (by decide)
  have hspill : spillRegion s = spillRegion origin := by simp only [spillRegion, hbase]
  have hkeys' : KeysAt keys dir base s :=
    ⟨by rw [hs.rd, hs.wr]; exact hkeys.read, hkeys.al, by rw [hspill]; exact hkeys.sep,
      by rw [hs.mem]; exact hkeys.keys⟩
  have hloop := roundsLoop_ok keys dir base s v
    (hok.congr hbase hbase hs.rd hs.wr)
    ((hs.regs lReg (by decide) (by decide) (by decide) (by decide)).trans hl)
    ((hs.regs rReg (by decide) (by decide) (by decide) (by decide)).trans hr)
    (hs.ptr.trans hptr) hs.count hs.stp hkeys'
  apply WP.seq
  refine WP.mono hloop fun s₂ hs₂ => ?_
  obtain ⟨s₃, run₃, left₃, right₃, rd₃, wr₃, sp₃, mem₃, regs₃⟩ := swapHalves_ok s₂
  obtain ⟨s₄, run₄, p₄, rd₄, wr₄, sp₄, mem₄, regs₄⟩ := passCountAdvance_ok s₃
  have hp₃ : s₃.gpr passes = BitVec.ofNat 64 p :=
    (regs₃ passes (by decide)).trans ((hs₂.regs passes (by decide)).trans
      ((hs.regs passes (by decide) (by decide) (by decide) (by decide)).trans hpasses))
  obtain ⟨hsub, hzero⟩ := countDown_rules p (by omega) hp.1
  refine WP.of_runBlock ⟨s₄, by simp only [runBoxes_append, run₃, Option.bind_some, run₄], ?_⟩
  refine ⟨?_, ?_, rd₄.trans (rd₃.trans (hs₂.rd.trans hs.rd)),
    wr₄.trans (wr₃.trans (hs₂.wr.trans hs.wr)), sp₄.trans (sp₃.trans (hs₂.sp.trans hs.sp)),
    ?_, ?_, ?_, ?_⟩
  · exact (regs₄ lReg (by decide)).trans (left₃.trans hs₂.right)
  · exact (regs₄ rReg (by decide)).trans (right₃.trans hs₂.left)
  · intro q hq
    have hq' : q ∈ roundOuterKept := by revert hq; cases q <;> decide
    have hq'' : q ∈ roundStepKept := by revert hq; cases q <;> decide
    have hne : q ≠ cnt ∧ q ≠ kp ∧ q ≠ kstep ∧ q ≠ passes ∧ q ≠ .t6 := by
      revert hq; cases q <;> decide
    exact (regs₄ q hne.2.2.2.1).trans ((regs₃ q hq').trans ((hs₂.regs q hq'').trans
      (hs.regs q hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.2)))
  · have hf := hs₂.frame
    rw [hspill, hs.mem] at hf
    rw [mem₄, mem₃]
    exact hf
  · rw [p₄, hp₃, hsub]
  · change VG.RISCV64.eval (.nonzero passes) s₄ = some (decide (p ≠ 1))
    simp only [VG.RISCV64.eval, p₄, hp₃]
    rw [hsub]
    rcases hp with ⟨h1, h3⟩
    rcases p with _ | _ | _ | _ | p <;> first | omega | decide

end VG.Proof.TripleDes.RISCV64
