module

public import VerifiedGarbage.Proof.TripleDes.PPC64LE.PassStart
import VerifiedGarbage.Proof.TripleDes.PPC64LE.RoundBody
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Box
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Write
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

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
      exact branch t₂ 1 (by omega) rfl rfl rfl hg₂

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
    (hok : Ok sboxCfg origin)
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
    (hok.congr hbase hbase hs.rd hs.wr)
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
  obtain ⟨hsub, hzero⟩ := countDown_rules p (by omega) hp.1
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
