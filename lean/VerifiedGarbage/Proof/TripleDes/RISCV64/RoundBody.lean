module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Round
public import VerifiedGarbage.Proof.TripleDes.RISCV64.Spills
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd

/-!
# A round

`box_ok`: one S-box's contribution, from its inputs through the circuit to
its outputs; `roundBody_ok`: the eight of them and the half swap, the
standard DES round; `roundStep_ok`: with the next key and the round counted.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.RegUpd VG.Impl.TripleDes.RISCV64
open VG.Proof.TripleDes (roundChunk boxPiece contribution contributions_roundFunction)

theorem runBoxes_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

/-- One complete DES S-box contribution, including E/key input extraction,
the Boolean circuit, and P output placement. -/
theorem box_ok (i : Nat) (hi : i < 8) (s : State) (hok : Ok sboxCfg s)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr kp) 8) (hal : (s.gpr kp).toNat % 8 = 0) :
    ∃ s', runBlock isa (box i) s = some s' ∧
      s'.gpr lReg = s.gpr lReg ^^^ contribution (s.gpr rReg) (s.mem.readW (s.gpr kp) 64) i ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r ∈ roundKept, s'.gpr r = s.gpr r) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, chunk, rd₁, wr₁, sp₁, mem₁, keep₁⟩ := roundInput_chunk i hi s hread hal
  have kept₁ : ∀ r ∈ lReg :: roundKept, s₁.gpr r = s.gpr r :=
    fun r hr => keep₁ r (roundInput_keep i hi r hr)
  have hok₁ : Ok sboxCfg s₁ := hok.congr
    (kept₁ sb (by decide)) (kept₁ sb (by decide)) rd₁ wr₁
  obtain ⟨s₂, run₂, bits, rd₂, wr₂, sp₂, keep₂, _⟩ := sbox_ok i hi hok₁
  have hbits : ∀ j < 4, (s₂.gpr (q j)).getLsbD 0 =
      (Spec.TripleDes.sBox i (roundChunk i ((s.gpr rReg).setWidth 32)
        ((s.mem.readW (s.gpr kp) 64).setWidth 48))).getLsbD j := by
    intro j hj
    rw [bits j hj 0 (by decide), chunk]
  obtain ⟨s₃, run₃, value, rd₃, wr₃, sp₃, mem₃, keep₃⟩ := roundOutput_piece i hi s₂ _ hbits
  refine ⟨s₃, ?_, ?_, rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁),
    sp₃.trans (sp₂.trans sp₁), ?_, ?_⟩
  · simp only [box, runBoxes_append, run₁, Option.bind_some, run₂, run₃]
  · rw [value, keep₂ lReg (by decide), kept₁ lReg (by decide)]
    rfl
  · intro r hr
    rw [keep₃ r (roundOutput_keep i hi r hr), keep₂ r ?_, kept₁ r (List.mem_cons_of_mem _ hr)]
    revert hr; decide +revert
  · have hf := sbox_spillFrame i hi s₁ s₂ run₂
    have hregion : spillRegion s₁ = spillRegion s := by
      simp only [spillRegion, kept₁ sb (by decide)]
    rw [hregion, mem₁] at hf
    rw [mem₃]
    exact hf

/-- Compose any ordered list of S-boxes. The schedule word and Feistel
right half stay fixed; each contribution is XORed into the left half. -/
theorem boxes_ok (indices : List Nat) (hindices : ∀ i ∈ indices, i < 8)
    (r k : BitVec 64) (s : State) (hok : Ok sboxCfg s)
    (hr : s.gpr rReg = r) (hk : s.mem.readW (s.gpr kp) 64 = k)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr kp) 8) (hal : (s.gpr kp).toNat % 8 = 0)
    (hsep : (⟨s.gpr kp, 8⟩ : Region).Disjoint (spillRegion s)) :
    ∃ s', runBlock isa (indices.flatMap box) s = some s' ∧
      s'.gpr lReg = indices.foldl (fun out i => out ^^^ contribution r k i) (s.gpr lReg) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ roundKept, s'.gpr q = s.gpr q) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  induction indices generalizing s with
  | nil =>
    exact ⟨s, runBlock_nil, rfl, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | cons i indices ih =>
    have hi : i < 8 := hindices i (List.mem_cons_self)
    obtain ⟨s₁, run₁, value₁, rd₁, wr₁, sp₁, keep₁, frame₁⟩ := box_ok i hi s hok hread hal
    have hregion : spillRegion s₁ = spillRegion s := by
      simp only [spillRegion, keep₁ sb (by decide)]
    have hr₁ : s₁.gpr rReg = r := (keep₁ rReg (by decide)).trans hr
    have hk₁ : s₁.mem.readW (s₁.gpr kp) 64 = k := by
      rw [keep₁ kp (by decide)]
      refine Eq.trans (frame₁.readW (r := ⟨s.gpr kp, 8⟩) ?_ ?_ (by decide)) hk
      · simp [Region.Contains]
      · intro q hq
        obtain rfl := List.mem_singleton.mp hq
        exact hsep
    have hread₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr kp) 8 := by
      rw [rd₁, wr₁, keep₁ kp (by decide)]
      exact hread
    have hal₁ : (s₁.gpr kp).toNat % 8 = 0 := by rw [keep₁ kp (by decide)]; exact hal
    have hsep₁ : (⟨s₁.gpr kp, 8⟩ : Region).Disjoint (spillRegion s₁) := by
      rw [keep₁ kp (by decide), hregion]
      exact hsep
    have hok₁ : Ok sboxCfg s₁ := hok.congr
      (keep₁ sb (by decide)) (keep₁ sb (by decide)) rd₁ wr₁
    obtain ⟨s₂, run₂, value₂, rd₂, wr₂, sp₂, keep₂, frame₂⟩ := ih
      (fun j hj => hindices j (List.mem_cons_of_mem _ hj)) s₁ hok₁ hr₁ hk₁ hread₁ hal₁ hsep₁
    refine ⟨s₂, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_, ?_⟩
    · simp only [List.flatMap_cons, runBoxes_append, run₁, Option.bind_some, run₂]
    · rw [hr, hk] at value₁
      simpa only [List.foldl_cons, ← value₁] using value₂
    · exact fun q hq => (keep₂ q hq).trans (keep₁ q hq)
    · rw [hregion] at frame₂
      exact frame₁.trans frame₂

/-- The registers the half swap keeps. -/
def roundOuterKept : List Reg := [.ra, .s1, .s2, .s3, .s4, .a0, kp, cnt, kstep, passes]

theorem swapHalves_ok (s : State) :
    ∃ s', runBlock isa swapHalves s = some s' ∧
      s'.gpr lReg = s.gpr rReg ∧ s'.gpr rReg = s.gpr lReg ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ q ∈ roundOuterKept, s'.gpr q = s.gpr q) := by
  let s₁ := s.write .t0 (s.gpr lReg + BitVec.ofInt 64 0)
  let s₂ := s₁.write lReg (s₁.gpr rReg + BitVec.ofInt 64 0)
  let s₃ := s₂.write rReg (s₂.gpr .t0 + BitVec.ofInt 64 0)
  refine ⟨s₃, ?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · rw [swapHalves, movR, movR, movR, runBlock_cons, exec_addi (by decide), runStep_some,
      runBlock_cons, exec_addi (by decide), runStep_some, runBlock_cons, exec_addi (by decide),
      runStep_some, runBlock_nil]
  · simp only [s₃, s₂, s₁, gpr_write, lReg, rReg, reduceCtorEq, ite_true, ite_false,
      BitVec.ofInt_ofNat, BitVec.add_zero]
  · simp only [s₃, s₂, s₁, gpr_write, lReg, rReg, reduceCtorEq, ite_true, ite_false,
      BitVec.ofInt_ofNat, BitVec.add_zero]
  · intro q hq
    have hne : q ≠ .t0 ∧ q ≠ lReg ∧ q ≠ rReg := by revert hq; cases q <;> decide
    simp only [s₃, s₂, s₁, gpr_write, hne.1, hne.2.1, hne.2.2, ite_false]

/-- One full Feistel round, with all eight S-boxes and the half swap. -/
theorem roundBody_ok (s : State) (l r : BitVec 32) (k : BitVec 64)
    (hl : s.gpr lReg = l.setWidth 64) (hr : s.gpr rReg = r.setWidth 64)
    (hk : s.mem.readW (s.gpr kp) 64 = k) (hok : Ok sboxCfg s)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr kp) 8) (hal : (s.gpr kp).toNat % 8 = 0)
    (hsep : (⟨s.gpr kp, 8⟩ : Region).Disjoint (spillRegion s)) :
    ∃ s', runBlock isa roundBody s = some s' ∧
      s'.gpr lReg = r.setWidth 64 ∧
      s'.gpr rReg = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)).setWidth 64 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ roundOuterKept, s'.gpr q = s.gpr q) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, value, rd₁, wr₁, sp₁, keep₁, frame₁⟩ := boxes_ok (List.range 8)
    (fun i hi => List.mem_range.mp hi) (r.setWidth 64) k s hok hr hk hread hal hsep
  obtain ⟨s₂, run₂, left, right, rd₂, wr₂, sp₂, mem₂, keep₂⟩ := swapHalves_ok s₁
  refine ⟨s₂, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_, ?_⟩
  · simp only [roundBody, runBoxes_append, run₁, Option.bind_some, run₂]
  · exact left.trans ((keep₁ rReg (by decide)).trans hr)
  · rw [right, value, contributions_roundFunction, hl]
    have hwidth : (r.setWidth 64).setWidth 32 = r := by simp
    rw [hwidth]
    exact BitVec.setWidth_xor.symm
  · intro q hq
    have hq' : q ∈ roundKept := by revert hq; cases q <;> decide
    exact (keep₂ q hq).trans (keep₁ q hq')
  · rw [mem₂]
    exact frame₁

/-- The registers a round and the step to the next keep. -/
def roundStepKept : List Reg := [.ra, .s1, .s2, .s3, .s4, .a0, kstep, passes]

theorem countDown_rules : ∀ n < 17, 1 ≤ n →
    (BitVec.ofNat 64 n + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n - 1)) ∧
    ((BitVec.ofNat 64 n + BitVec.ofInt 64 (-1)) != 0) = decide (n ≠ 1) := by
  decide +kernel

theorem roundAdvance_ok (s : State) :
    ∃ s', runBlock isa roundAdvance s = some s' ∧
      s'.gpr kp = s.gpr kp + s.gpr kstep ∧
      s'.gpr cnt = s.gpr cnt + BitVec.ofInt 64 (-1) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ cnt → r ≠ kp → s'.gpr r = s.gpr r) := by
  let s₁ := s.write kp (s.gpr kp + s.gpr kstep)
  let s₂ := s₁.write cnt (s₁.gpr cnt + BitVec.ofInt 64 (-1))
  refine ⟨s₂, ?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · rw [roundAdvance, runBlock_cons, exec_add, runStep_some, runBlock_cons,
      exec_addi (by decide), runStep_some, runBlock_nil]
  · simp only [s₂, s₁, gpr_write, kp, cnt, kstep, reduceCtorEq, ite_true, ite_false]
  · simp only [s₂, s₁, gpr_write, kp, cnt, reduceCtorEq, ite_true, ite_false]
  · intro r h16 h17
    simp only [s₂, s₁, gpr_write, h16, h17, ite_false]

theorem roundStep_ok (s : State)
    (l r : BitVec 32) (k : BitVec 64) (n : Nat) (hn : 1 ≤ n) (hn' : n < 17)
    (hl : s.gpr lReg = l.setWidth 64) (hr : s.gpr rReg = r.setWidth 64)
    (hk : s.mem.readW (s.gpr kp) 64 = k) (hok : Ok sboxCfg s)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr kp) 8) (hal : (s.gpr kp).toNat % 8 = 0)
    (hsep : (⟨s.gpr kp, 8⟩ : Region).Disjoint (spillRegion s))
    (hcount : s.gpr cnt = BitVec.ofNat 64 n) :
    ∃ s', runBlock isa (roundBody ++ roundAdvance) s = some s' ∧
      s'.gpr lReg = r.setWidth 64 ∧
      s'.gpr rReg = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)).setWidth 64 ∧
      s'.gpr kp = s.gpr kp + s.gpr kstep ∧
      s'.gpr cnt = BitVec.ofNat 64 (n - 1) ∧
      isa.eval (.nonzero cnt) s' = some (decide (n ≠ 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ roundStepKept, s'.gpr q = s.gpr q) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, left₁, right₁, rd₁, wr₁, sp₁, keep₁, frame₁⟩ :=
    roundBody_ok s l r k hl hr hk hok hread hal hsep
  obtain ⟨s₂, run₂, ptr₂, count₂, rd₂, wr₂, sp₂, mem₂, keep₂⟩ := roundAdvance_ok s₁
  obtain ⟨hsub, hzero⟩ := countDown_rules n hn' hn
  have hcount₁ : s₁.gpr cnt = BitVec.ofNat 64 n := (keep₁ cnt (by decide)).trans hcount
  refine ⟨s₂, ?_, ?_, ?_, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_, ?_⟩
  · simp only [runBoxes_append, run₁, Option.bind_some, run₂]
  · exact (keep₂ lReg (by decide) (by decide)).trans left₁
  · exact (keep₂ rReg (by decide) (by decide)).trans right₁
  · rw [ptr₂, keep₁ kp (by decide), keep₁ kstep (by decide)]
  · rw [count₂, hcount₁, hsub]
  · change VG.RISCV64.eval (.nonzero cnt) s₂ = _
    simp only [VG.RISCV64.eval, count₂, hcount₁, hzero]
  · intro q hq
    have hq' : q ∈ roundOuterKept := by revert hq; cases q <;> decide
    have hneq : q ≠ cnt ∧ q ≠ kp := by revert hq; cases q <;> decide
    exact (keep₂ q hneq.1 hneq.2).trans (keep₁ q hq')
  · rw [mem₂]; exact frame₁

end VG.Proof.TripleDes.RISCV64
