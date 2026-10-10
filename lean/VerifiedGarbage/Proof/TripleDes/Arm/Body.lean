import VerifiedGarbage.Proof.TripleDes.Arm.Box
import VerifiedGarbage.Proof.TripleDes.Arm.RoundFunction
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Rc2.Arm.KeySteps
import VerifiedGarbage.Proof.TripleDes.Core
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.TripleDes.Word

/-! ## `RoundBody` -/

section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm

def contribution (r : BitVec 32) (k : BitVec 64) (i : Nat) : BitVec 32 :=
  (boxPiece i (Spec.TripleDes.sBox i
    (roundChunk i (r.setWidth 32) (k.setWidth 48)))).zeroExtend 32

/-- Compose any ordered list of S-boxes. The schedule word and Feistel
right half stay fixed; each contribution is XORed into the left half. -/
theorem boxes_ok (indices : List Nat) (hindices : ∀ i ∈ indices, i < 8)
    (r : BitVec 32) (k : BitVec 64) (s : State) (hok : Ok sboxCfg s)
    (hr : s.gpr .r11 = r) (hk : keyWord s = k)
    (hread : ∀ j < 2, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r0) j) 4)
    (hsep : ∀ j < 2, (⟨wordAddr (s.gpr .r0) j, 4⟩ : Region).Disjoint (spillRegion s)) :
    ∃ s', runBlock isa (indices.flatMap box) s = some s' ∧
      s'.gpr .r10 = indices.foldl (fun out i => out ^^^ contribution r k i) (s.gpr .r10) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ roundKept, s'.gpr q = s.gpr q) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  induction indices generalizing s with
  | nil =>
    exact ⟨s, runBlock_nil, rfl, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩
  | cons i indices ih =>
    have hi : i < 8 := hindices i (List.mem_cons_self)
    obtain ⟨s₁, run₁, value₁, rd₁, wr₁, sp₁, keep₁, frame₁⟩ := box_ok i hi s hok hread
    have hregion : spillRegion s₁ = spillRegion s := by
      simp only [spillRegion, keep₁ .r2 (by decide)]
    have hr₁ : s₁.gpr .r11 = r := (keep₁ .r11 (by decide)).trans hr
    have hword (j : Nat) (hj : j < 2) :
        s₁.mem.readW (wordAddr (s₁.gpr .r0) j) 32 = s.mem.readW (wordAddr (s.gpr .r0) j) 32 := by
      rw [keep₁ .r0 (by decide)]
      apply frame₁.readW (r := ⟨wordAddr (s.gpr .r0) j, 4⟩) (Region.contains_self _ _)
        (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hsep j hj) (by decide)
    have hk₁ : keyWord s₁ = k := by
      unfold keyWord
      rw [hword 0 (by decide), hword 1 (by decide)]
      exact hk
    have hread₁ : ∀ j < 2, InRegions (s₁.rd ++ s₁.wr) (wordAddr (s₁.gpr .r0) j) 4 := by
      rw [rd₁, wr₁, keep₁ .r0 (by decide)]
      exact hread
    have hsep₁ : ∀ j < 2, (⟨wordAddr (s₁.gpr .r0) j, 4⟩ : Region).Disjoint (spillRegion s₁) := by
      rw [keep₁ .r0 (by decide), hregion]
      exact hsep
    have hok₁ : Ok sboxCfg s₁ := hok.congr
      (keep₁ .r2 (by decide)) (keep₁ .r2 (by decide)) rd₁ wr₁
    obtain ⟨s₂, run₂, value₂, rd₂, wr₂, sp₂, keep₂, frame₂⟩ := ih
      (fun j hj => hindices j (List.mem_cons_of_mem _ hj)) s₁ hok₁ hr₁ hk₁ hread₁ hsep₁
    refine ⟨s₂, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_, ?_⟩
    · simp only [List.flatMap_cons, runBoxes_append, run₁, Option.bind_some, run₂]
    · rw [hr, hk] at value₁
      change s₁.gpr .r10 = s.gpr .r10 ^^^ contribution r k i at value₁
      simpa only [List.foldl_cons, ← value₁] using value₂
    · exact fun q hq => (keep₂ q hq).trans (keep₁ q hq)
    · rw [hregion] at frame₂
      exact frame₁.trans frame₂

theorem contributions_roundFunction (r : BitVec 32) (k : BitVec 64) (l : BitVec 32) :
    (List.range 8).foldl (fun out i => out ^^^ contribution r k i) l =
      l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48) := by
  rw [foldl_xor_start]
  exact congrArg (l ^^^ ·) (by
    simpa only [contribution, BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_eq] using
      boxPieces_eq_roundFunction r (k.setWidth 48))

def roundOuterKept : List Reg := [.r0, .r1, .r2, .r3, .r9]

theorem swapHalves_ok (s : State) :
    ∃ s', runBlock isa swapHalves s = some s' ∧
      s'.gpr .r10 = s.gpr .r11 ∧ s'.gpr .r11 = s.gpr .r10 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ q ∈ roundOuterKept, s'.gpr q = s.gpr q) := by
  open VG.Arm.RegUpd in
  refine ⟨_, by
    simp only [swapHalves, rr, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [rd_setReg]
  · simp only [wr_setReg]
  · simp only [sp_setReg]
  · simp only [mem_setReg]
  · intro q hq
    have hneq : q ≠ .lr ∧ q ≠ .r10 ∧ q ≠ .r11 := by revert hq; cases q <;> decide
    simp only [gpr_setReg, hneq.1, hneq.2.1, hneq.2.2, ite_false]

/-- One full Feistel round, with all eight S-boxes and the half swap. -/
theorem roundBody_ok (s : State) (l r : BitVec 32) (k : BitVec 64)
    (hl : s.gpr .r10 = l) (hr : s.gpr .r11 = r)
    (hk : keyWord s = k) (hok : Ok sboxCfg s)
    (hread : ∀ j < 2, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r0) j) 4)
    (hsep : ∀ j < 2, (⟨wordAddr (s.gpr .r0) j, 4⟩ : Region).Disjoint (spillRegion s)) :
    ∃ s', runBlock isa roundBody s = some s' ∧
      s'.gpr .r10 = r ∧
      s'.gpr .r11 = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ roundOuterKept, s'.gpr q = s.gpr q) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, value, rd₁, wr₁, sp₁, keep₁, frame₁⟩ := boxes_ok (List.range 8)
    (fun i hi => List.mem_range.mp hi) (r) k s hok hr hk hread hsep
  obtain ⟨s₂, run₂, left, right, rd₂, wr₂, sp₂, mem₂, keep₂⟩ := swapHalves_ok s₁
  refine ⟨s₂, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_, ?_⟩
  · simp only [roundBody, runBoxes_append, run₁, Option.bind_some, run₂]
  · exact left.trans ((keep₁ .r11 (by decide)).trans hr)
  · rw [right, value, contributions_roundFunction, hl]
  · intro q hq
    have hq' : q ∈ roundKept := by revert hq; cases q <;> decide
    exact (keep₂ q hq).trans (keep₁ q hq')
  · rw [mem₂]
    exact frame₁

end VG.Proof.TripleDes.Arm

end

/-! ## `RoundStep` -/

section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.Straight VG.Arm.RegUpd VG.Impl.TripleDes.Arm
open VG.Proof.Rc2.Arm (gpr_subFlags mem_subFlags)

def roundStepKept : List Reg := [.r1, .r2, .r3]

theorem countDown_rules : ∀ n < 17, 1 ≤ n →
    (BitVec.ofNat 32 n - 1 = BitVec.ofNat 32 (n - 1)) ∧
    (!(BitVec.ofNat 32 n - 1 == 0)) = decide (n ≠ 1) := by decide +kernel

theorem roundAdvance_ok (d : Spec.TripleDes.Direction) (s : State) :
    ∃ s', runBlock isa (roundAdvance d) s = some s' ∧
      s'.gpr .r0 = (if d = .encrypt then s.gpr .r0 + 8 else s.gpr .r0 - 8) ∧
      s'.gpr .r9 = s.gpr .r9 - 1 ∧
      s'.z = ((s.gpr .r9 - 1) == 0) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .r9 → r ≠ .r0 → s'.gpr r = s.gpr r) := by
  cases d <;> refine ⟨_, by
    simp only [roundAdvance, ite_true, reduceCtorEq, ite_false, runBlock_cons,
      exec, Op2.eval, encodable, reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false,
    z_setReg, subFlags, rd_setReg, wr_setReg, sp_setReg, mem_setReg]
  all_goals try rfl
  all_goals
    intro r hr₁ hr₂
    simp only [hr₁, hr₂, ite_false]

theorem roundStep_ok (d : Spec.TripleDes.Direction) (s : State)
    (l r : BitVec 32) (k : BitVec 64) (n : Nat) (hn : 1 ≤ n) (hn' : n < 17)
    (hl : s.gpr .r10 = l) (hr : s.gpr .r11 = r)
    (hk : keyWord s = k) (hok : Ok sboxCfg s)
    (hread : ∀ j < 2, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r0) j) 4)
    (hsep : ∀ j < 2, (⟨wordAddr (s.gpr .r0) j, 4⟩ : Region).Disjoint (spillRegion s))
    (hcount : s.gpr .r9 = BitVec.ofNat 32 n) :
    ∃ s', runBlock isa (roundBody ++ roundAdvance d) s = some s' ∧
      s'.gpr .r10 = r ∧
      s'.gpr .r11 = (l ^^^ Spec.TripleDes.roundFunction r (k.setWidth 48)) ∧
      s'.gpr .r0 = (if d = .encrypt then s.gpr .r0 + 8 else s.gpr .r0 - 8) ∧
      s'.gpr .r9 = BitVec.ofNat 32 (n - 1) ∧
      isa.eval .ne s' = some (decide (n ≠ 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ q ∈ roundStepKept, s'.gpr q = s.gpr q) ∧
      Frame [spillRegion s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, left₁, right₁, rd₁, wr₁, sp₁, keep₁, frame₁⟩ :=
    roundBody_ok s l r k hl hr hk hok hread hsep
  obtain ⟨s₂, run₂, ptr₂, count₂, z₂, rd₂, wr₂, sp₂, mem₂, keep₂⟩ := roundAdvance_ok d s₁
  obtain ⟨hsub, hzero⟩ := countDown_rules n hn' hn
  have hcount₁ : s₁.gpr .r9 = BitVec.ofNat 32 n := (keep₁ .r9 (by decide)).trans hcount
  refine ⟨s₂, ?_, ?_, ?_, ?_, ?_, ?_, rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, ?_, ?_⟩
  · simp only [runBoxes_append, run₁, Option.bind_some, run₂]
  · exact (keep₂ .r10 (by decide) (by decide)).trans left₁
  · exact (keep₂ .r11 (by decide) (by decide)).trans right₁
  · rw [ptr₂, keep₁ .r0 (by decide)]
  · rw [count₂, hcount₁, hsub]
  · change VG.Arm.eval .ne s₂ = _
    simp only [VG.Arm.eval, z₂, hcount₁, hzero]
  · intro q hq
    have hq' : q ∈ roundOuterKept := by revert hq; cases q <;> decide
    have hneq : q ≠ .r9 ∧ q ≠ .r0 := by revert hq; cases q <;> decide
    exact (keep₂ q hneq.1 hneq.2).trans (keep₁ q hq')
  · rw [mem₂]; exact frame₁

end VG.Proof.TripleDes.Arm

end

/-! ## `Loop` -/

section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm
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
    exact congrArg (fun n => base + BitVec.ofNat 32 n) (by omega)
  · change base + BitVec.ofNat 32 (8 * (15 - j)) - BitVec.ofNat 32 8 = base + BitVec.ofNat 32 (8 * (15 - (j + 1)))
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      Offset.ofNat_sub_ofNat (by omega)]
    exact congrArg (fun n => base + BitVec.ofNat 32 n) (by omega)

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
  left : s.gpr .r10 = (roundPrefix keys direction (16 - n) v).1
  right : s.gpr .r11 = (roundPrefix keys direction (16 - n) v).2
  counter : s.gpr .r9 = BitVec.ofNat 32 n
  pointer : s.gpr .r0 = keyAddr base direction (16 - n)
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem

structure LoopPost (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32) (s : State) : Prop where
  left : s.gpr .r10 = (roundPrefix keys direction 16 v).1
  right : s.gpr .r11 = (roundPrefix keys direction 16 v).2
  counter : s.gpr .r9 = 0
  pointer : s.gpr .r0 = endPointer base direction
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem

theorem loopStep (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (keyAddr base direction j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (keyAddr base direction j) t, 4⟩ : Region).Disjoint (spillRegion origin))
    (hkeys : ∀ j < 16, (readKey origin.mem (keyAddr base direction j)).setWidth 48 =
      roundKey keys direction j)
    (n : Nat) (s : State) (hs : LoopInv keys direction base origin v n s) :
    WP isa (.block (roundBody ++ roundAdvance direction)) s (fun s' =>
      (isa.eval .ne s' = some false ∧ LoopPost keys direction base origin v s') ∨
      (isa.eval .ne s' = some true ∧ ∃ m < n, LoopInv keys direction base origin v m s')) := by
  have hj : 16 - n < 16 := by omega_using [hs.positive]
  have hwork : spillRegion s = spillRegion origin := by
    simp only [spillRegion, hs.regs .r2 (by decide)]
  have hokS : Ok sboxCfg s := hok.congr
    (hs.regs .r2 (by decide)) (hs.regs .r2 (by decide)) hs.rd hs.wr
  have hreadS : ∀ t < 2, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .r0) t) 4 := by
    rw [hs.rd, hs.wr, hs.pointer]; exact hread _ hj
  have hsepS : ∀ t < 2, (⟨wordAddr (s.gpr .r0) t, 4⟩ : Region).Disjoint (spillRegion s) := by
    rw [hs.pointer, hwork]; exact hsep _ hj
  have hk : (keyWord s).setWidth 48 = roundKey keys direction (16 - n) := by
    change (readKey s.mem (s.gpr .r0)).setWidth 48 = _
    rw [hs.pointer]
    have hmem := readKey_frame hs.frame (ptr := keyAddr base direction (16 - n))
      (fun t ht q hq => by obtain rfl := List.mem_singleton.mp hq; exact hsep _ hj t ht)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hkeys _ hj)
  obtain ⟨s', run, left, right, ptr, count, flag, rd, wr, sp, regs, frame⟩ :=
    roundStep_ok direction s _ _ (keyWord s) n hs.positive
      (by omega_using [hs.bounded]) hs.left hs.right rfl hokS hreadS hsepS
      hs.counter
  have hidx : 16 - (n - 1) = 16 - n + 1 := by
    omega_using [hs.positive, hs.bounded]
  have hleft : s'.gpr .r10 = (roundPrefix keys direction (16 - (n - 1)) v).1 := by
    rw [hidx]
    exact left.trans (congrArg (fun pair => pair.1)
      (VG.Proof.TripleDes.roundPrefix_succ keys direction (16 - n) v).symm)
  have hright : s'.gpr .r11 = (roundPrefix keys direction (16 - (n - 1)) v).2 := by
    rw [hidx]
    have hval := congrArg (fun key =>
      ((roundPrefix keys direction (16 - n) v).1 ^^^
        Spec.TripleDes.roundFunction (roundPrefix keys direction (16 - n) v).2 key)) hk
    exact (right.trans hval).trans (congrArg (fun pair => pair.2)
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
      exact ⟨hleft, hright, count, by
        rw [ptr, hs.pointer]
        exact keyAddr_end base direction, rd.trans hs.rd, wr.trans hs.wr, sp.trans hs.sp, hregs, hframe⟩
  · right
    refine ⟨?_, n - 1, by omega_using [hs.positive], ?_⟩
    · simpa only [hlast, ne_eq, not_false_eq_true, decide_true] using flag
    · refine ⟨by omega_using [hs.positive, hlast], by omega_using [hs.bounded],
        hleft, hright, count, ?_, rd.trans hs.rd, wr.trans hs.wr, sp.trans hs.sp, hregs, hframe⟩
      rw [ptr, hs.pointer, keyAddr_step base direction (16 - n) (by
        omega_using [hs.positive, hlast]), ← hidx]

/-- The complete sixteen-round loop, in either key order. -/
theorem roundsLoop_ok (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hl : origin.gpr .r10 = v.1) (hr : origin.gpr .r11 = v.2)
    (hptr : origin.gpr .r0 = keyAddr base direction 0)
    (hcount : origin.gpr .r9 = BitVec.ofNat 32 16)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (keyAddr base direction j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (keyAddr base direction j) t, 4⟩ : Region).Disjoint (spillRegion origin))
    (hkeys : ∀ j < 16, (readKey origin.mem (keyAddr base direction j)).setWidth 48 =
      roundKey keys direction j) :
    WP isa (.loop (.block (roundBody ++ roundAdvance direction)) .ne)
      origin (LoopPost keys direction base origin v) := by
  apply WP.loop (M := isa) (body := .block (roundBody ++ roundAdvance direction))
    (c := .ne) (Q := LoopPost keys direction base origin v) (LoopInv keys direction base origin v)
    (loopStep keys direction base origin v hok hread hsep hkeys)
    16 origin
  exact ⟨by decide, by decide, hl, hr, hcount, hptr, rfl, rfl, rfl,
    fun _ _ => rfl, Frame.refl _ _⟩

end VG.Proof.TripleDes.Arm

end

/-! ## `PassStart` -/

section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm

def startPointer (ptr : BitVec 32) (offset : Int) : BitVec 32 :=
  if offset < 0 then ptr - BitVec.ofNat 32 offset.natAbs else ptr + BitVec.ofNat 32 offset.natAbs

theorem passOffset_encodable : ∀ offset ∈ ([0, 120, 136, 376, -120, -136] : List Int),
    encodable (BitVec.ofNat 32 offset.natAbs) = true := by decide +kernel

theorem passStart_ok (offset : Int) (s : State)
    (ho : encodable (BitVec.ofNat 32 offset.natAbs) = true) :
    ∃ s', runBlock isa (passStart offset) s = some s' ∧
      s'.gpr .r0 = startPointer (s.gpr .r0) offset ∧ s'.gpr .r9 = 16 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .r0 → r ≠ .r9 → s'.gpr r = s.gpr r) := by
  by_cases h : offset < 0
  all_goals refine ⟨(s.setReg .r0 (startPointer (s.gpr .r0) offset)).setReg .r9 16, by
    simp only [passStart, h, ite_true, ite_false, runBlock_cons, exec, Op2.eval, ho, ite_true,
      Option.map_some, imm, runStep_some, startPointer]
    rfl, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  all_goals try simp only [gpr_setReg, startPointer, h, ite_true, ite_false, reduceCtorEq]
  all_goals try rfl
  all_goals
    intro r hr₀ hr₉
    simp only [hr₀, hr₉, ite_false]
end VG.Proof.TripleDes.Arm

end

/-! ## `Pass` -/

section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey roundPrefix)

structure PassPost (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32) (s : State) : Prop where
  left : s.gpr .r10 = (roundPrefix keys direction 16 v).2
  right : s.gpr .r11 = (roundPrefix keys direction 16 v).1
  pointer : s.gpr .r0 = endPointer base direction
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem

/-- The sixteen-round loop and final DES half swap. -/
theorem roundsWithSwap_ok (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hl : origin.gpr .r10 = v.1) (hr : origin.gpr .r11 = v.2)
    (hptr : origin.gpr .r0 = keyAddr base direction 0)
    (hcount : origin.gpr .r9 = BitVec.ofNat 32 16)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (keyAddr base direction j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (keyAddr base direction j) t, 4⟩ : Region).Disjoint (spillRegion origin))
    (hkeys : ∀ j < 16, (readKey origin.mem (keyAddr base direction j)).setWidth 48 =
      roundKey keys direction j) :
    WP isa (.seq (.loop (.block (roundBody ++ roundAdvance direction)) .ne)
      (.block swapHalves)) origin (PassPost keys direction base origin v) := by
  apply WP.seq
  apply WP.mono (roundsLoop_ok keys direction base origin v hok hl hr hptr hcount
    hread hsep hkeys)
  intro s hs
  obtain ⟨s', run, left, right, rd, wr, sp, mem, regs⟩ := swapHalves_ok s
  apply WP.of_runBlock
  refine ⟨s', run, left.trans hs.right, right.trans hs.left, (regs .r0 (by decide)).trans hs.pointer,
    rd.trans hs.rd, wr.trans hs.wr, sp.trans hs.sp, ?_, ?_⟩
  · intro q hq
    have hkeep : ∀ r ∈ roundStepKept, r ∈ roundOuterKept := by decide
    exact (regs q (hkeep q hq)).trans (hs.regs q hq)
  · rw [mem]
    exact hs.frame


theorem pass_ok (offset : Int) (ho : encodable (BitVec.ofNat 32 offset.natAbs) = true)
    (keys : DesSchedule) (direction : Direction) (base : BitVec 32)
    (origin : State) (v : BitVec 32 × BitVec 32)
    (hok : Ok sboxCfg origin)
    (hl : origin.gpr .r10 = v.1) (hr : origin.gpr .r11 = v.2)
    (hptr : startPointer (origin.gpr .r0) offset =
      keyAddr base direction 0)
    (hread : ∀ j < 16, ∀ t < 2, InRegions (origin.rd ++ origin.wr) (wordAddr (keyAddr base direction j) t) 4)
    (hsep : ∀ j < 16, ∀ t < 2, (⟨wordAddr (keyAddr base direction j) t, 4⟩ : Region).Disjoint (spillRegion origin))
    (hkeys : ∀ j < 16, (readKey origin.mem (keyAddr base direction j)).setWidth 48 =
      roundKey keys direction j) :
    WP isa (pass offset direction) origin (PassPost keys direction base origin v) := by
  obtain ⟨s, run, ptr, count, mem, rd, wr, sp, regs⟩ := passStart_ok offset origin ho
  have hbase : s.gpr .r2 = origin.gpr .r2 := regs .r2 (by decide) (by decide)
  have hwork : spillRegion s = spillRegion origin := by simp only [spillRegion, hbase]
  have hkeysS : ∀ j < 16, (readKey s.mem (keyAddr base direction j)).setWidth 48 =
      roundKey keys direction j := by rw [mem]; exact hkeys
  have hreadS : ∀ j < 16, ∀ t < 2, InRegions (s.rd ++ s.wr) (wordAddr (keyAddr base direction j) t) 4 := by
    rw [rd, wr]; exact hread
  have hsepS : ∀ j < 16, ∀ t < 2, (⟨wordAddr (keyAddr base direction j) t, 4⟩ : Region).Disjoint (spillRegion s) := by
    rw [hwork]; exact hsep
  have htail := roundsWithSwap_ok keys direction base s v
    (hok.congr hbase hbase rd wr)
    ((regs .r10 (by decide) (by decide)).trans hl)
    ((regs .r11 (by decide) (by decide)).trans hr)
    (ptr.trans hptr) count hreadS hsepS hkeysS
  apply WP.seq
  apply WP.of_runBlock
  refine ⟨s, run, WP.mono htail ?_⟩
  intro s' hs
  refine ⟨hs.left, hs.right, hs.pointer, hs.rd.trans rd, hs.wr.trans wr, hs.sp.trans sp, ?_, ?_⟩
  · intro q hq
    have hneq : ∀ r ∈ roundStepKept, r ≠ .r9 ∧ r ≠ .r0 := by decide
    exact (hs.regs q hq).trans (regs q (hneq q hq).2 (hneq q hq).1)
  · have hf := hs.frame
    rw [hwork, mem] at hf
    exact hf

end VG.Proof.TripleDes.Arm

end

/-! ## `WordState` -/

section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Impl.TripleDes.Arm
open VG.Proof.TripleDes (desCore roundPrefix)

/-- A DES word held as two 32-bit Feistel registers. -/
structure WordState (x : BitVec 64) (s : State) : Prop where
  left : s.gpr .r10 = ((x >>> 32).setWidth 32)
  right : s.gpr .r11 = (x.setWidth 32)

theorem PassPost.wordState {keys : Spec.TripleDes.DesSchedule}
    {direction : Spec.TripleDes.Direction} {base : BitVec 32} {origin s : State} {x : BitVec 64}
    (hs : PassPost keys direction base origin ((x >>> 32).setWidth 32, x.setWidth 32) s) :
    WordState (desCore keys direction x) s := by
  have hcore := VG.Proof.TripleDes.desCore_roundPrefix keys direction x
  let halves := roundPrefix keys direction 16 ((x >>> 32).setWidth 32, x.setWidth 32)
  have hleft : ((desCore keys direction x >>> 32).setWidth 32) = halves.2 :=
    (congrArg (fun v : BitVec 64 => ((v >>> 32).setWidth 32)) hcore).trans
      (VG.Proof.TripleDes.appended_left halves.2 halves.1)
  have hright : ((desCore keys direction x).setWidth 32) = halves.1 :=
    (congrArg (fun v : BitVec 64 => (v.setWidth 32)) hcore).trans
      (VG.Proof.TripleDes.appended_right halves.2 halves.1)
  exact ⟨hs.left.trans hleft.symm, hs.right.trans hright.symm⟩

end VG.Proof.TripleDes.Arm

end

/-! ## `Ready` -/

section

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

def componentBase (base : BitVec 32) (component : Nat) : BitVec 32 :=
  base + BitVec.ofNat 32 (128 * component)

structure Ready (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) : Prop where
  spills : Ok sboxCfg s
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    InRegions (s.rd ++ s.wr) (wordAddr (keyAddr (componentBase base c) d j) t) 4
  separate : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    (⟨wordAddr (keyAddr (componentBase base c) d j) t, 4⟩ : Region).Disjoint (spillRegion s)
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (readKey s.mem (keyAddr (componentBase base c) d j)).setWidth 48 = roundKey (keys c) d j

theorem Ready.congr {keys : Nat → DesSchedule} {base : BitVec 32} {s t : State}
    (hs : Ready keys base s) (hbase : t.gpr .r2 = s.gpr .r2)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hf : Frame [spillRegion s] s.mem t.mem) : Ready keys base t := by
  have hwork : spillRegion t = spillRegion s :=
    congrArg (fun p => (⟨State.addr p + BitVec.ofNat 64 60, 388⟩ : Region)) hbase
  refine ⟨hs.spills.congr hbase hbase hrd hwr, ?_, ?_, ?_⟩
  · rw [hrd, hwr]; exact hs.read
  · rw [hwork]; exact hs.separate
  · intro c hc d j hj
    have hmem := readKey_frame hf (ptr := keyAddr (componentBase base c) d j)
      (fun t ht q hq => by obtain rfl := List.mem_singleton.mp hq; exact hs.separate c hc d j hj t ht)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hs.values c hc d j hj)

structure Stable (origin s : State) : Prop where
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [spillRegion origin] origin.mem s.mem

theorem Stable.refl (s : State) : Stable s s :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩

theorem Stable.trans {s t u : State} (hs : Stable s t) (ht : Stable t u) : Stable s u := by
  have hwork : spillRegion t = spillRegion s :=
    congrArg (fun p => (⟨State.addr p + BitVec.ofNat 64 60, 388⟩ : Region)) (hs.regs .r2 (by decide))
  have hf := ht.frame
  rw [hwork] at hf
  exact ⟨ht.rd.trans hs.rd, ht.wr.trans hs.wr, ht.sp.trans hs.sp,
    fun q hq => (ht.regs q hq).trans (hs.regs q hq), hs.frame.trans hf⟩

theorem pass_word_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) (x : BitVec 64)
    (c : Nat) (hc : c < 3) (d : Direction) (offset : Int)
    (ho : encodable (BitVec.ofNat 32 offset.natAbs) = true)
    (hptr : startPointer (s.gpr .r0) offset = keyAddr (componentBase base c) d 0)
    (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (pass offset d) s (fun t => WordState (VG.Proof.TripleDes.desCore (keys c) d x) t ∧
      Ready keys base t ∧ Stable s t ∧ t.gpr .r0 = endPointer (componentBase base c) d) := by
  apply WP.mono (pass_ok offset ho (keys c) d (componentBase base c) s
    ((x >>> 32).setWidth 32, x.setWidth 32) hready.spills hword.left hword.right
    hptr (hready.read c hc d) (hready.separate c hc d) (hready.values c hc d))
  intro t ht
  exact ⟨ht.wordState, hready.congr (ht.regs .r2 (by decide)) ht.rd ht.wr ht.frame,
    ⟨ht.rd, ht.wr, ht.sp, ht.regs, ht.frame⟩, ht.pointer⟩

end VG.Proof.TripleDes.Arm

end

/-! ## `Body` -/

section

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (desCore)

theorem threePasses_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) (x : BitVec 64)
    (c₀ c₁ c₂ : Nat) (h₀ : c₀ < 3) (h₁ : c₁ < 3) (h₂ : c₂ < 3)
    (d₀ d₁ d₂ : Direction) (o₀ o₁ o₂ : Int)
    (e₀ : encodable (BitVec.ofNat 32 o₀.natAbs) = true)
    (e₁ : encodable (BitVec.ofNat 32 o₁.natAbs) = true)
    (e₂ : encodable (BitVec.ofNat 32 o₂.natAbs) = true)
    (p₀ : startPointer (s.gpr .r0) o₀ = keyAddr (componentBase base c₀) d₀ 0)
    (p₁ : startPointer (endPointer (componentBase base c₀) d₀) o₁ = keyAddr (componentBase base c₁) d₁ 0)
    (p₂ : startPointer (endPointer (componentBase base c₁) d₁) o₂ = keyAddr (componentBase base c₂) d₂ 0)
    (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (.seq (pass o₀ d₀) (.seq (pass o₁ d₁) (pass o₂ d₂))) s
      (fun t => WordState (desCore (keys c₂) d₂ (desCore (keys c₁) d₁ (desCore (keys c₀) d₀ x))) t ∧
        Ready keys base t ∧ Stable s t ∧ t.gpr .r0 = endPointer (componentBase base c₂) d₂) := by
  apply WP.seq
  apply WP.mono (pass_word_ok keys base s x c₀ h₀ d₀ o₀ e₀ p₀ hready hword)
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (pass_word_ok keys base s₁ _ c₁ h₁ d₁ o₁ e₁
    (by rw [hs₁.2.2.2]; exact p₁) hs₁.2.1 hs₁.1)
  intro s₂ hs₂
  apply WP.mono (pass_word_ok keys base s₂ _ c₂ h₂ d₂ o₂ e₂
    (by rw [hs₂.2.2.2]; exact p₂) hs₂.2.1 hs₂.1)
  intro s₃ hs₃
  exact ⟨hs₃.1, hs₃.2.1,
    hs₁.2.2.1.trans (hs₂.2.2.1.trans hs₃.2.2.1), hs₃.2.2.2⟩

theorem passPointers (base : BitVec 32) :
    startPointer base 0 = keyAddr (componentBase base 0) .encrypt 0 ∧
    startPointer (endPointer (componentBase base 0) .encrypt) 120 = keyAddr (componentBase base 1) .decrypt 0 ∧
    startPointer (endPointer (componentBase base 1) .decrypt) 136 = keyAddr (componentBase base 2) .encrypt 0 ∧
    startPointer base 376 = keyAddr (componentBase base 2) .decrypt 0 ∧
    startPointer (endPointer (componentBase base 2) .decrypt) (-120) = keyAddr (componentBase base 1) .encrypt 0 ∧
    startPointer (endPointer (componentBase base 1) .encrypt) (-136) = keyAddr (componentBase base 0) .decrypt 0 := by
  simp only [startPointer, endPointer, componentBase, keyAddr,
    Int.reduceLT, Int.natAbs_neg, ite_true, ite_false, reduceCtorEq,
    Nat.reduceMul, Nat.reduceSub]
  repeat' constructor <;> bv_omega

def blockCore (keys : Nat → DesSchedule) (direction : Direction) (x : BitVec 64) : BitVec 64 :=
  match direction with
  | .encrypt => desCore (keys 2) .encrypt (desCore (keys 1) .decrypt (desCore (keys 0) .encrypt x))
  | .decrypt => desCore (keys 0) .decrypt (desCore (keys 1) .encrypt (desCore (keys 2) .decrypt x))

theorem blockBody_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) (x : BitVec 64)
    (direction : Direction) (hptr : s.gpr .r0 = base)
    (hready : Ready keys base s) (hword : WordState x s) :
    WP isa (blockBody direction) s
      (fun t => WordState (blockCore keys direction x) t ∧ Ready keys base t ∧ Stable s t ∧
        t.gpr .r0 = (if direction = .encrypt then base + 384 else base - 8)) := by
  obtain ⟨p₀, p₁, p₂, p₃, p₄, p₅⟩ := passPointers base
  cases direction
  · apply WP.mono (threePasses_ok keys base s x 0 1 2 (by decide) (by decide) (by decide)
      .encrypt .decrypt .encrypt 0 120 136 (by decide) (by decide) (by decide)
      (by rw [hptr]; exact p₀) p₁ p₂ hready hword)
    intro t ht
    refine ⟨ht.1, ht.2.1, ht.2.2.1, ?_⟩
    rw [ht.2.2.2]
    change base + BitVec.ofNat 32 256 + BitVec.ofNat 32 128 = base + BitVec.ofNat 32 384
    rw [Offset.add_ofNat_add_ofNat]
  · apply WP.mono (threePasses_ok keys base s x 2 1 0 (by decide) (by decide) (by decide)
      .decrypt .encrypt .decrypt 376 (-120) (-136) (by decide) (by decide) (by decide)
      (by rw [hptr]; exact p₃) p₄ p₅ hready hword)
    intro t ht
    refine ⟨ht.1, ht.2.1, ht.2.2.1, ?_⟩
    rw [ht.2.2.2]
    change (base + 0) - 8 = base - 8
    exact congrArg (· - (8 : BitVec 32)) (BitVec.add_zero base)
end VG.Proof.TripleDes.Arm

end
