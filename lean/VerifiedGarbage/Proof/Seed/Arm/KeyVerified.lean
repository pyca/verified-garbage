module

public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Seed.Scratch
import VerifiedGarbage.Proof.Framework.Arm.RegScratchWipe
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Seed.Arm.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.StackScratch.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Seed.Scratch
meta import VerifiedGarbage.Proof.Framework.Arm.RegScratchWipe
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Seed.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
import VerifiedGarbage.Proof.Seed.KeyRot
public import VerifiedGarbage.Impl.Seed.Arm.ExpandKey
public import VerifiedGarbage.Proof.Seed.KeySchedule
public import VerifiedGarbage.Proof.Seed.Arm.Group
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Seed.Memory
meta import VerifiedGarbage.Proof.Seed.KeyRot
meta import VerifiedGarbage.Impl.Seed.Arm.ExpandKey
meta import VerifiedGarbage.Proof.Seed.KeySchedule
meta import VerifiedGarbage.Proof.Seed.Arm.Group
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Seed.Memory

/-! ### `Seed.Arm.Key`, which only this module used -/

section

/-! ### `Seed.Arm.KeyRound`, which only this module used -/

section

/-!
# A round of the key schedule on ARMv7

`keyRound_ok`: `keyRound j` writes round `j + 1`'s two inputs of `G`
(`gInput`), from `Key0 … Key3` in `r4`–`r7`, to their slots, and rotates
`Key0 || Key1` or `Key2 || Key3` as one 64-bit word (`rotr8_hi`, …: a
rotation of `a || b` by eight bits is two shifts of each word); `keyRounds_ok`
runs the sixteen.
-/

@[expose] public section

namespace VG.Proof.Seed.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Seed.Arm VG.Proof.Seed
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp movR ldS stS lsrOp imm32)
open VG.Arm.Straight (wordAddr)

/-! ## Instructions -/

theorem exec_subR (s : State) (d n m : Reg) :
    exec (subR d n m) s = some (s.setReg d (s.gpr n - s.gpr m)) := rfl

theorem exec_movR (s : State) (d n : Reg) : exec (movR d n) s = some (s.setReg d (s.gpr n)) := rfl

theorem exec_mov_lsr (s : State) (d r : Reg) {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 31) :
    exec (.mov d (lsrOp r n)) s = some (s.setReg d (s.gpr r >>> n)) := by
  simp [exec, Op2.eval, lsrOp, h1, h2]

theorem exec_mov_lsl (s : State) (d r : Reg) {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 31) :
    exec (.mov d (lslOp r n)) s = some (s.setReg d (s.gpr r <<< n)) := by
  simp [exec, Op2.eval, lslOp, h1, h2]

theorem exec_orr_lsr (s : State) (d m r : Reg) {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 31) :
    exec (.dp .orr d m (lsrOp r n)) s = some (s.setReg d (s.gpr m ||| s.gpr r >>> n)) := by
  simp [exec, Op2.eval, lsrOp, h1, h2]

theorem exec_orr_lsl (s : State) (d m r : Reg) {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 31) :
    exec (.dp .orr d m (lslOp r n)) s = some (s.setReg d (s.gpr m ||| s.gpr r <<< n)) := by
  simp [exec, Op2.eval, lslOp, h1, h2]

/-! ## The rotations -/

/-- The key words in `r4`–`r7`. -/
def kw (s : State) : Quad := (s.gpr .r4, s.gpr .r5, s.gpr .r6, s.gpr .r7)

/-- The registers a round of the key schedule writes. -/
def keyRegs : List Reg := [t0, t1, .r4, .r5, .r6, .r7]

theorem rotr8_ok (s : State) :
    ∃ s', runBlock isa (rotr8 .r4 .r5) s = some s' ∧
      kw s' = keyStep 0 (kw s) ∧ (∀ r ∉ keyRegs, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  rw [rotr8, runBlock_cons, exec_mov_lsr _ _ _ (by decide) (by decide), runStep_some, runBlock_cons,
    exec_orr_lsl _ _ _ _ (by decide) (by decide), runStep_some, runBlock_cons,
    exec_mov_lsr _ _ _ (by decide) (by decide), runStep_some, runBlock_cons,
    exec_orr_lsl _ _ _ _ (by decide) (by decide), runStep_some, runBlock_cons, exec_movR, runStep_some,
    runBlock_nil]
  refine ⟨_, rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [kw, keyStep, Nat.zero_mod, gpr_setReg, t0, t1, reduceCtorEq, ↓reduceIte,
      rotr8_hi, rotr8_lo]
  · simp only [keyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, ↓reduceIte]

theorem rotl8_ok (s : State) :
    ∃ s', runBlock isa (rotl8 .r6 .r7) s = some s' ∧
      kw s' = keyStep 1 (kw s) ∧ (∀ r ∉ keyRegs, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  rw [rotl8, runBlock_cons, exec_mov_lsl _ _ _ (by decide) (by decide), runStep_some, runBlock_cons,
    exec_orr_lsr _ _ _ _ (by decide) (by decide), runStep_some, runBlock_cons,
    exec_mov_lsl _ _ _ (by decide) (by decide), runStep_some, runBlock_cons,
    exec_orr_lsr _ _ _ _ (by decide) (by decide), runStep_some, runBlock_cons, exec_movR, runStep_some,
    runBlock_nil]
  refine ⟨_, rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [kw, keyStep, show 1 % 2 = 1 from rfl, gpr_setReg, t0, t1, reduceCtorEq, ↓reduceIte,
      rotl8_hi, rotl8_lo]
  · simp only [keyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ↓reduceIte]

/-! ## A round -/

/-- A round's inputs of `G`, before the rotation. -/
def keyIn (j : Nat) : List Instr :=
  [addR t0 .r4 .r6] ++ imm32 t1 (Spec.Seed.kc.getD j 0) ++
  [subR t0 t0 t1, stS (uSlot (2 * j)) t0, subR t0 .r5 .r7, addR t0 t0 t1, stS (uSlot (2 * j + 1)) t0]

theorem keyRound_eq (j : Nat) :
    keyRound j = keyIn j ++ (if j % 2 = 0 then rotr8 .r4 .r5 else rotl8 .r6 .r7) := by
  simp only [keyRound, keyIn, List.append_assoc]

theorem uSlot_lt {i : Nat} (hi : i < 32) : uSlot i < slots := by simp [uSlot, aSlot, slots_eq]; omega_arith

theorem keyIn_ok {j : Nat} (hj : j < 16) {s : State} (h : Room s) :
    ∃ s', runBlock isa (keyIn j) s = some s' ∧
      slotW s' (uSlot (2 * j)) = s.gpr .r4 + s.gpr .r6 - Spec.Seed.kc.getD j 0 ∧
      slotW s' (uSlot (2 * j + 1)) = s.gpr .r5 - s.gpr .r7 + Spec.Seed.kc.getD j 0 ∧
      (∀ k < slots, k ≠ uSlot (2 * j) → k ≠ uSlot (2 * j + 1) → slotW s' k = slotW s k) ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [workR s] s.mem s'.mem := by
  obtain hu0 := uSlot_lt (i := 2 * j) (by omega_arith)
  obtain hu1 := uSlot_lt (i := 2 * j + 1) (by omega_arith)
  obtain hR : ∀ {t : State} (r : Reg) (v : BitVec 32), Room t → r ≠ sb → Room (t.setReg r v) :=
    fun r v ht hr => room_setReg ht hr v
  rw [show keyIn j = [addR t0 .r4 .r6, .movw t1 ((Spec.Seed.kc.getD j 0).extractLsb' 0 16),
      .movt t1 ((Spec.Seed.kc.getD j 0).extractLsb' 16 16), subR t0 t0 t1, stS (uSlot (2 * j)) t0,
      subR t0 .r5 .r7, addR t0 t0 t1, stS (uSlot (2 * j + 1)) t0] from rfl,
    runBlock_cons, exec_addR, runStep_some, runBlock_cons,
    show ∀ t : State, exec (.movw t1 ((Spec.Seed.kc.getD j 0).extractLsb' 0 16)) t =
      some (t.setReg t1 (((Spec.Seed.kc.getD j 0).extractLsb' 0 16).setWidth 32)) from fun _ => rfl,
    runStep_some, runBlock_cons,
    show ∀ t : State, exec (.movt t1 ((Spec.Seed.kc.getD j 0).extractLsb' 16 16)) t =
      some (t.setReg t1 ((Spec.Seed.kc.getD j 0).extractLsb' 16 16 ++ (t.gpr t1).extractLsb' 0 16)) from
      fun _ => rfl,
    runStep_some, runBlock_cons, exec_subR, runStep_some, runBlock_cons,
    exec_stS (hR _ _ (hR _ _ (hR _ _ (hR _ _ h (by decide)) (by decide)) (by decide)) (by decide)) hu0,
    runStep_some, runBlock_cons, exec_subR, runStep_some, runBlock_cons, exec_addR, runStep_some,
    runBlock_cons, exec_stS (hR _ _ (hR _ _ (room_setMem (hR _ _ (hR _ _ (hR _ _ (hR _ _ h (by decide))
      (by decide)) (by decide)) (by decide)) _) (by decide)) (by decide)) hu1,
    runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, ?_, fun k hk1 hk2 hk3 => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, ?_⟩
  · simp (disch := decide) only [slotW_setMem, slotA_setReg, slotA_setMem, gpr_setReg_self, mem_setMem,
      mem_setReg, movw_movt]
    rw [Mem.readW_writeW_sep (Straight.slot_sep _ (by have := h.fit; rw [slots_eq] at hu0 hu1 this; omega_arith)
      (by have := h.fit; rw [slots_eq] at hu0 hu1 this; omega_arith) (by simp [uSlot])) (by decide),
      Mem.readW_writeW_self32]
    simp only [gpr_setReg, t0, t1, reduceCtorEq, ↓reduceIte]
  · simp (disch := decide) only [slotW_setMem, slotA_setReg, slotA_setMem, gpr_setReg_self, mem_setMem,
      mem_setReg, Mem.readW_writeW_self32, movw_movt]
    simp only [gpr_setReg, gpr_setMem, t0, t1, reduceCtorEq, ↓reduceIte]
  · simp (disch := decide) only [slotW_setMem, slotA_setReg, slotA_setMem, mem_setMem, mem_setReg]
    obtain hf := h.fit; rw [slots_eq] at hk1 hu0 hu1 hf
    rw [Mem.readW_writeW_sep (Straight.slot_sep _ (by omega_arith) (by omega_arith) hk3) (by decide),
      Mem.readW_writeW_sep (Straight.slot_sep _ (by omega_arith) (by omega_arith) hk2) (by decide)]
    rfl
  · simp only [gpr_setMem, gpr_setReg_of_ne _ _ h1, gpr_setReg_of_ne _ _ h2]
  · simp (disch := decide) only [mem_setMem, mem_setReg, slotA_setReg, slotA_setMem]
    obtain hf := h.fit; rw [slots_eq] at hu0 hu1 hf
    obtain hw : ∀ i < 32, (workR s).Contains (slotA s (uSlot i)) 4 := fun i hi => by
      rw [slotA, slot_addr (by simp [uSlot, aSlot]; omega_arith)]
      exact Offset.contains_base _ (by simp [uSlot, aSlot, tailSlot]; omega_arith) (by simp [uSlot, aSlot]; omega_arith)
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ (hw _ (by omega_arith))).writeW List.mem_cons_self _
      (hw _ (by omega_arith))

theorem keyRound_ok {j : Nat} (hj : j < 16) {s : State} (h : Room s) :
    ∃ s', runBlock isa (keyRound j) s = some s' ∧ kw s' = keyStep j (kw s) ∧
      slotW s' (uSlot (2 * j)) = (kw s).1 + (kw s).2.2.1 - Spec.Seed.kc.getD j 0 ∧
      slotW s' (uSlot (2 * j + 1)) = (kw s).2.1 - (kw s).2.2.2 + Spec.Seed.kc.getD j 0 ∧
      (∀ k < slots, k ≠ uSlot (2 * j) → k ≠ uSlot (2 * j + 1) → slotW s' k = slotW s k) ∧
      (∀ r ∉ keyRegs, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [workR s] s.mem s'.mem := by
  obtain ⟨s₁, e₁, a₁, b₁, o₁, g₁, rd₁, wr₁, sp₁, f₁⟩ := keyIn_ok hj h
  obtain k₁ : kw s₁ = kw s := by
    simp only [kw, g₁ .r4 (by decide) (by decide), g₁ .r5 (by decide) (by decide), g₁ .r6 (by decide) (by decide),
      g₁ .r7 (by decide) (by decide)]
  obtain rot : ∃ s₂, runBlock isa (if j % 2 = 0 then rotr8 .r4 .r5 else rotl8 .r6 .r7) s₁ = some s₂ ∧
      kw s₂ = keyStep j (kw s₁) ∧ (∀ r ∉ keyRegs, s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧ s₂.sp = s₁.sp := by
    by_cases he : j % 2 = 0
    · rw [ite_eq_left he]
      obtain ⟨s₂, e₂, k₂, rest⟩ := rotr8_ok s₁
      exact ⟨s₂, e₂, by rw [k₂]; simp only [keyStep, he, Nat.zero_mod, ite_true], rest⟩
    · rw [ite_eq_right he]
      obtain ⟨s₂, e₂, k₂, rest⟩ := rotl8_ok s₁
      exact ⟨s₂, e₂, by rw [k₂]; simp only [keyStep, he, show 1 % 2 = 1 from rfl]; rfl, rest⟩
  obtain ⟨s₂, e₂, k₂, g₂, m₂, rd₂, wr₂, sp₂⟩ := rot
  obtain sb₂ : s₂.gpr sb = s.gpr sb := by rw [g₂ _ (by decide), g₁ _ (by decide) (by decide)]
  obtain sl₂ : ∀ k, slotW s₂ k = slotW s₁ k := fun k => by
    simp only [slotW, m₂, g₂ sb (by decide)]
  refine ⟨s₂, by rw [keyRound_eq, runBlock_append, e₁, Option.bind_some, e₂], by rw [k₂, k₁],
    by rw [sl₂, a₁]; rfl, by rw [sl₂, b₁]; rfl, fun k h1 h2 h3 => by rw [sl₂, o₁ k h1 h2 h3],
    fun r hr => ?_, by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁], by rw [m₂]; exact f₁⟩
  have : r ≠ t0 ∧ r ≠ t1 := by
    simp only [keyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact ⟨hr.1, hr.2.1⟩
  rw [g₂ r hr, g₁ r this.1 this.2]

/-- The inputs of `G` from round `j + 1`'s key words. -/
theorem gInput_even (key : Spec.Seed.Block) (j : Nat) :
    gInput key (2 * j) = (keyWords key j).1 + (keyWords key j).2.2.1 - Spec.Seed.kc.getD j 0 := by
  simp only [gInput, show 2 * j / 2 = j by omega_arith, show 2 * j % 2 = 0 by omega_arith, ite_true]

theorem gInput_odd (key : Spec.Seed.Block) (j : Nat) :
    gInput key (2 * j + 1) = (keyWords key j).2.1 - (keyWords key j).2.2.2 + Spec.Seed.kc.getD j 0 := by
  simp only [gInput, show (2 * j + 1) / 2 = j by omega_arith, show (2 * j + 1) % 2 = 1 by omega_arith]; rfl

/-- The first `n` rounds of the key schedule. -/
theorem keyRounds_ok (key : Spec.Seed.Block) {s : State} (h : Room s) (hk : kw s = keyWords key 0) :
    ∀ n ≤ 16, ∃ s', runBlock isa ((List.range n).flatMap keyRound) s = some s' ∧ Room s' ∧
      kw s' = keyWords key n ∧ (∀ i < 2 * n, slotW s' (uSlot i) = gInput key i) ∧
      (∀ k < slots, (k < uSlot 0 ∨ uSlot (2 * n) ≤ k) → slotW s' k = slotW s k) ∧
      (∀ r ∉ keyRegs, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [workR s] s.mem s'.mem := by
  intro n hn
  induction n with
  | zero => exact ⟨s, runBlock_nil, h, hk, fun i hi => by omega_arith, fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl,
      Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, e₁, h₁, k₁, v₁, o₁, g₁, rd₁, wr₁, sp₁, f₁⟩ := ih (by omega_arith)
    obtain ⟨s₂, e₂, k₂, a₂, b₂, o₂, g₂, rd₂, wr₂, sp₂, f₂⟩ := keyRound_ok (j := n) (by omega_arith) h₁
    obtain sb₁ : s₁.gpr sb = s.gpr sb := g₁ _ (by decide)
    obtain sb₂ : s₂.gpr sb = s.gpr sb := by rw [g₂ _ (by decide), sb₁]
    refine ⟨s₂, ?_, h.congr sb₂ (by rw [wr₂, wr₁]), by rw [k₂, k₁]; rfl, fun i hi => ?_, fun k hk1 hk2 => ?_,
      fun r hr => by rw [g₂ r hr, g₁ r hr], by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁],
      f₁.trans (by simpa [workR, sb₁] using f₂)⟩
    · rw [List.range_succ, List.flatMap_append, runBlock_append, e₁, Option.bind_some, List.flatMap_singleton, e₂]
    · rcases (show i < 2 * n ∨ i = 2 * n ∨ i = 2 * n + 1 by omega_arith) with hi' | rfl | rfl
      · rw [o₂ _ (uSlot_lt (by omega_arith)) (by simp [uSlot]; omega_arith) (by simp [uSlot]; omega_arith), v₁ i hi']
      · rw [a₂, k₁, gInput_even]
      · rw [b₂, k₁, gInput_odd]
    · rw [o₂ k hk1 (by simp [uSlot] at hk2 ⊢; omega_arith) (by simp [uSlot] at hk2 ⊢; omega_arith),
        o₁ k hk1 (by simp [uSlot] at hk2 ⊢; omega_arith)]

end VG.Proof.Seed.Arm

end

end


/-!
# SEED key expansion on ARMv7: the whole function

`expandKey_wp`: with the working space as an argument (`expandKeyArm`),
`expandKey` saves the callee-saved registers and the schedule's pointer,
loads the key's words (`keyLoad_ok`), computes the 32 inputs of `G`
(`keyRounds_ok`), and `G` of eight at a time to the schedule
(`keyChunk_ok`); RFC 4269 §2.3's schedule is `G` of these inputs
(`expandKey_eq`).
-/

@[expose] public section

namespace VG.Proof.Seed

open VG VG.Arm VG.Impl.Seed.Arm

/-- Key expansion on ARMv7 with its working space at `r2`. -/
def expandKeyArm : Contract Arm.isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 16⟩
    let sched : Region := ⟨State.addr (s.gpr .r1), 128⟩
    let scratch : Region := ⟨State.addr (s.gpr .r2), 4 * slots⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧ key.Disjoint sched ∧ key.Disjoint scratch ∧
      sched.Disjoint scratch ∧
      (s.gpr .r0).toNat + 16 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 128 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 4 * slots ≤ 2 ^ 32
  post s s' :=
    Spec.Seed.scheduleAt s'.mem (State.addr (s.gpr .r1)) =
      Spec.Seed.expandKey (Spec.Seed.blockAt s.mem (State.addr (s.gpr .r0)))
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.sp = s₂.sp

end VG.Proof.Seed

namespace VG.Proof.Seed.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Seed.Arm VG.Proof.Seed
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp movR ldS stS)
open VG.Arm.Straight (wordAddr add_ofNat_ofNat in_off)

/-! ## Copies between slots -/

/-- `ldr t0, [sb, #4 a]; str t0, [sb, #4 d]` for each `(a, d)`. -/
def copiesCode (L : List (Nat × Nat)) : List Instr := L.flatMap fun p => [ldS t0 p.1, stS p.2 t0]

theorem copies_ok {s : State} (h : Room s) {n : Nat} (hn : n ≤ slots) :
    ∀ (L : List (Nat × Nat)), (∀ p ∈ L, p.1 < slots ∧ p.2 < n) → (∀ p ∈ L, ∀ q ∈ L, p.1 ≠ q.2) →
      (L.map (·.2)).Nodup →
      ∃ s', runBlock isa (copiesCode L) s = some s' ∧
        (∀ p ∈ L, slotW s' p.2 = slotW s p.1) ∧
        (∀ j < slots, j ∉ L.map (·.2) → slotW s' j = slotW s j) ∧
        (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        Frame [⟨State.addr (s.gpr sb), 4 * n⟩] s.mem s'.mem
  | [], _, _, _ => ⟨s, runBlock_nil, fun _ h => absurd h List.not_mem_nil, fun _ _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | p :: L, hL, hd, hnd => by
    obtain hp := hL p List.mem_cons_self
    obtain hpd : p.2 < slots := by omega_arith
    let s₁ := setMem (s.setReg t0 (slotW s p.1)) (s.mem.writeW (slotA s p.2) (slotW s p.1))
    obtain e₁ : runBlock isa [ldS t0 p.1, stS p.2 t0] s = some s₁ := by
      rw [runBlock_cons, exec_ldS h hp.1, runStep_some, runBlock_cons,
        exec_stS (room_setReg h (by decide) _) hpd, runStep_some, runBlock_nil]
      simp only [s₁, slotA_setReg _ (show t0 ≠ sb by decide), gpr_setReg_self, mem_setReg]
    obtain h₁ : Room s₁ := room_setMem (room_setReg h (by decide) _) _
    obtain sb₁ : s₁.gpr sb = s.gpr sb := by
      simp only [s₁, gpr_setMem, gpr_setReg_of_ne _ _ (show sb ≠ t0 by decide)]
    obtain sl₁ : ∀ j < slots, slotW s₁ j = if j = p.2 then slotW s p.1 else slotW s j := by
      intro j hj
      rw [show s₁ = setMem _ _ from rfl, slotW_setMem, slotA_setReg _ (by decide)]
      exact slotW_setMem_write h hpd hj _
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', v', o', g', rd', wr', sp', f'⟩ := copies_ok h₁ hn L (fun q hq => hL q (List.mem_cons_of_mem _ hq))
      (fun q hq q' hq' => hd q (List.mem_cons_of_mem _ hq) q' (List.mem_cons_of_mem _ hq')) hnd.2
    have hfit := h.fit
    refine ⟨s', ?_, fun q hq => ?_, fun j hj hjL => ?_, fun r hr => ?_, by rw [rd']; rfl, by rw [wr']; rfl,
      by rw [sp']; rfl, ?_⟩
    · rw [copiesCode, List.flatMap_cons, runBlock_append, e₁, Option.bind_some]; exact e'
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [o' _ (by have := (hL q List.mem_cons_self).2; omega_arith) hnd.1, sl₁ _ hpd, ite_eq_left rfl]
      · rw [v' q hq, sl₁ _ (hL q (List.mem_cons_of_mem _ hq)).1,
          ite_eq_right (hd q (List.mem_cons_of_mem _ hq) p List.mem_cons_self)]
    · simp only [List.map_cons, List.mem_cons, not_or] at hjL
      rw [o' j hj hjL.2, sl₁ j hj, ite_eq_right hjL.1]
    · rw [g' r hr]
      simp only [s₁, gpr_setMem, gpr_setReg_of_ne _ _ hr]
    · refine Frame.trans ?_ (by rw [sb₁] at f'; exact f')
      show Frame _ s.mem (s.mem.writeW (slotA s p.2) (slotW s p.1))
      refine (Frame.refl _ _).writeW List.mem_cons_self _ ?_
      rw [slots_eq] at hfit hn
      exact Straight.slot_contains _ hp.2 (by omega_arith)

/-! ## Stores to the schedule -/

/-- `ldr t0, [sb, #4 a]; str t0, [kp, #4 o]` for each `(a, o)`. -/
def storesCode (L : List (Nat × Nat)) : List Instr := L.flatMap fun p => [ldS t0 p.1, .str t0 kp (4 * p.2)]

/-- The schedule at `P` (in `kp`), writable and apart from the scratch buffer. -/
structure OutPre (s : State) (P : BitVec 32) : Prop where
  room : Room s
  kp : s.gpr kp = P
  mem : (⟨State.addr P, 128⟩ : Region) ∈ s.wr
  fit : P.toNat + 128 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨State.addr P, 128⟩ (scratchR s)

theorem stores_ok {P : BitVec 32} :
    ∀ (L : List (Nat × Nat)) (s : State), OutPre s P → (∀ p ∈ L, p.1 < slots ∧ p.2 < 32) →
      (L.map (·.2)).Nodup →
      ∃ s', runBlock isa (storesCode L) s = some s' ∧
        (∀ p ∈ L, s'.mem.readW (State.addr P + BitVec.ofNat 64 (4 * p.2)) 32 = slotW s p.1) ∧
        (∀ o < 32, o ∉ L.map (·.2) → s'.mem.readW (State.addr P + BitVec.ofNat 64 (4 * o)) 32 =
          s.mem.readW (State.addr P + BitVec.ofNat 64 (4 * o)) 32) ∧
        (∀ j < slots, slotW s' j = slotW s j) ∧
        (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        Frame [⟨State.addr P, 128⟩] s.mem s'.mem
  | [], s, _, _, _ => ⟨s, runBlock_nil, fun _ h => absurd h List.not_mem_nil, fun _ _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | p :: L, s, hs, hL, hnd => by
    obtain hp := hL p List.mem_cons_self
    have hP := hs.fit
    obtain hA : State.addr (P + BitVec.ofNat 32 (4 * p.2)) = State.addr P + BitVec.ofNat 64 (4 * p.2) :=
      addr_add (by omega_arith)
    let s₁ := s.setReg t0 (slotW s p.1)
    let s₂ := setMem s₁ (s.mem.writeW (State.addr P + BitVec.ofNat 64 (4 * p.2)) (slotW s p.1))
    obtain e₁ : runBlock isa [ldS t0 p.1, .str t0 kp (4 * p.2)] s = some s₂ := by
      rw [runBlock_cons, exec_ldS hs.room hp.1, runStep_some, runBlock_cons,
        exec_str (by omega_arith) (by
          rw [show s₁.gpr kp = P by simp only [s₁, gpr_setReg_of_ne _ _ (show kp ≠ t0 by decide), hs.kp]]
          exact in_off hs.mem hP (by omega_arith) (by omega_arith)),
        runStep_some, runBlock_nil]
      simp only [s₂, s₁, gpr_setReg_of_ne _ _ (show kp ≠ t0 by decide), hs.kp, gpr_setReg_self, mem_setReg, hA]
      rfl
    obtain hsep : ∀ j < slots, Region.Disjoint ⟨State.addr P + BitVec.ofNat 64 (4 * p.2), 4⟩ ⟨slotA s j, 4⟩ := by
      intro j hj
      refine (hs.sep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right ?_
      have := hs.room.fit
      rw [slots_eq] at hj this
      rw [slotA, slot_addr (by omega_arith)]
      exact Offset.sub_base _ (by rw [slots_eq]; omega_arith)
    obtain sl₂ : ∀ j < slots, slotW s₂ j = slotW s j := by
      intro j hj
      show (s.mem.writeW _ _).readW (wordAddr (s₁.gpr sb) j) 32 = _
      rw [show s₁.gpr sb = s.gpr sb from gpr_setReg_of_ne _ _ (by decide)]
      exact Mem.readW_writeW_sep (fun x h1 h2 => hsep j hj x h2 h1) (by decide)
    obtain sb₂ : s₂.gpr sb = s.gpr sb := by
      show (s.setReg t0 (slotW s p.1)).gpr sb = _; exact gpr_setReg_of_ne _ _ (by decide)
    obtain hs₂ : OutPre s₂ P := ⟨hs.room.congr sb₂ rfl,
      by simp only [s₂, gpr_setMem, s₁, gpr_setReg_of_ne _ _ (show kp ≠ t0 by decide), hs.kp], hs.mem, hP,
      by unfold scratchR; rw [sb₂]; exact hs.sep⟩
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', v', o', sl', g', rd', wr', sp', f'⟩ := stores_ok L s₂ hs₂
      (fun q hq => hL q (List.mem_cons_of_mem _ hq)) hnd.2
    obtain hw : ∀ o < 32, s₂.mem.readW (State.addr P + BitVec.ofNat 64 (4 * o)) 32 =
        if o = p.2 then slotW s p.1 else s.mem.readW (State.addr P + BitVec.ofNat 64 (4 * o)) 32 := by
      intro o ho
      show (s.mem.writeW _ _).readW _ 32 = _
      split
      · rename_i e; subst e; exact Mem.readW_writeW_self32 _ _ _
      · rename_i e
        exact Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)
    refine ⟨s', ?_, fun q hq => ?_, fun o ho hoL => ?_, fun j hj => by rw [sl' j hj, sl₂ j hj],
      fun r hr => ?_, by rw [rd']; rfl, by rw [wr']; rfl, by rw [sp']; rfl, ?_⟩
    · rw [storesCode, List.flatMap_cons, runBlock_append, e₁, Option.bind_some]; exact e'
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [o' _ hp.2 hnd.1, hw _ hp.2, ite_eq_left rfl]
      · rw [v' q hq, sl₂ _ (hL q (List.mem_cons_of_mem _ hq)).1]
    · simp only [List.map_cons, List.mem_cons, not_or] at hoL
      rw [o' o ho hoL.2, hw o ho, ite_eq_right hoL.1]
    · rw [g' r hr]; exact gpr_setReg_of_ne _ _ hr
    · refine Frame.trans ?_ f'
      show Frame _ s.mem (s.mem.writeW _ (slotW s p.1))
      exact (Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by omega_arith) (by omega_arith))

/-! ## `G` of eight inputs, to the schedule -/

theorem nodup_map_range {f : Nat → Nat} (hf : ∀ a b, f a = f b → a = b) (n : Nat) :
    ((List.range n).map f).Nodup :=
  List.Pairwise.map f (fun a b hab h => hab (hf a b h)) List.nodup_range

def chunkIn (c : Nat) : List (Nat × Nat) := (List.range 8).map fun w => (uSlot (8 * c + w), tSlot w)
def chunkOut (c : Nat) : List (Nat × Nat) := (List.range 8).map fun w => (tSlot w, 8 * c + w)

theorem keyChunk_eq (c : Nat) :
    keyChunk c = copiesCode (chunkIn c) ++ g8 ++ storesCode (chunkOut c) := by
  simp only [keyChunk, copiesCode, storesCode, chunkIn, chunkOut, List.flatMap_map]

theorem keyChunk_ok {c : Nat} (hc : c < 4) {s : State} (h : Room s) {P : BitVec 32}
    (hp : s.gpr kp = P) (hm : (⟨State.addr P, 128⟩ : Region) ∈ s.wr) (hf : P.toNat + 128 ≤ 2 ^ 32)
    (hsep : Region.Disjoint ⟨State.addr P, 128⟩ (scratchR s)) :
    ∃ s', runBlock isa (keyChunk c) s = some s' ∧
      (∀ w < 8, s'.mem.readW (State.addr P + BitVec.ofNat 64 (4 * (8 * c + w))) 32 =
        Spec.Seed.g (slotW s (uSlot (8 * c + w)))) ∧
      (∀ o < 32, (o < 8 * c ∨ 8 * c + 8 ≤ o) → s'.mem.readW (State.addr P + BitVec.ofNat 64 (4 * o)) 32 =
        s.mem.readW (State.addr P + BitVec.ofNat 64 (4 * o)) 32) ∧
      (∀ j, 56 ≤ j → j < slots → slotW s' j = slotW s j) ∧ Room s' ∧ s'.gpr sb = s.gpr sb ∧ s'.gpr kp = P ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [workR s, ⟨State.addr P, 128⟩] s.mem s'.mem := by
  have hS := slots_eq
  -- The inputs to `G`'s words.
  obtain ⟨s₁, e₁, v₁, o₁, g₁, rd₁, wr₁, sp₁, f₁⟩ := copies_ok h (n := tailSlot) (by decide) (chunkIn c)
    (by intro p hp; simp only [chunkIn, List.mem_map, List.mem_range] at hp; obtain ⟨w, hw, rfl⟩ := hp
        simp [uSlot, aSlot, tSlot, tailSlot, slots_eq]; omega_arith)
    (by intro p hp q hq; simp only [chunkIn, List.mem_map, List.mem_range] at hp hq
        obtain ⟨w, hw, rfl⟩ := hp; obtain ⟨w', hw', rfl⟩ := hq; simp [uSlot, aSlot, tSlot]; omega_arith)
    (by simp only [chunkIn, List.map_map]
        exact nodup_map_range (fun a b hab => by simpa [tSlot] using hab) 8)
  obtain sb₁ : s₁.gpr sb = s.gpr sb := g₁ _ (by decide)
  obtain h₁ : Room s₁ := h.congr sb₁ wr₁
  obtain k₁ : ∀ j, 56 ≤ j → j < slots → slotW s₁ j = slotW s j := fun j h1 h2 => o₁ j h2 (by
    simp only [chunkIn, List.map_map, List.mem_map, List.mem_range, Function.comp, not_exists, not_and]
    intro w hw he; simp [tSlot] at he; omega_arith)
  -- `G`.
  obtain ⟨s₂, e₂, gv₂, k₂, h₂, rd₂, wr₂, sp₂, g₂, f₂⟩ := g8_lanes h₁
  obtain sb₂ : s₂.gpr sb = s.gpr sb := by rw [g₂ _ (by decide), sb₁]
  obtain hO : OutPre s₂ P :=
    ⟨h₂, by rw [g₂ _ (by decide), g₁ _ (by decide), hp], by rw [wr₂, wr₁]; exact hm, hf,
      by unfold scratchR; rw [sb₂]; exact hsep⟩
  -- The stores.
  obtain ⟨s', e', v', o', sl', g', rd', wr', sp', f'⟩ := stores_ok (chunkOut c) s₂ hO
    (by intro p hp; simp only [chunkOut, List.mem_map, List.mem_range] at hp; obtain ⟨w, hw, rfl⟩ := hp
        simp [tSlot, slots_eq]; omega_arith)
    (by simp only [chunkOut, List.map_map]
        exact nodup_map_range (fun a b hab => by simpa using hab) 8)
  obtain sb' : s'.gpr sb = s.gpr sb := by rw [g' _ (by decide), sb₂]
  -- `s`'s memory outside the scratch buffer through the first three steps.
  obtain fr₃ : Frame [workR s] s.mem s₂.mem := by
    exact (by simpa [workR] using f₁ : Frame [workR s] s.mem s₁.mem).trans (by simpa [workR, sb₁] using f₂)
  refine ⟨s', ?_, fun w hw => ?_, fun o ho ho' => ?_, fun j h1 h2 => ?_, h.congr sb' (by rw [wr', wr₂, wr₁]), sb',
    by rw [g' _ (by decide)]; exact hO.kp, by rw [rd', rd₂, rd₁], by rw [wr', wr₂, wr₁], by rw [sp', sp₂, sp₁], ?_⟩
  · rw [keyChunk_eq, runBlock_append, runBlock_append, e₁, Option.bind_some, e₂, Option.bind_some, e']
  · rw [v' (tSlot w, 8 * c + w) (by simp only [chunkOut, List.mem_map, List.mem_range]; exact ⟨w, hw, rfl⟩),
      tSlot_lane, show slotW s₂ (tSlot 0 + w) = lv s₂ (tSlot 0) w from rfl, gv₂ w hw, lv, ← tSlot_lane,
      v₁ (uSlot (8 * c + w), tSlot w) (by simp only [chunkIn, List.mem_map, List.mem_range]; exact ⟨w, hw, rfl⟩)]
  · rw [o' o ho (by
      simp only [chunkOut, List.map_map, List.mem_map, List.mem_range, Function.comp, not_exists, not_and]
      intro w hw he; omega_arith)]
    refine fr₃.readW (r := ⟨State.addr P + BitVec.ofNat 64 (4 * o), 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (hsep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (workR_sub_scratch s)
  · rw [sl' j h2, k₂ j h1 h2, k₁ j h1 h2]
  · refine (fr₃.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (f'.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩)

/-- The four chunks of `G`. -/
theorem keyChunks_ok {s : State} (h : Room s) {P : BitVec 32}
    (hp : s.gpr kp = P) (hm : (⟨State.addr P, 128⟩ : Region) ∈ s.wr) (hf : P.toNat + 128 ≤ 2 ^ 32)
    (hsep : Region.Disjoint ⟨State.addr P, 128⟩ (scratchR s)) :
    ∀ n ≤ 4, ∃ s', runBlock isa ((List.range n).flatMap keyChunk) s = some s' ∧
      (∀ o < 8 * n, s'.mem.readW (State.addr P + BitVec.ofNat 64 (4 * o)) 32 =
        Spec.Seed.g (slotW s (uSlot o))) ∧
      (∀ j, 56 ≤ j → j < slots → slotW s' j = slotW s j) ∧ Room s' ∧ s'.gpr sb = s.gpr sb ∧ s'.gpr kp = P ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [workR s, ⟨State.addr P, 128⟩] s.mem s'.mem := by
  intro n hn
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun o ho => by omega_arith, fun _ _ _ => rfl, h, rfl, hp, rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, e₁, v₁, k₁, h₁, sb₁, kp₁, rd₁, wr₁, sp₁, f₁⟩ := ih (by omega_arith)
    obtain ⟨s₂, e₂, v₂, o₂, k₂, h₂, sb₂, kp₂, rd₂, wr₂, sp₂, f₂⟩ := keyChunk_ok (c := n) (by omega_arith) h₁
      kp₁ (by rw [wr₁]; exact hm) hf (by unfold scratchR; rw [sb₁]; exact hsep)
    refine ⟨s₂, ?_, fun o ho => ?_, fun j h1 h2 => by rw [k₂ j h1 h2, k₁ j h1 h2], h₂, by rw [sb₂, sb₁], kp₂,
      by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁], f₁.trans (by simpa [workR, sb₁] using f₂)⟩
    · rw [List.range_succ, List.flatMap_append, runBlock_append, e₁, Option.bind_some, List.flatMap_singleton, e₂]
    · by_cases hlo : o < 8 * n
      · rw [o₂ o (by omega_arith) (.inl hlo), v₁ o hlo]
      · rw [show o = 8 * n + (o - 8 * n) by omega_arith, v₂ _ (by omega_arith),
          k₁ _ (by simp [uSlot, aSlot]) (uSlot_lt (by omega_arith))]

/-! ## The key's words -/

theorem keyLoad_eq : keyLoad = [.ldr .r4 .r0 0, .rev .r4 .r4, .ldr .r5 .r0 4, .rev .r5 .r5,
    .ldr .r6 .r0 8, .rev .r6 .r6, .ldr .r7 .r0 12, .rev .r7 .r7] := rfl

theorem exec_rev (s : State) (d m : Reg) : exec (.rev d m) s = some (s.setReg d (rev (s.gpr m))) := rfl

theorem ldRev_ok {t : State} {K : BitVec 32} (d : Reg) (h0 : t.gpr .r0 = K)
    (hK : (⟨State.addr K, 16⟩ : Region) ∈ t.rd ++ t.wr) (hfit : K.toNat + 16 ≤ 2 ^ 32) {o : Nat} (ho : o ≤ 12) :
    ∃ t', runBlock isa [.ldr d .r0 o, .rev d d] t = some t' ∧
      t'.gpr d = byteRev32 (t.mem.readW (State.addr K + BitVec.ofNat 64 o) 32) ∧
      (∀ r, r ≠ d → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp := by
  obtain hin : InRegions (t.rd ++ t.wr) (State.addr (t.gpr .r0 + BitVec.ofNat 32 o)) 4 := by
    rw [h0]; exact in_off hK hfit (by omega_arith) (by omega_arith)
  rw [runBlock_cons, exec_ldr (by omega_arith) hin, runStep_some, runBlock_cons, exec_rev, runStep_some, runBlock_nil]
  refine ⟨_, rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · rw [gpr_setReg_self, gpr_setReg_self, h0, addr_add (by omega_arith)]; rfl
  · rw [gpr_setReg_of_ne _ _ hr, gpr_setReg_of_ne _ _ hr]

theorem keyLoad_ok {s : State} {K : BitVec 32} (hr0 : s.gpr .r0 = K)
    (hK : (⟨State.addr K, 16⟩ : Region) ∈ s.rd ++ s.wr) (hfit : K.toNat + 16 ≤ 2 ^ 32) :
    ∃ s', runBlock isa keyLoad s = some s' ∧ kw s' = keyWords (Spec.Seed.blockAt s.mem (State.addr K)) 0 ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ldRev_ok .r4 hr0 hK hfit (o := 0) (by decide)
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := ldRev_ok .r5 (by rw [o₁ _ (by decide), hr0])
    (by rw [rd₁, wr₁]; exact hK) hfit (o := 4) (by decide)
  obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃, sp₃⟩ := ldRev_ok .r6 (by rw [o₂ _ (by decide), o₁ _ (by decide), hr0])
    (by rw [rd₂, wr₂, rd₁, wr₁]; exact hK) hfit (o := 8) (by decide)
  obtain ⟨s₄, e₄, v₄, o₄, m₄, rd₄, wr₄, sp₄⟩ := ldRev_ok .r7
    (by rw [o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide), hr0])
    (by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact hK) hfit (o := 12) (by decide)
  refine ⟨s₄, ?_, ?_, fun r h4 h5 h6 h7 => by rw [o₄ r h7, o₃ r h6, o₂ r h5, o₁ r h4],
    by rw [m₄, m₃, m₂, m₁], by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁], by rw [sp₄, sp₃, sp₂, sp₁]⟩
  · rw [keyLoad_eq, show ([.ldr .r4 .r0 0, .rev .r4 .r4, .ldr .r5 .r0 4, .rev .r5 .r5,
      .ldr .r6 .r0 8, .rev .r6 .r6, .ldr .r7 .r0 12, .rev .r7 .r7] : List Instr) =
      [.ldr .r4 .r0 0, .rev .r4 .r4] ++ ([.ldr .r5 .r0 4, .rev .r5 .r5] ++ ([.ldr .r6 .r0 8, .rev .r6 .r6] ++
      [.ldr .r7 .r0 12, .rev .r7 .r7])) from rfl, runBlock_append, e₁, Option.bind_some, runBlock_append, e₂,
      Option.bind_some, runBlock_append, e₃, Option.bind_some, e₄]
  · simp only [kw, keyWords]
    rw [Proof.Seed.wordAt_blockAt _ _ (by decide), Proof.Seed.wordAt_blockAt _ _ (by decide),
      Proof.Seed.wordAt_blockAt _ _ (by decide), Proof.Seed.wordAt_blockAt _ _ (by decide),
      o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), v₁, o₄ _ (by decide), o₃ _ (by decide), v₂,
      o₄ _ (by decide), v₃, v₄, m₃, m₂, m₁]

/-! ## The whole function -/

theorem expandKey_wp {s₀ : State} (hp : expandKeyArm.pre s₀) :
    WP isa expandKey s₀ fun s' => (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ expandKeyArm.post s₀ s' := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, fitK, fitS, fitB⟩ := hp
  let b := s₀.gpr .r2
  let K := s₀.gpr .r0
  let P := s₀.gpr .r1
  have fitB' : b.toNat + 4 * slots ≤ 2 ^ 32 := fitB
  have fitK' : K.toNat + 16 ≤ 2 ^ 32 := fitK
  have fitS' : P.toNat + 128 ≤ 2 ^ 32 := fitS
  obtain hwS : ScrIn s₀.wr b := ⟨by rw [hwr]; simp [b], fitB⟩
  obtain hwP : (⟨State.addr P, 128⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [P]
  obtain hrK : (⟨State.addr K, 16⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp [K]
  -- The prologue.
  obtain ⟨s₁, e₁, sv₁, g₁, rd₁, wr₁, sp₁, f₁, -⟩ := save_ok (base := .r2) hwS rfl
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := movR_ok s₁ sb .r2
  obtain sb₂ : s₂.gpr sb = b := by rw [r₂, g₁]
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃, sp₃⟩ := movR_ok s₂ kp .r1
  obtain sb₃ : s₃.gpr sb = b := by rw [o₃ _ (by decide), sb₂]
  obtain g₀₃ : ∀ r, r ≠ sb → r ≠ kp → s₃.gpr r = s₀.gpr r := fun r h1 h2 => by rw [o₃ r h2, o₂ r h1, g₁]
  obtain f₀₃ : Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s₃.mem := by rw [m₃, m₂]; exact f₁
  obtain h₃ : Room s₃ := ⟨by unfold scratchR; rw [sb₃, wr₃, wr₂, wr₁]; exact hwS.mem, by rw [sb₃]; exact fitB'⟩
  obtain ptr₃ : s₃.gpr kp = P := by rw [r₃, o₂ _ (by decide), g₁]
  -- The key, as on entry.
  obtain key₃ : Spec.Seed.blockAt s₃.mem (State.addr K) = Spec.Seed.blockAt s₀.mem (State.addr K) := by
    apply Vector.ext; intro i hi
    simp only [Spec.Seed.blockAt, Vector.getElem_ofFn]
    exact f₀₃.bytes (R := ⟨State.addr K, 16⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKB) (by simp only; omega_arith) hi
  -- The key's words.
  obtain ⟨s₄, e₄, k₄, g₄, m₄, rd₄, wr₄, sp₄⟩ := keyLoad_ok (s := s₃) (K := K) (g₀₃ _ (by decide) (by decide))
    (by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact List.mem_append_left _ hrK) fitK'
  obtain sb₄ : s₄.gpr sb = b := by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), sb₃]
  obtain h₄ : Room s₄ := h₃.congr (by rw [sb₄, sb₃]) wr₄
  obtain sl₄ : ∀ j, slotW s₄ j = slotW s₃ j := fun j => by simp only [slotW, m₄, sb₄, sb₃]
  -- The inputs of `G`.
  let key := Spec.Seed.blockAt s₀.mem (State.addr K)
  obtain ⟨s₅, e₅, h₅, -, v₅, o₅, g₅, rd₅, wr₅, sp₅, f₅⟩ := keyRounds_ok key h₄ (by rw [k₄, key₃]) 16 (Nat.le_refl _)
  obtain sb₅ : s₅.gpr sb = b := by rw [g₅ _ (by decide), sb₄]
  obtain keep₅ : ∀ j < slots, uSlot 32 ≤ j → slotW s₅ j = slotW s₃ j := fun j h1 h2 => by
    rw [o₅ j h1 (.inr h2), sl₄]
  -- `G`, to the schedule.
  obtain ⟨s₆, e₆, v₆, k₆, h₆, sb₆, -, rd₆, wr₆, sp₆, f₆⟩ := keyChunks_ok h₅ (P := P)
    (by rw [g₅ _ (by decide), g₄ _ (by decide) (by decide) (by decide) (by decide), ptr₃])
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁]; exact hwP) fitS'
    (by unfold scratchR; rw [sb₅]; exact dSB) 4 (Nat.le_refl _)
  -- The epilogue.
  obtain ⟨s₇, e₇, r₇, o₇, m₇, rd₇, wr₇, sp₇⟩ := movR_ok s₆ .r12 sb
  obtain sv₆ : Saved s₀ b s₆.mem := by
    intro i hi
    obtain hs : savedSlot + i < slots := by rw [savedSlot_eq, slots_eq]; omega_arith
    have := k₆ (savedSlot + i) (by rw [savedSlot_eq]; omega_arith) hs
    simp only [slotW, sb₆, sb₅] at this
    rw [this, show s₅.mem.readW (wordAddr b (savedSlot + i)) 32 = slotW s₅ (savedSlot + i) by
      simp only [slotW, sb₅], keep₅ _ hs (by simp [uSlot, aSlot, savedSlot_eq]; omega_arith), slotW, sb₃, m₃, m₂]
    exact sv₁ i hi
  obtain ⟨s₈, e₈, rg₈, -, m₈, -, -, -⟩ := restore_ok (s₀ := s₀) (b := b)
    (by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]; exact hwS) (by rw [r₇, sb₆, sb₅]) (by rw [m₇]; exact sv₆)
  refine WP.of_runBlock ⟨s₈, ?_, rg₈, ?_⟩
  · rw [runBlock_append, runBlock_append, runBlock_append, runBlock_append, runBlock_append,
      runBlock_append, e₁, Option.bind_some,
      show ([movR sb .r2, movR kp .r1] : List Instr) = [movR sb .r2] ++ [movR kp .r1] from rfl,
      runBlock_append, e₂, Option.bind_some, e₃, Option.bind_some, e₄, Option.bind_some, e₅, Option.bind_some,
      e₆, Option.bind_some, e₇, Option.bind_some, e₈]
  · show Spec.Seed.scheduleAt s₈.mem (State.addr P) = Spec.Seed.expandKey key
    rw [Proof.Seed.expandKey_eq]
    apply Vector.ext; intro i hi
    rw [Proof.Seed.scheduleAt_readW _ _ i hi, Vector.getElem_ofFn, m₈, m₇, v₆ i (by omega_arith), v₅ i (by omega_arith)]

end VG.Proof.Seed.Arm

end

end

/-!
# SEED key expansion on ARMv7 meets its contracts

`expandKey_verified`: `expandKey` is correct (`expandKey_wp`) and constant
time, by the taint analysis: the pointers are public, and so is the
schedule's pointer the code keeps in a slot of the scratch buffer (stored
through `sb`, the buffer's base). `expandKey_framed`
runs it with its working space on the stack, zeroed on return, as
`ecb_framed` does.
-/

@[expose] public section

namespace VG.Proof.Seed.Arm

open VG VG.Arm VG.Impl.Seed.Arm
open VG.Proof.Seed (expandKeyArm)

/-- The initial taint: the pointers are public; `r1` and `r2` point at the
schedule and the scratch buffer, the writable regions. -/
def expandKeyTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2], flags := false, lens := [128, 4 * slots], bases := [(.r1, 0), (.r2, 1)] }

theorem expandKeyTaint_wf {s : State} (h : expandKeyArm.pre s) : VG.Arm.Taint.Wf expandKeyTaint s := by
  obtain ⟨-, hwr, -, -, dSB, -, fitS, fitB⟩ := h
  refine ⟨fun _ => ⟨by simp [hwr, expandKeyTaint], ?_, ?_⟩, fun p hp => ?_, fun h => by simp [expandKeyTaint] at h,
    fun p hp => by simp [expandKeyTaint] at hp⟩
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil]
    exact ⟨dSB, fun _ h => h.elim, trivial⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [toNat_addr] <;> omega_arith
  · simp only [expandKeyTaint, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [VG.Arm.Taint.region, hwr]

theorem expandKeyTaint_agree (s₁ s₂ : State) (h₁ : expandKeyArm.pre s₁) (h₂ : expandKeyArm.pre s₂)
    (hp : expandKeyArm.pub s₁ s₂) : VG.Arm.Taint.Agree expandKeyTaint s₁ s₂ := by
  obtain ⟨p0, p1, p2, -⟩ := hp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, expandKeyTaint_wf h₁, expandKeyTaint_wf h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => by simp [expandKeyTaint] at h, fun k hk => by simp [expandKeyTaint] at hk⟩
  · simp only [expandKeyTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.2.1, h₂.2.1, p1, p2]

theorem expandKey_ct : ConstantTime isa expandKeyArm.pre expandKeyArm.pub expandKey :=
  VG.Taint.constantTime (A := VG.Arm.taint) expandKeyTaint expandKeyTaint_agree (by native_taint_decide)

theorem expandKey_correct (s : State) (hs : expandKeyArm.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandKeyArm.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := expandKey_wp hs
  refine ⟨t, s', he, ⟨fun r hr => ?_, VG.Arm.Exec.sp he⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega_using [])
  · exact h₁ 1 (by omega_using [])
  · exact h₁ 2 (by omega_using [])
  · exact h₁ 3 (by omega_using [])
  · exact h₁ 4 (by omega_using [])
  · exact h₁ 5 (by omega_using [])
  · exact h₁ 6 (by omega_using [])
  · exact h₁ 7 (by omega_using [])
  · exact h₁ 8 (by omega_using [])

/-- A state satisfying the precondition. -/
def expandKeySat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 4 * 188⟩]

theorem expandKey_verified :
    Verified Arm.target expandKey (Proof.Seed.expandKeyScratchContract Arm.abi 94) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Proof.Seed.expandKeyScratchContract, Proof.Seed.expandKeyScratchSig, Proof.Seed.expandKeyPost,
      expandKeyArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr, slots, cntSlot, ptrSlot,
      savedSlot, tableEnd, tableSlot]
      [expandKeySat] using expandKeySat)

/-- A state satisfying the key schedule's precondition: the key at
`0x1000`, the schedule at `0x2000`. -/
def expandKeyFrameSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Seed.expandKeyContract Arm.abi 752).pre s := by
  implies_sat [Spec.Seed.expandKeyContract, Spec.Seed.expandKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [expandKeyFrameSat] using expandKeyFrameSat

/-- Key expansion, with its working space on the stack. -/
theorem expandKey_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withRegScratchWiped 752 .r2 188 expandKey)
      (Spec.Seed.expandKeyContract Arm.abi 752) :=
  Arm.Verified.regScratchWiped (sig := Spec.Seed.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 94) (post := Proof.Seed.expandKeyPost Arm.abi.ptrBits) (wa := false) (stack := 0)
    expandKey_verified (by decide) (by decide) (by decide) (by decide)
    (Proof.Seed.expandKeyPostOut_local _) expandKeyFrameSat_pre

end VG.Proof.Seed.Arm
