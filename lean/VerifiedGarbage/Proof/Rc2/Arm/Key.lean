import VerifiedGarbage.Proof.Rc2.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Impl.Rc2.Arm.ExpandKey
import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc2.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Arm.KeyLoop`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Arm.KeySteps`. -/
section

/-! # Individual Arm RC2 key-expansion steps -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Proof.Rc2.Word32

def keyTemps : List Reg := [.r12, .r0, .r3, .r9, .r10, .r11, .lr]

/-- The public zero flag controls the key-expansion loops. -/
def zeroFlag (s : State) : Option Bool := some s.z

theorem eval_zero (s : State) : eval .eq s = VG.Proof.Rc2.Arm.zeroFlag s := rfl

theorem eval_nonzero (s : State) :
    eval .ne s = (VG.Proof.Rc2.Arm.zeroFlag s).map (!·) := rfl

theorem gpr_subFlags (s : State) (x y : BitVec 32) (r : Reg) :
    (subFlags s x y).gpr r = s.gpr r := rfl

theorem mem_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).mem = s.mem := rfl

theorem rd_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).rd = s.rd := rfl

theorem wr_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).wr = s.wr := rfl

theorem zeroFlag_subFlags (s : State) (x y : BitVec 32) :
    VG.Proof.Rc2.Arm.zeroFlag (subFlags s x y) = some (x - y == 0) := rfl

theorem copyKey_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r4 + s.gpr .r0)) 1)
    (writable : InRegions s.wr (State.addr (s.gpr .r6 + s.gpr .r0)) 1) :
    ∃ s', runBlock isa copyKey s = some s' ∧
      s'.gpr .r0 = s.gpr .r0 + 1 ∧
      VG.Proof.Rc2.Arm.zeroFlag s' = some ((s.gpr .r0 + 1 - s.gpr .r5) == 0) ∧
      Keep VG.Proof.Rc2.Arm.keyTemps
        {s with mem := s.mem.writeW (State.addr (s.gpr .r6 + s.gpr .r0)) (s.mem (State.addr (s.gpr .r4 + s.gpr .r0)))} s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [copyKey, runBlock_cons, runStep_some,
      runBlock_nil, exec, Op2.eval, Option.map_some, State.load8, State.store8,
      BitVec.add_zero, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, readable, writable, ite_true, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, VG.Proof.Rc2.Arm.gpr_subFlags, reduceCtorEq, ite_false, ite_true]
  · simp only [VG.Proof.Rc2.Arm.zeroFlag_subFlags]
  · constructor
    · intro r hr
      have h8 : r ≠ .r12 := by intro h; subst r; exact hr (by decide)
      have h23 : r ≠ .r0 := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .lr := by intro h; subst r; exact hr (by decide)
      simp only [gpr_setReg, VG.Proof.Rc2.Arm.gpr_subFlags, h8, h23, h9, ite_false]
    · simp only [VG.Proof.Rc2.Arm.mem_subFlags, mem_setReg,
        BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide), BitVec.setWidth_eq]
    · rfl
    · rfl

theorem fillInput_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r6 + s.gpr .r0 - 1)) 1)
    (readHi : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r6 + (s.gpr .r0 - s.gpr .r5))) 1) :
    ∃ s', runBlock isa fillInput s = some s' ∧
      s'.gpr .r12 = (s.mem (State.addr (s.gpr .r6 + s.gpr .r0 - 1))).setWidth 32 +
        (s.mem (State.addr (s.gpr .r6 + (s.gpr .r0 - s.gpr .r5)))).setWidth 32 ∧
      Keep [.r12, .r3, .r9, .lr] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [fillInput, runBlock_cons, runStep_some,
      runBlock_nil, exec, Op2.eval, Option.map_some, State.load8,
      BitVec.add_zero, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, readLo, readHi, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg_self]
  · constructor
    · intro r hr
      have h8 : r ≠ .r12 := by intro h; subst r; exact hr (by decide)
      have h3 : r ≠ .r3 := by intro h; subst r; exact hr (by decide)
      have h5 : r ≠ .r9 := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .lr := by intro h; subst r; exact hr (by decide)
      simp only [gpr_setReg, h8, h3, h5, h9, ite_false]
    · rfl
    · rfl
    · rfl

theorem fillOutput_ok (s : State)
    (writable : InRegions s.wr (State.addr (s.gpr .r6 + s.gpr .r0)) 1) :
    ∃ s', runBlock isa fillFinish s = some s' ∧
      s'.gpr .r0 = s.gpr .r0 + 1 ∧
      VG.Proof.Rc2.Arm.zeroFlag s' = some ((s.gpr .r0 + 1 - 128) == 0) ∧
      Keep VG.Proof.Rc2.Arm.keyTemps {s with mem := s.mem.writeW (State.addr (s.gpr .r6 + s.gpr .r0)) ((s.gpr .r12).setWidth 8)} s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [fillFinish, storeKey, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
      runBlock_nil, exec, Op2.eval, Option.map_some, State.store8,
      BitVec.add_zero, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, writable, ite_true, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, VG.Proof.Rc2.Arm.gpr_subFlags, reduceCtorEq, ite_true, ite_false]
  · simp only [VG.Proof.Rc2.Arm.zeroFlag_subFlags]
  · constructor
    · intro r hr
      have h23 : r ≠ .r0 := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .lr := by intro h; subst r; exact hr (by decide)
      simp only [gpr_setReg, VG.Proof.Rc2.Arm.gpr_subFlags, h23, h9, ite_false]
    · simp only [VG.Proof.Rc2.Arm.mem_subFlags, mem_setReg]
    · rfl
    · rfl

theorem reduceInput_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r6 + s.gpr .r0)) 1) :
    ∃ s', runBlock isa reduceInput s = some s' ∧
      s'.gpr .r12 = (s.mem (State.addr (s.gpr .r6 + s.gpr .r0))).setWidth 32 &&& s.gpr .r2 ∧
      Keep [.r12, .lr] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [reduceInput, runBlock_cons, runStep_some,
      runBlock_nil, exec, Op2.eval, Option.map_some, State.load8,
      BitVec.add_zero, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, readable, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg_self]
  · constructor
    · intro r hr
      have h8 : r ≠ .r12 := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .lr := by intro h; subst r; exact hr (by decide)
      simp only [gpr_setReg, h8, h9, ite_false]
    · rfl
    · rfl
    · rfl

theorem storeByte_ok (s : State)
    (writable : InRegions s.wr (State.addr (s.gpr .r6 + s.gpr .r0)) 1) :
    ∃ s', runBlock isa storeKey s = some s' ∧ s'.gpr .r0 = s.gpr .r0 ∧
      Keep [.lr] {s with mem := s.mem.writeW (State.addr (s.gpr .r6 + s.gpr .r0)) ((s.gpr .r12).setWidth 8)} s' := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, storeKey, runBlock_cons, runStep_some,
      runBlock_nil, exec, Op2.eval, Option.map_some, State.store8,
      BitVec.add_zero, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, writable]
    rfl, ?_⟩
  constructor
  · rfl
  · constructor
    · intro r hr
      have h9 : r ≠ .lr := by intro h; subst r; exact hr (by decide)
      simp only [gpr_setReg, h9, ite_false]
    · rfl
    · rfl
    · rfl

theorem descendInput_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r6 + (s.gpr .r0 - 1) + 1)) 1)
    (readHi : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r6 + (s.gpr .r0 - 1 + s.gpr .r1))) 1) :
    ∃ s', runBlock isa descendInput s = some s' ∧
      s'.gpr .r0 = s.gpr .r0 - 1 ∧
      s'.gpr .r12 = (s.mem (State.addr (s.gpr .r6 + (s.gpr .r0 - 1) + 1))).setWidth 32 ^^^
        (s.mem (State.addr (s.gpr .r6 + (s.gpr .r0 - 1 + s.gpr .r1)))).setWidth 32 ∧
      Keep [.r12, .r0, .r3, .r9, .lr] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [descendInput, runBlock_cons, runStep_some,
      runBlock_nil, exec, Op2.eval, Option.map_some, State.load8,
      BitVec.add_zero, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, readLo, readHi, ite_true, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
  · simp only [gpr_setReg_self]
  · constructor
    · intro r hr
      have h8 : r ≠ .r12 := by intro h; subst r; exact hr (by decide)
      have h23 : r ≠ .r0 := by intro h; subst r; exact hr (by decide)
      have h3 : r ≠ .r3 := by intro h; subst r; exact hr (by decide)
      have h5 : r ≠ .r9 := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .lr := by intro h; subst r; exact hr (by decide)
      simp only [gpr_setReg, h8, h23, h3, h5, h9, ite_false]
    · rfl
    · rfl
    · rfl

theorem cmpZero_ok (s : State) :
    ∃ s', runBlock isa [.cmp .r0 (.imm 0)] s = some s' ∧
      VG.Proof.Rc2.Arm.zeroFlag s' = some (s.gpr .r0 == 0) ∧ Keep [] s s' := by
  refine ⟨subFlags s (s.gpr .r0) 0, ?_, ?_⟩
  · simp (config := {decide := true}) only [runBlock_cons, exec, Op2.eval,
      ite_true, Option.map_some, runStep_some, runBlock_nil]
  constructor
  · exact congrArg (fun x : BitVec 32 => some (x == 0)) (by bv_omega)
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

end VG.Proof.Rc2.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Arm.KeyLoop`. -/
section

section

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Impl.Rc2.Arm

theorem fillKey_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r6 + s.gpr .r0 - 1)) 1)
    (readHi : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r6 + (s.gpr .r0 - s.gpr .r5))) 1)
    (writable : InRegions s.wr (State.addr (s.gpr .r6 + s.gpr .r0)) 1) :
    WP isa (.block fillKey) s (fun s' =>
      s'.gpr .r0 = s.gpr .r0 + 1 ∧
      VG.Proof.Rc2.Arm.zeroFlag s' = some ((s.gpr .r0 + 1 - 128) == 0) ∧
      Keep VG.Proof.Rc2.Arm.keyTemps {s with
        mem := s.mem.writeW (State.addr (s.gpr .r6 + s.gpr .r0))
          (Spec.Rc2.pi (s.mem (State.addr (s.gpr .r6 + s.gpr .r0 - 1)) +
          s.mem (State.addr (s.gpr .r6 + (s.gpr .r0 - s.gpr .r5)))))} s') := by
  rw [fillKey, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := VG.Proof.Rc2.Arm.fillInput_ok s readLo readHi
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  apply WP.mono (piLookup_ok s₁)
  intro s₂ h₂
  have k₁ : Keep VG.Proof.Rc2.Arm.keyTemps s s₁ := keep₁.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h <;> subst r <;> decide)
  have k₂ : Keep VG.Proof.Rc2.Arm.keyTemps s₁ s₂ := h₂.2.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h <;> subst r <;> decide)
  have keep := k₁.trans k₂
  have ptr := keep.reg .r6 (by decide)
  have index := (keep₁.reg .r0 (by decide)).trans rfl
  have index₂ : s₂.gpr .r0 = s.gpr .r0 := (h₂.2.reg .r0 (by decide)).trans index
  have write₂ : InRegions s₂.wr (State.addr (s₂.gpr .r6 + s₂.gpr .r0)) 1 := by
    rw [keep.wr, ptr, index₂]; exact writable
  obtain ⟨s₃, run₃, out₃, flag₃, keep₃⟩ := VG.Proof.Rc2.Arm.fillOutput_ok s₂ write₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  refine ⟨by rw [out₃, index₂], by rw [flag₃, index₂], ?_⟩
  constructor
  · intro r hr
    exact (keep₃.reg r hr).trans (keep.reg r hr)
  · rw [keep₃.mem, keep.mem, ptr, index₂, h₂.1, out₁]
    simp [BitVec.setWidth_add]
  · exact keep₃.rd.trans keep.rd
  · exact keep₃.wr.trans keep.wr

theorem piStore_ok (s : State) (writable : InRegions s.wr (State.addr (s.gpr .r6 + s.gpr .r0)) 1) :
    WP isa (.block (piLookup ++ storeKey)) s (fun s' =>
      s'.gpr .r0 = s.gpr .r0 ∧
      Keep VG.Proof.Rc2.Arm.keyTemps {s with
        mem := s.mem.writeW (State.addr (s.gpr .r6 + s.gpr .r0)) (Spec.Rc2.pi ((s.gpr .r12).setWidth 8))} s') := by
  rw [WP.block_append_iff]
  apply WP.mono (piLookup_ok s)
  intro s₁ h₁
  have ptr := h₁.2.reg .r6 (by decide)
  have index := h₁.2.reg .r0 (by decide)
  have valid : InRegions s₁.wr (State.addr (s₁.gpr .r6 + s₁.gpr .r0)) 1 := by
    rw [h₁.2.wr, ptr, index]; exact writable
  obtain ⟨s₂, run₂, index₂, keep₂⟩ := VG.Proof.Rc2.Arm.storeByte_ok s₁ valid
  refine WP.of_runBlock ⟨s₂, run₂, index₂.trans index, ?_⟩
  constructor
  · intro r hr
    rw [keep₂.reg r (by intro hm; simp only [List.mem_singleton] at hm; subst r; exact hr (by decide))]
    exact h₁.2.reg r (fun hm => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h <;> subst r <;> decide))
  · rw [keep₂.mem, h₁.2.mem, ptr, index, h₁.1]
    simp
  · exact keep₂.rd.trans h₁.2.rd
  · exact keep₂.wr.trans h₁.2.wr

theorem reduceKey_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r6 + s.gpr .r0)) 1)
    (writable : InRegions s.wr (State.addr (s.gpr .r6 + s.gpr .r0)) 1) :
    WP isa (.block reduceKey) s (fun s' => s'.gpr .r0 = s.gpr .r0 ∧
      Keep VG.Proof.Rc2.Arm.keyTemps {s with
        mem := s.mem.writeW (State.addr (s.gpr .r6 + s.gpr .r0))
          (Spec.Rc2.pi (s.mem (State.addr (s.gpr .r6 + s.gpr .r0)) &&& (s.gpr .r2).setWidth 8))} s') := by
  rw [reduceKey, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := VG.Proof.Rc2.Arm.reduceInput_ok s readable
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have ptr := keep₁.reg .r6 (by decide)
  have index := keep₁.reg .r0 (by decide)
  have valid : InRegions s₁.wr (State.addr (s₁.gpr .r6 + s₁.gpr .r0)) 1 := by
    rw [keep₁.wr, ptr, index]; exact writable
  apply WP.mono (VG.Proof.Rc2.Arm.piStore_ok s₁ valid)
  intro s₂ h₂
  refine ⟨h₂.1.trans index, ?_⟩
  constructor
  · intro r hr
    exact (h₂.2.reg r hr).trans (keep₁.reg r (by
      intro hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h <;> subst r <;> exact hr (by decide)))
  · rw [h₂.2.mem, keep₁.mem, ptr, index, out₁]
    simp
  · exact h₂.2.rd.trans keep₁.rd
  · exact h₂.2.wr.trans keep₁.wr

theorem descendKey_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r6 + (s.gpr .r0 - 1) + 1)) 1)
    (readHi : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r6 + (s.gpr .r0 - 1 + s.gpr .r1))) 1)
    (writable : InRegions s.wr (State.addr (s.gpr .r6 + (s.gpr .r0 - 1))) 1) :
    WP isa (.block descendKey) s (fun s' =>
      s'.gpr .r0 = s.gpr .r0 - 1 ∧ VG.Proof.Rc2.Arm.zeroFlag s' = some ((s.gpr .r0 - 1) == 0) ∧
      Keep VG.Proof.Rc2.Arm.keyTemps {s with
        mem := s.mem.writeW (State.addr (s.gpr .r6 + (s.gpr .r0 - 1)))
          (Spec.Rc2.pi (s.mem (State.addr (s.gpr .r6 + (s.gpr .r0 - 1) + 1)) ^^^
            s.mem (State.addr (s.gpr .r6 + (s.gpr .r0 - 1 + s.gpr .r1)))))} s') := by
  rw [descendKey, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, index₁, out₁, keep₁⟩ := VG.Proof.Rc2.Arm.descendInput_ok s readLo readHi
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have ptr := keep₁.reg .r6 (by decide)
  have valid : InRegions s₁.wr (State.addr (s₁.gpr .r6 + s₁.gpr .r0)) 1 := by
    rw [keep₁.wr, ptr, index₁]; exact writable
  rw [← List.append_assoc, WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.Arm.piStore_ok s₁ valid)
  intro s₂ h₂
  obtain ⟨s₃, run₃, flag₃, keep₃⟩ := VG.Proof.Rc2.Arm.cmpZero_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have index₂ := h₂.1.trans index₁
  refine ⟨(keep₃.reg .r0 (by decide)).trans index₂, by rw [flag₃, index₂], ?_⟩
  constructor
  · intro r hr
    exact ((keep₃.reg r (by simp)).trans (h₂.2.reg r hr)).trans (keep₁.reg r (fun hm => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h | h <;> subst r <;> decide)))
  · rw [keep₃.mem, h₂.2.mem, keep₁.mem, ptr, index₁, out₁]
    simp
  · exact keep₃.rd.trans (h₂.2.rd.trans keep₁.rd)
  · exact keep₃.wr.trans (h₂.2.wr.trans keep₁.wr)


end VG.Proof.Rc2.Arm

end

/-! # A bounded loop rule and frame invariant for key expansion -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Impl.Rc2.Arm

theorem forwardLoop (body : Prog isa) (I : Nat → State → Prop) (stop : Nat)
    (step : ∀ i < stop, ∀ s, I i s → WP isa body s (fun s' =>
      I (i + 1) s' ∧ VG.Proof.Rc2.Arm.zeroFlag s' = some (decide (i + 1 = stop))))
    (i : Nat) (hi : i < stop) (s : State) (hs : I i s) :
    WP isa (.loop body .ne) s (I stop) := by
  let Inv (n : Nat) (s : State) := ∃ i, i < stop ∧ stop - i = n ∧ I i s
  refine WP.loop (M := isa) Inv ?_ (stop - i) s ⟨i, hi, rfl, hs⟩
  intro n s ⟨j, hj, hn, hI⟩
  apply WP.mono (step j hj s hI)
  intro s' h'
  by_cases he : j + 1 = stop
  · left
    constructor
    · simp only [VG.Proof.Rc2.Arm.eval_nonzero, h'.2, he, decide_true, Option.map_some, Bool.not_true]
    · rw [he] at h'
      exact h'.1
  · right
    constructor
    · simp only [VG.Proof.Rc2.Arm.eval_nonzero, h'.2, he, decide_false, Option.map_some, Bool.not_false]
    · exact ⟨stop - (j + 1), by omega, j + 1, by omega, rfl, h'.1⟩

/-- Across a key-expansion loop only the six temporaries and the schedule
buffer change. The key, scratch saves, and return address are separate. -/
structure KeyFrame (s₀ s : State) : Prop where
  reg : ∀ r, r ∉ VG.Proof.Rc2.Arm.keyTemps → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Frame [⟨State.addr (s₀.gpr .r6), 128⟩] s₀.mem s.mem

theorem KeyFrame.refl (s : State) : VG.Proof.Rc2.Arm.KeyFrame s s :=
  ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩

theorem KeyFrame.trans {s₀ s₁ s₂ : State} (h₁ : VG.Proof.Rc2.Arm.KeyFrame s₀ s₁) (h₂ : VG.Proof.Rc2.Arm.KeyFrame s₁ s₂) :
    VG.Proof.Rc2.Arm.KeyFrame s₀ s₂ := by
  refine ⟨fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, ?_⟩
  have frame₂ := h₂.mem
  rw [h₁.reg .r6 (by decide)] at frame₂
  exact h₁.mem.trans frame₂

theorem KeyFrame.step {s₀ s s' : State} (h : VG.Proof.Rc2.Arm.KeyFrame s₀ s) (i : Nat) (hi : i < 128)
    (b : Byte) (keep : Keep VG.Proof.Rc2.Arm.keyTemps {s with mem := s.mem.writeW (State.addr (s₀.gpr .r6) + BitVec.ofNat 64 i) b} s') : VG.Proof.Rc2.Arm.KeyFrame s₀ s' := by
  refine ⟨fun r hr => (keep.reg r hr).trans (h.reg r hr), keep.rd.trans h.rd,
    keep.wr.trans h.wr, ?_⟩
  rw [keep.mem]
  exact h.mem.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))

theorem KeyFrame.keep {s₀ s s' : State} (h : VG.Proof.Rc2.Arm.KeyFrame s₀ s) (keep : Keep VG.Proof.Rc2.Arm.keyTemps s s') :
    VG.Proof.Rc2.Arm.KeyFrame s₀ s' := by
  refine ⟨fun r hr => (keep.reg r hr).trans (h.reg r hr), keep.rd.trans h.rd,
    keep.wr.trans h.wr, ?_⟩
  rw [keep.mem]; exact h.mem

theorem counter_add (i : Nat) : BitVec.ofNat 32 i + 1 = BitVec.ofNat 32 (i + 1) := by
  rw [BitVec.ofNat_add]
  rfl

theorem counter_eq (i n : Nat) (hi : i < 2 ^ 32) (hn : n < 2 ^ 32) :
    ((BitVec.ofNat 32 i - BitVec.ofNat 32 n) == 0#32) = decide (i = n) := by
  have he : (BitVec.ofNat 32 i - BitVec.ofNat 32 n = 0#32) ↔ i = n := by bv_omega
  apply Bool.eq_iff_iff.mpr
  simpa only [beq_iff_eq, decide_eq_true_eq] using he

theorem counter_sub (i : Nat) (hi : 1 ≤ i) :
    BitVec.ofNat 32 i - 1 = BitVec.ofNat 32 (i - 1) :=
  Offset.ofNat_sub_ofNat hi

end VG.Proof.Rc2.Arm

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Arm.KeyIO`. -/
section

section

/-! # Public effective-key mask selection -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Proof.Rc2.Word32

theorem small_imm (i : Nat) (hi : i < 256) :
    (BitVec.ofNat 16 i).setWidth 32 = BitVec.ofNat 32 i := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem cmpMask_ok (s : State) (i : Nat) (hi : i < 7) :
    ∃ s', runBlock isa [.cmp .r9 (.imm (BitVec.ofNat 32 (i + 1)))] s = some s' ∧
      zeroFlag s' = some (s.gpr .r9 == BitVec.ofNat 32 (i + 1)) ∧ Keep [] s s' := by
  have enc : encodable (BitVec.ofNat 32 (i + 1)) = true := by
    have fact : ∀ i < 7, encodable (BitVec.ofNat 32 (i + 1)) = true := by decide
    exact fact i hi
  refine ⟨subFlags s (s.gpr .r9) (BitVec.ofNat 32 (i + 1)), ?_, ?_⟩
  · simp only [runBlock_cons, exec, Op2.eval, enc, ite_true, Option.map_some, runStep_some, runBlock_nil]
  constructor
  · change some ((s.gpr .r9 - BitVec.ofNat 32 (i + 1)) == 0) = _
    apply congrArg some
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    bv_omega
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem setMask_ok (s : State) (i : Nat) (hi : i < 7) :
    ∃ s', runBlock isa [imm .r2 (2 ^ (i + 1) - 1)] s = some s' ∧
      s'.gpr .r2 = BitVec.ofNat 32 (2 ^ (i + 1) - 1) ∧ Keep [.r2] s s' := by
  refine ⟨_, by
    simp only [imm, runBlock_cons, exec]
    rfl, ?_⟩
  constructor
  · simp only [gpr_setReg_self]
    apply small_imm
    have bound : ∀ i < 7, 2 ^ (i + 1) - 1 < 256 := by decide
    exact bound i hi
  · exact ⟨fun r hr => gpr_setReg_of_ne _ _ (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; exact hr), rfl, rfl, rfl⟩

theorem maskBranch_ok (s : State) (i : Nat) (hi : i < 7) :
    WP isa (.seq (.block [.cmp .r9 (.imm (BitVec.ofNat 32 (i + 1)))])
      (.ite .eq (.block [imm .r2 (2 ^ (i + 1) - 1)]) (.block []))) s (fun s' =>
        s'.gpr .r2 = (if s.gpr .r9 = BitVec.ofNat 32 (i + 1)
          then BitVec.ofNat 32 (2 ^ (i + 1) - 1) else s.gpr .r2) ∧ Keep [.r2] s s') := by
  apply WP.seq
  obtain ⟨s₁, run₁, flag₁, keep₁⟩ := cmpMask_ok s i hi
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  apply WP.ite (s.gpr .r9 == BitVec.ofNat 32 (i + 1)) (by exact flag₁)
  · intro he
    have eq := beq_iff_eq.mp he
    obtain ⟨s₂, run₂, out₂, keep₂⟩ := setMask_ok s₁ i hi
    apply WP.of_runBlock
    refine ⟨s₂, run₂, ?_, ?_⟩
    · rw [ite_eq_left eq]; exact out₂
    · exact (keep₁.weaken (by simp)).trans keep₂
  · intro he
    have ne : s.gpr .r9 ≠ BitVec.ofNat 32 (i + 1) := by simpa using he
    apply WP.block_nil
    refine ⟨?_, keep₁.weaken (by simp)⟩
    rw [ite_eq_right ne]
    exact keep₁.reg .r2 (by simp)

private theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} :
    WP isa (.seq (.seq a b) c) s Q ↔ WP isa (.seq a (.seq b c)) s Q := by
  constructor
  · intro h
    exact WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)
  · intro h
    exact WP.seq (WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h => WP.seq_iff.mp h))

theorem maskBranches_ok (is : List Nat) (hi : ∀ i ∈ is, i < 7)
    (s : State) (k : Nat) (hk : k < 8) (index : s.gpr .r9 = BitVec.ofNat 32 k) :
    WP isa (is.foldr (fun i rest =>
      .seq (.block [.cmp .r9 (.imm (BitVec.ofNat 32 (i + 1)))])
        (.seq (.ite .eq (.block [imm .r2 (2 ^ (i + 1) - 1)]) (.block [])) rest)) (.block []))
      s (fun s' => s'.gpr .r2 = (if k ∈ is.map (· + 1) then
        BitVec.ofNat 32 (2 ^ k - 1) else s.gpr .r2) ∧ Keep [.r2] s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.foldr_cons, ← seq_assoc]
    apply WP.seq
    apply WP.mono (maskBranch_ok s i (hi i List.mem_cons_self))
    intro s₁ h₁
    have index₁ := (h₁.2.reg .r9 (by decide)).trans index
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁ index₁)
    intro s₂ h₂
    refine ⟨?_, h₁.2.trans h₂.2⟩
    rw [h₂.1, h₁.1, index]
    have eq : BitVec.ofNat 32 k = BitVec.ofNat 32 (i + 1) ↔ k = i + 1 := by
      have bound := hi i List.mem_cons_self
      bv_omega
    simp only [eq, List.map_cons, List.mem_cons]
    by_cases he : k = i + 1
    · subst k; simp
    · by_cases hm : k ∈ is.map (· + 1) <;> simp [he, hm]

theorem maskStart_ok (s : State) :
    ∃ s', runBlock isa ([rr .r9 .r7] ++ mask .r9 3 ++ [imm .r2 255]) s = some s' ∧
      s'.gpr .r9 = s.gpr .r7 &&& 7 ∧ s'.gpr .r2 = 255 ∧ Keep [.r2, .r9] s s' := by
  refine ⟨_, by
    simp only [↓reduceIte, Nat.reduceLeDiff, Nat.reduceSub, and_self, rr, imm, mask, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Option.map_some, gpr_setReg,
      ]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_false, ite_true]
    rw [maskBits _ 3 (by decide)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_and]
    change (s.gpr .r7).toNat % 8 % 2 ^ 32 = (s.gpr .r7).toNat &&& (2 ^ 3 - 1)
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  · rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, hr.1, hr.2, ite_false]
    · rfl
    · rfl
    · rfl

theorem maskCode_ok (s : State) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (input : s.gpr .r7 = BitVec.ofNat 32 bits) :
    WP isa maskCode s (fun s' =>
      (s'.gpr .r2).setWidth 8 = BitVec.ofNat 8 (255 % 2 ^ (8 + bits - 8 * ((bits + 7) / 8))) ∧
      Keep [.r2, .r9] s s') := by
  rw [maskCode]
  apply WP.seq
  obtain ⟨s₁, run₁, index₁, mask₁, keep₁⟩ := maskStart_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have index : s₁.gpr .r9 = BitVec.ofNat 32 (bits % 8) := by
    rw [index₁, input]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    change bits % 2 ^ 32 &&& (2 ^ 3 - 1) = bits % 8 % 2 ^ 32
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  apply WP.mono (maskBranches_ok (List.range 7) (by simp)
    s₁ (bits % 8) (Nat.mod_lt _ (by decide)) index)
  intro s₂ h₂
  refine ⟨?_, keep₁.trans (h₂.2.weaken (by simp))⟩
  rw [h₂.1, mask₁]
  have exponent : 8 + bits - 8 * ((bits + 7) / 8) = if bits % 8 = 0 then 8 else bits % 8 := by
    split <;> omega
  rw [exponent]
  have fact : ∀ r < 8,
      ((if r ∈ (List.range 7).map (· + 1) then BitVec.ofNat 32 (2 ^ r - 1)
        else 255).setWidth 8) = BitVec.ofNat 8 (255 % 2 ^ (if r = 0 then 8 else r)) := by decide
  exact fact _ (Nat.mod_lt _ (by decide))

end VG.Proof.Rc2.Arm

end

section

/-! # The descending effective-key reduction loop -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Impl.Rc2.Arm

theorem descendLoop_ok (s : State) (l : KeyBytes) (t8 : Nat) (ht : 1 ≤ t8) (ht' : t8 < 128)
    (outFit : (s.gpr .r6).toNat + 128 ≤ 2 ^ 32)
    (len : s.gpr .r1 = BitVec.ofNat 32 t8) (start : s.gpr .r0 = BitVec.ofNat 32 (128 - t8))
    (writable : ∀ i < 128, InRegions s.wr (State.addr (s.gpr .r6) + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (State.addr (s.gpr .r6)) l 128) :
    WP isa (.loop (.block descendKey) .ne) s (fun s' =>
      s'.gpr .r0 = 0 ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (State.addr (s.gpr .r6)) (descend l t8 (128 - t8)) 128) := by
  let I (j : Nat) (s' : State) := s'.gpr .r0 = BitVec.ofNat 32 (128 - t8 - j) ∧ KeyFrame s s' ∧
    BytesPrefix s'.mem (State.addr (s.gpr .r6)) (descend l t8 j) 128
  have finish : I (128 - t8) = (fun s' => s'.gpr .r0 = 0 ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (State.addr (s.gpr .r6)) (descend l t8 (128 - t8)) 128) := by
    funext s'
    simp only [I, Nat.sub_self]
    rfl
  rw [← finish]
  apply forwardLoop (.block descendKey) I (128 - t8) _ 0 (by omega) s
    ⟨start, KeyFrame.refl s, initialPrefix⟩
  intro j hj s₁ ⟨index₁, frame₁, prefix₁⟩
  have outPtr := frame₁.reg .r6 (by decide)
  have len₁ := (frame₁.reg .r1 (by decide)).trans len
  have indexNew : s₁.gpr .r0 - 1 = BitVec.ofNat 32 (127 - t8 - j) := by
    rw [index₁, counter_sub _ (show 1 ≤ 128 - t8 - j by omega)]
    congr 1; omega
  have loAddr : State.addr (s₁.gpr .r6 + (s₁.gpr .r0 - 1) + 1) =
      State.addr (s.gpr .r6) + BitVec.ofNat 64 (127 - t8 - j + 1) := by
    rw [outPtr, indexNew, BitVec.add_assoc, counter_add]
    exact addr_add (by omega)
  have hiAddr : State.addr (s₁.gpr .r6 + (s₁.gpr .r0 - 1 + s₁.gpr .r1)) =
      State.addr (s.gpr .r6) + BitVec.ofNat 64 (127 - t8 - j + t8) := by
    rw [outPtr, indexNew, len₁, ← BitVec.ofNat_add]
    exact addr_add (by omega)
  have read₁ (i : Nat) (hi : i < 128) :
      InRegions (s₁.rd ++ s₁.wr) (State.addr (s.gpr .r6) + BitVec.ofNat 64 i) 1 := by
    obtain ⟨r, hr, hc⟩ := writable i hi
    rw [frame₁.wr]
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have write₁ : InRegions s₁.wr (State.addr (s₁.gpr .r6 + (s₁.gpr .r0 - 1))) 1 := by
    rw [frame₁.wr, outPtr, indexNew, addr_add (by omega)]
    exact writable _ (by omega)
  have readLo : InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.gpr .r6 + (s₁.gpr .r0 - 1) + 1)) 1 := by
    rw [loAddr]; exact read₁ _ (by omega)
  have readHi : InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.gpr .r6 + (s₁.gpr .r0 - 1 + s₁.gpr .r1))) 1 := by
    rw [hiAddr]; exact read₁ _ (by omega)
  apply WP.mono (descendKey_ok s₁ readLo readHi write₁)
  intro s₂ h₂
  let b := Spec.Rc2.pi ((descend l t8 j).getD (127 - t8 - j + 1) 0 ^^^
    (descend l t8 j).getD (127 - t8 - j + t8) 0)
  have keep₂ : Keep keyTemps {s₁ with
      mem := s₁.mem.writeW (State.addr (s.gpr .r6) + BitVec.ofNat 64 (127 - t8 - j)) b} s₂ := by
    have h := h₂.2.2
    rw [loAddr, hiAddr, prefix₁ _ (by omega), prefix₁ _ (by omega), outPtr, indexNew, addr_add (by omega)] at h
    exact h
  constructor
  · refine ⟨?_, frame₁.step (127 - t8 - j) (by omega) b keep₂, ?_⟩
    · rw [h₂.1]
      change s₁.gpr .r0 - 1 = _
      rw [indexNew]
      congr 1; omega
    · rw [keep₂.mem, descend_succ]
      exact prefix₁.write (by decide) (by omega) b
  · rw [h₂.2.1]
    change some ((s₁.gpr .r0 - 1) == 0#32) = _
    rw [indexNew]
    have he : 127 - t8 - j = 0 ↔ j + 1 = 128 - t8 := by omega
    have eqZero := counter_eq (127 - t8 - j) 0 (by omega) (by decide)
    simp only [BitVec.sub_zero] at eqZero
    rw [eqZero]
    simp only [he]

end VG.Proof.Rc2.Arm

end

section

section

/-! # Forward expansion to 128 bytes -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Impl.Rc2.Arm

theorem fillLoop_ok (s : State) (key : List Byte) (ht : 1 ≤ key.length) (ht' : key.length < 128)
    (outFit : (s.gpr .r6).toNat + 128 ≤ 2 ^ 32)
    (len : s.gpr .r5 = BitVec.ofNat 32 key.length) (start : s.gpr .r0 = BitVec.ofNat 32 key.length)
    (writable : ∀ i < 128, InRegions s.wr (State.addr (s.gpr .r6) + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (State.addr (s.gpr .r6)) (fill key 0) key.length) :
    WP isa (.loop (.block fillKey) .ne) s (fun s' =>
      s'.gpr .r0 = 128 ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (State.addr (s.gpr .r6)) (fill key (128 - key.length)) 128) := by
  let I (j : Nat) (s' : State) := s'.gpr .r0 = BitVec.ofNat 32 (key.length + j) ∧ KeyFrame s s' ∧
    BytesPrefix s'.mem (State.addr (s.gpr .r6)) (fill key j) (key.length + j)
  have finish : I (128 - key.length) = (fun s' => s'.gpr .r0 = 128 ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (State.addr (s.gpr .r6)) (fill key (128 - key.length)) 128) := by
    funext s'
    simp only [I, Nat.add_sub_of_le (Nat.le_of_lt ht')]
    rfl
  rw [← finish]
  apply forwardLoop (.block fillKey) I (128 - key.length) _ 0 (by omega) s
    ⟨start, KeyFrame.refl s, initialPrefix⟩
  intro j hj s₁ ⟨index₁, frame₁, prefix₁⟩
  have outPtr := frame₁.reg .r6 (by decide)
  have len₁ := (frame₁.reg .r5 (by decide)).trans len
  have loAddr : State.addr (s₁.gpr .r6 + s₁.gpr .r0 - 1) =
      State.addr (s.gpr .r6) + BitVec.ofNat 64 (key.length + j - 1) := by
    rw [outPtr, index₁, BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg, counter_sub _ (by omega)]
    exact addr_add (by omega)
  have hiAddr : State.addr (s₁.gpr .r6 + (s₁.gpr .r0 - s₁.gpr .r5)) =
      State.addr (s.gpr .r6) + BitVec.ofNat 64 j := by
    rw [outPtr, index₁, len₁, Offset.ofNat_sub_ofNat (by omega), Nat.add_sub_cancel_left]
    exact addr_add (by omega)
  have read₁ (i : Nat) (hi : i < 128) :
      InRegions (s₁.rd ++ s₁.wr) (State.addr (s.gpr .r6) + BitVec.ofNat 64 i) 1 := by
    obtain ⟨r, hr, hc⟩ := writable i hi
    rw [frame₁.wr]
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have write₁ : InRegions s₁.wr (State.addr (s₁.gpr .r6 + s₁.gpr .r0)) 1 := by
    rw [frame₁.wr, outPtr, index₁, addr_add (by omega)]
    exact writable _ (by omega)
  have readLo : InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.gpr .r6 + s₁.gpr .r0 - 1)) 1 := by
    rw [loAddr]; exact read₁ _ (by omega)
  have readHi : InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.gpr .r6 + (s₁.gpr .r0 - s₁.gpr .r5))) 1 := by
    rw [hiAddr]; exact read₁ _ (by omega)
  apply WP.mono (fillKey_ok s₁ readLo readHi write₁)
  intro s₂ h₂
  let b := Spec.Rc2.pi ((fill key j).getD (key.length + j - 1) 0 + (fill key j).getD j 0)
  have keep₂ : Keep keyTemps {s₁ with
      mem := s₁.mem.writeW (State.addr (s.gpr .r6) + BitVec.ofNat 64 (key.length + j)) b} s₂ := by
    have h := h₂.2.2
    rw [loAddr, hiAddr, prefix₁ _ (by omega), prefix₁ _ (by omega), outPtr, index₁, addr_add (by omega)] at h
    exact h
  constructor
  · refine ⟨?_, frame₁.step (key.length + j) (by omega) b keep₂, ?_⟩
    · rw [h₂.1, index₁, counter_add, Nat.add_assoc]
    · rw [keep₂.mem, fill_succ]
      have h := prefix₁.extend (show key.length + j < 128 by omega) b
      simpa only [fillStep, Nat.add_sub_cancel_left, Nat.add_assoc] using h
  · rw [h₂.2.1, index₁, counter_add]
    have he : key.length + j + 1 = 128 ↔ j + 1 = 128 - key.length := by omega
    change some ((BitVec.ofNat 32 (key.length + j + 1) - BitVec.ofNat 32 128) == 0#32) = _
    rw [counter_eq _ _ (by omega) (by decide)]
    simp only [he]

end VG.Proof.Rc2.Arm

end

section

/-! # The key-copy loop -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Impl.Rc2.Arm

theorem copyLoop_ok (s : State) (t : Nat) (ht : 1 ≤ t) (ht' : t ≤ 128)
    (keyFit : (s.gpr .r4).toNat + t ≤ 2 ^ 32)
    (outFit : (s.gpr .r6).toNat + 128 ≤ 2 ^ 32)
    (len : s.gpr .r5 = BitVec.ofNat 32 t) (zero : s.gpr .r0 = 0)
    (readable : ∀ i < t, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r4) + BitVec.ofNat 64 i) 1)
    (writable : ∀ i < 128, InRegions s.wr (State.addr (s.gpr .r6) + BitVec.ofNat 64 i) 1)
    (sep : (Region.mk (State.addr (s.gpr .r4)) t).Disjoint ⟨State.addr (s.gpr .r6), 128⟩) :
    WP isa (.loop (.block copyKey) .ne) s (fun s' =>
      s'.gpr .r0 = BitVec.ofNat 32 t ∧ KeyFrame s s' ∧
      BytesPrefix s'.mem (State.addr (s.gpr .r6)) (fill (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r4)) t) 0) t) := by
  let key := Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r4)) t
  let I (i : Nat) (s' : State) := s'.gpr .r0 = BitVec.ofNat 32 i ∧ KeyFrame s s' ∧
    BytesPrefix s'.mem (State.addr (s.gpr .r6)) (fill key 0) i
  apply forwardLoop (.block copyKey) I t _ 0 (by omega) s
    ⟨zero, KeyFrame.refl s, fun i hi => by omega⟩
  intro i hi s₁ ⟨index₁, frame₁, prefix₁⟩
  have keyPtr := frame₁.reg .r4 (by decide)
  have outPtr := frame₁.reg .r6 (by decide)
  have len₁ := (frame₁.reg .r5 (by decide)).trans len
  have read₁ : InRegions (s₁.rd ++ s₁.wr) (State.addr (s₁.gpr .r4 + s₁.gpr .r0)) 1 := by
    rw [frame₁.rd, frame₁.wr, keyPtr, index₁, addr_add (by omega)]
    exact readable i hi
  have write₁ : InRegions s₁.wr (State.addr (s₁.gpr .r6 + s₁.gpr .r0)) 1 := by
    rw [frame₁.wr, outPtr, index₁, addr_add (by omega)]
    exact writable i (by omega)
  have byte₁ : s₁.mem (State.addr (s₁.gpr .r4 + s₁.gpr .r0)) = key.getD i 0 := by
    rw [keyPtr, index₁, addr_add (by omega), bytesAt_getD _ _ _ _ hi]
    exact frame₁.mem.bytes (by simpa using sep) (by change t ≤ 2 ^ 64; omega) hi
  obtain ⟨s₂, run₂, index₂, flag₂, keep₂⟩ := copyKey_ok s₁ read₁ write₁
  have keep₂' : Keep keyTemps
      {s₁ with mem := s₁.mem.writeW (State.addr (s.gpr .r6) + BitVec.ofNat 64 i) (key.getD i 0)} s₂ := by
    rw [byte₁] at keep₂
    simpa only [outPtr, index₁, addr_add (by omega : (s.gpr .r6).toNat + i < 2 ^ 32)] using keep₂
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  constructor
  · refine ⟨?_, frame₁.step i (by omega) _ keep₂', ?_⟩
    · rw [index₂, index₁, counter_add]
    · rw [keep₂'.mem]
      have prefix₂ := prefix₁.extend (show i < 128 by omega) (key.getD i 0)
      rw [initial_set key i] at prefix₂
      exact prefix₂
  · rw [flag₂, index₁, len₁, counter_add]
    exact congrArg some (counter_eq (i + 1) t (by omega) (by omega))

end VG.Proof.Rc2.Arm

end

/-! # Key-expansion control and register setup -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Proof.Rc2.Word32

theorem cmp128_ok (s : State) :
    ∃ s', runBlock isa [.cmp .r0 (.imm 128)] s = some s' ∧
      zeroFlag s' = some ((s.gpr .r0 - 128) == 0) ∧ Keep [] s s' := by
  refine ⟨subFlags s (s.gpr .r0) 128, ?_, ?_⟩
  · simp (config := {decide := true}) only [runBlock_cons, exec, Op2.eval, Option.map_some,
      ite_true, runStep_some, runBlock_nil]
  constructor
  · rfl
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem maybeFill_ok (s : State) (key : List Byte) (ht : 1 ≤ key.length) (ht' : key.length ≤ 128)
    (outFit : (s.gpr .r6).toNat + 128 ≤ 2 ^ 32)
    (len : s.gpr .r5 = BitVec.ofNat 32 key.length) (start : s.gpr .r0 = BitVec.ofNat 32 key.length)
    (writable : ∀ i < 128, InRegions s.wr (State.addr (s.gpr .r6) + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (State.addr (s.gpr .r6)) (fill key 0) key.length) :
    WP isa (.seq (.block [.cmp .r0 (.imm 128)])
      (.ite .ne (.loop (.block fillKey) .ne) (.block []))) s (fun s' =>
        s'.gpr .r0 = 128 ∧ KeyFrame s s' ∧
        BytesPrefix s'.mem (State.addr (s.gpr .r6)) (fill key (128 - key.length)) 128) := by
  apply WP.seq
  obtain ⟨s₁, run₁, flag₁, keep₁⟩ := cmp128_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have frame₁ := (KeyFrame.refl s).keep (keep₁.weaken (by simp [keyTemps]))
  have flag : zeroFlag s₁ = some (decide (key.length = 128)) := by
    rw [flag₁, start]
    exact congrArg some (counter_eq _ _ (by omega) (by decide))
  have ptr₁ := keep₁.reg .r6 (by simp)
  by_cases he : key.length = 128
  · apply WP.ite false (by simp only [eval_nonzero, flag, he, decide_true, Option.map_some, Bool.not_true])
    · simp
    · intro _
      apply WP.block_nil
      refine ⟨?_, frame₁, ?_⟩
      · rw [keep₁.reg .r0 (by simp), start, he]; rfl
      · rw [keep₁.mem]
        simpa only [he, Nat.sub_self] using initialPrefix
  · apply WP.ite true (by simp only [eval_nonzero, flag, he, decide_false, Option.map_some, Bool.not_false])
    · intro _
      have writes : ∀ i < 128, InRegions s₁.wr (State.addr (s₁.gpr .r6) + BitVec.ofNat 64 i) 1 := by
        rw [keep₁.wr, ptr₁]; exact writable
      have initial : BytesPrefix s₁.mem (State.addr (s₁.gpr .r6)) (fill key 0) key.length := by
        rw [keep₁.mem, ptr₁]; exact initialPrefix
      apply WP.mono (fillLoop_ok s₁ key ht (by omega) (by rw [ptr₁]; exact outFit)
        ((keep₁.reg .r5 (by simp)).trans len) ((keep₁.reg .r0 (by simp)).trans start) writes initial)
      intro s₂ h₂
      exact ⟨h₂.1, frame₁.trans h₂.2.1, by rw [ptr₁] at h₂; exact h₂.2.2⟩
    · simp

theorem setReduction_ok (s : State) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (input : s.gpr .r7 = BitVec.ofNat 32 bits) :
    ∃ s', runBlock isa reduceSetup s = some s' ∧
      s'.gpr .r1 = BitVec.ofNat 32 ((bits + 7) / 8) ∧
      s'.gpr .r0 = BitVec.ofNat 32 (128 - (bits + 7) / 8) ∧ Keep [.r1, .r0] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [reduceSetup, imm, runBlock_cons, runStep_some, runBlock_nil,
      exec, Op2.eval, Option.map_some,
      gpr_setReg, ite_true, ite_false]
    rfl, ?_⟩
  have t8 : (s.gpr .r7 + 7#32) >>> 3 = BitVec.ofNat 32 ((bits + 7) / 8) := by
    rw [input]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
    exact t8
  · simp only [gpr_setReg, reduceCtorEq, ite_true, ite_false]
    change 128#32 - (s.gpr .r7 + 7#32) >>> 3 = _
    rw [t8]
    exact Offset.ofNat_sub_ofNat (by omega)
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, hr.1, hr.2, ite_false]
    · simp only [mem_setReg]
    · simp only [rd_setReg]
    · simp only [wr_setReg]

theorem maybeDescend_ok (s : State) (l : KeyBytes) (t8 : Nat) (ht : 1 ≤ t8) (ht' : t8 ≤ 128)
    (outFit : (s.gpr .r6).toNat + 128 ≤ 2 ^ 32)
    (len : s.gpr .r1 = BitVec.ofNat 32 t8) (start : s.gpr .r0 = BitVec.ofNat 32 (128 - t8))
    (writable : ∀ i < 128, InRegions s.wr (State.addr (s.gpr .r6) + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (State.addr (s.gpr .r6)) l 128) :
    WP isa (.seq (.block [.cmp .r0 (.imm 0)])
      (.ite .ne (.loop (.block descendKey) .ne) (.block []))) s (fun s' =>
        KeyFrame s s' ∧ BytesPrefix s'.mem (State.addr (s.gpr .r6)) (descend l t8 (128 - t8)) 128) := by
  apply WP.seq
  obtain ⟨s₁, run₁, flag₁, keep₁⟩ := cmpZero_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have frame₁ := (KeyFrame.refl s).keep (keep₁.weaken (by simp [keyTemps]))
  have flag : zeroFlag s₁ = some (decide (t8 = 128)) := by
    rw [flag₁, start]
    have eqZero := counter_eq (128 - t8) 0 (by omega) (by decide)
    simp only [BitVec.sub_zero] at eqZero
    change some (BitVec.ofNat 32 (128 - t8) == 0#32) = _
    rw [eqZero]
    have he : 128 - t8 = 0 ↔ t8 = 128 := by omega
    simp only [he]
  have ptr₁ := keep₁.reg .r6 (by simp)
  by_cases he : t8 = 128
  · apply WP.ite false (by simp only [eval_nonzero, flag, he, decide_true, Option.map_some, Bool.not_true])
    · simp
    · intro _
      apply WP.block_nil
      refine ⟨frame₁, ?_⟩
      rw [keep₁.mem, he]
      exact initialPrefix
  · apply WP.ite true (by simp only [eval_nonzero, flag, he, decide_false, Option.map_some, Bool.not_false])
    · intro _
      have writes : ∀ i < 128, InRegions s₁.wr (State.addr (s₁.gpr .r6) + BitVec.ofNat 64 i) 1 := by
        rw [keep₁.wr, ptr₁]; exact writable
      have initial : BytesPrefix s₁.mem (State.addr (s₁.gpr .r6)) l 128 := by
        rw [keep₁.mem, ptr₁]; exact initialPrefix
      apply WP.mono (descendLoop_ok s₁ l t8 ht (by omega) (by rw [ptr₁]; exact outFit)
        ((keep₁.reg .r1 (by simp)).trans len) ((keep₁.reg .r0 (by simp)).trans start) writes initial)
      intro s₂ h₂
      exact ⟨frame₁.trans h₂.2.1, by rw [ptr₁] at h₂; exact h₂.2.2⟩
    · simp

end VG.Proof.Rc2.Arm

end

section

/-! # Composing the RC2 key-expansion stages -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Impl.Rc2.Arm

def coreRegs : List Reg := [.r8, .r6]

structure CoreFrame (s₀ s : State) : Prop where
  reg : ∀ r ∈ coreRegs, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Frame [⟨State.addr (s₀.gpr .r6), 128⟩] s₀.mem s.mem

theorem CoreFrame.of_keep {s s' : State} {rs : List Reg} (keep : Keep rs s s')
    (sep : ∀ r ∈ coreRegs, r ∉ rs) : CoreFrame s s' := by
  refine ⟨fun r hr => keep.reg r (sep r hr), keep.rd, keep.wr, ?_⟩
  rw [keep.mem]; exact Frame.refl _ _

theorem CoreFrame.of_key {s s' : State} (h : KeyFrame s s') : CoreFrame s s' := by
  have sep : ∀ r ∈ coreRegs, r ∉ keyTemps := by decide
  exact ⟨fun r hr => h.reg r (sep r hr), h.rd, h.wr, h.mem⟩

theorem CoreFrame.trans {s₀ s₁ s₂ : State} (h₁ : CoreFrame s₀ s₁) (h₂ : CoreFrame s₁ s₂) :
    CoreFrame s₀ s₂ := by
  refine ⟨fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, ?_⟩
  have frame₂ := h₂.mem
  rw [h₁.reg .r6 (by decide)] at frame₂
  exact h₁.mem.trans frame₂

theorem expandCopyFill_ok (s : State) (t : Nat) (ht : 1 ≤ t) (ht' : t ≤ 128)
    (keyFit : (s.gpr .r4).toNat + t ≤ 2 ^ 32)
    (outFit : (s.gpr .r6).toNat + 128 ≤ 2 ^ 32)
    (len : s.gpr .r5 = BitVec.ofNat 32 t) (zero : s.gpr .r0 = 0)
    (readable : ∀ i < t, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r4) + BitVec.ofNat 64 i) 1)
    (writable : ∀ i < 128, InRegions s.wr (State.addr (s.gpr .r6) + BitVec.ofNat 64 i) 1)
    (sep : (Region.mk (State.addr (s.gpr .r4)) t).Disjoint ⟨State.addr (s.gpr .r6), 128⟩) :
    WP isa expandCopyFill s (fun s' => KeyFrame s s' ∧
      BytesPrefix s'.mem (State.addr (s.gpr .r6)) (fill (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r4)) t) (128 - t)) 128) := by
  rw [expandCopyFill]
  apply WP.seq
  apply WP.mono (copyLoop_ok s t ht ht' keyFit outFit len zero readable writable sep)
  intro s₁ h₁
  have length : (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r4)) t).length = t := by
    simp [Spec.Rc2.bytesAt]
  have ptr₁ := h₁.2.1.reg .r6 (by decide)
  have writes : ∀ i < 128, InRegions s₁.wr (State.addr (s₁.gpr .r6) + BitVec.ofNat 64 i) 1 := by
    rw [h₁.2.1.wr, ptr₁]; exact writable
  apply WP.mono (maybeFill_ok s₁ (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r4)) t)
    (by rw [length]; exact ht) (by rw [length]; exact ht') (by rw [ptr₁]; exact outFit)
    (by rw [length]; exact (h₁.2.1.reg .r5 (by decide)).trans len)
    (by rw [length]; exact h₁.1) writes (by rw [ptr₁, length]; exact h₁.2.2))
  intro s₂ h₂
  exact ⟨h₁.2.1.trans h₂.2.1, by rw [length, ptr₁] at h₂; exact h₂.2.2⟩

theorem reduceDescend_ok (s : State) (l : KeyBytes) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (outFit : (s.gpr .r6).toNat + 128 ≤ 2 ^ 32)
    (len : s.gpr .r1 = BitVec.ofNat 32 ((bits + 7) / 8))
    (index : s.gpr .r0 = BitVec.ofNat 32 (128 - (bits + 7) / 8))
    (mask : (s.gpr .r2).setWidth 8 = BitVec.ofNat 8 (255 % 2 ^ (8 + bits - 8 * ((bits + 7) / 8))))
    (writable : ∀ i < 128, InRegions s.wr (State.addr (s.gpr .r6) + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (State.addr (s.gpr .r6)) l 128) :
    WP isa (.seq (.block reduceKey) (.seq (.block [.cmp .r0 (.imm 0)])
      (.ite .ne (.loop (.block descendKey) .ne) (.block [])))) s (fun s' =>
        KeyFrame s s' ∧ BytesPrefix s'.mem (State.addr (s.gpr .r6))
          (descend (reduce l bits) ((bits + 7) / 8) (128 - (bits + 7) / 8)) 128) := by
  have bound : 1 ≤ (bits + 7) / 8 ∧ (bits + 7) / 8 ≤ 128 := by omega
  have writes : InRegions s.wr (State.addr (s.gpr .r6 + s.gpr .r0)) 1 := by
    rw [index, addr_add (by omega)]; exact writable _ (by omega)
  have reads : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r6 + s.gpr .r0)) 1 := by
    obtain ⟨r, hr, hc⟩ := writes
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.seq
  apply WP.mono (reduceKey_ok s reads writes)
  intro s₁ h₁
  have keep₁ := h₁.2
  rw [index, addr_add (by omega), initialPrefix _ (by omega), mask] at keep₁
  have frame₁ := (KeyFrame.refl s).step _ (by omega) _ keep₁
  have ptr₁ := keep₁.reg .r6 (by decide)
  have prefix₁ : BytesPrefix s₁.mem (State.addr (s.gpr .r6)) (reduce l bits) 128 := by
    rw [keep₁.mem]
    exact initialPrefix.write (by decide) (by omega) _
  have write₁ : ∀ i < 128, InRegions s₁.wr (State.addr (s₁.gpr .r6) + BitVec.ofNat 64 i) 1 := by
    rw [keep₁.wr, ptr₁]; exact writable
  apply WP.mono (maybeDescend_ok s₁ (reduce l bits) ((bits + 7) / 8) bound.1 bound.2 (by rw [ptr₁]; exact outFit)
    ((keep₁.reg .r1 (by decide)).trans len) (h₁.1.trans index) write₁
    (by rw [ptr₁]; exact prefix₁))
  intro s₂ h₂
  exact ⟨frame₁.trans h₂.1, by rw [ptr₁] at h₂; exact h₂.2⟩

theorem expandReduce_ok (s : State) (l : KeyBytes) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (outFit : (s.gpr .r6).toNat + 128 ≤ 2 ^ 32)
    (input : s.gpr .r7 = BitVec.ofNat 32 bits)
    (writable : ∀ i < 128, InRegions s.wr (State.addr (s.gpr .r6) + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (State.addr (s.gpr .r6)) l 128) :
    WP isa expandReduce s (fun s' => CoreFrame s s' ∧ BytesPrefix s'.mem (State.addr (s.gpr .r6))
      (descend (reduce l bits) ((bits + 7) / 8) (128 - (bits + 7) / 8)) 128) := by
  rw [expandReduce]
  apply WP.seq
  obtain ⟨s₁, run₁, len₁, index₁, keep₁⟩ := setReduction_ok s bits hb hb' input
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  apply WP.seq
  apply WP.mono (maskCode_ok s₁ bits hb hb' ((keep₁.reg .r7 (by decide)).trans input))
  intro s₂ h₂
  have frame := (CoreFrame.of_keep keep₁ (by decide)).trans (CoreFrame.of_keep h₂.2 (by decide))
  have ptr₂ := frame.reg .r6 (by decide)
  have writes : ∀ i < 128, InRegions s₂.wr (State.addr (s₂.gpr .r6) + BitVec.ofNat 64 i) 1 := by
    rw [frame.wr, ptr₂]; exact writable
  apply WP.mono (reduceDescend_ok s₂ l bits hb hb' (by rw [ptr₂]; exact outFit)
    ((h₂.2.reg .r1 (by decide)).trans len₁) ((h₂.2.reg .r0 (by decide)).trans index₁) h₂.1 writes
    (by rw [ptr₂, h₂.2.mem, keep₁.mem]; exact initialPrefix))
  intro s₃ h₃
  exact ⟨frame.trans (CoreFrame.of_key h₃.1), by rw [ptr₂] at h₃; exact h₃.2⟩

end VG.Proof.Rc2.Arm

end

/-! # Register setup and scratch saves for key expansion -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Proof.Rc2.Word32

theorem keySave_eq : save .r12 0 = (slotsOf saved).map (fun p => Instr.str p.1 .r12 p.2) := by rfl

theorem keyRestore_eq : restore .r12 0 = (slotsOf saved).map (fun p => Instr.ldr p.1 .r12 p.2) := by rfl

theorem keySlots_ok : Spill.Slots 0 36 (slotsOf saved) := by decide

theorem pinKey_ok (s : State) :
    ∃ s', runBlock isa [rr .r8 .r12, rr .r4 .r0, rr .r5 .r1, rr .r6 .r3, rr .r7 .r2, imm .r0 0] s = some s' ∧
      s'.gpr .r8 = s.gpr .r12 ∧ s'.gpr .r4 = s.gpr .r0 ∧ s'.gpr .r5 = s.gpr .r1 ∧
      s'.gpr .r6 = s.gpr .r3 ∧ s'.gpr .r7 = s.gpr .r2 ∧ s'.gpr .r0 = 0 ∧ Keep [.r8, .r4, .r5, .r6, .r7, .r0] s s' := by
  refine ⟨_, by
    simp only [rr, imm, runBlock_cons, exec]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · exact gpr_setReg_self _ _ _
  · constructor
    · intro r hr
      have sep : r ≠ .r8 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r0 := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using hr
      simp only [gpr_setReg, sep.1, sep.2.1, sep.2.2.1, sep.2.2.2.1,
        sep.2.2.2.2.1, sep.2.2.2.2.2, ite_false]
    · rfl
    · rfl
    · rfl

theorem loadScratch_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 4) :
    ∃ s', runBlock isa [.ldrSp .r12 0] s = some s' ∧
      s'.gpr .r12 = stackArg s 0 ∧ Keep [.r12] s s' := by
  have rd : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4 := by
    simpa only [stackArgAddr, Nat.mul_zero, BitVec.add_zero] using readable
  refine ⟨s.setReg .r12 (stackArg s 0), ?_, ?_⟩
  · simp only [↓reduceIte, Nat.reduceLT, runBlock_cons, exec,
      State.load32, rd, BitVec.add_zero,
      Option.map_some, runStep_some, runBlock_nil, stackArg, stackArgAddr, Nat.mul_zero]
  · exact ⟨rfl, fun r hr => gpr_setReg_of_ne _ _ (by simpa using hr), rfl, rfl, rfl⟩

theorem scratchBase_ok (s : State) :
    ∃ s', runBlock isa [rr .r12 .r8] s = some s' ∧
      s'.gpr .r12 = s.gpr .r8 ∧ Keep [.r12] s s' := by
  refine ⟨s.setReg .r12 (s.gpr .r8), rfl, rfl, ?_⟩
  exact ⟨fun r hr => gpr_setReg_of_ne _ _ (by simpa using hr), rfl, rfl, rfl⟩

theorem bytesAt_frame {m m' : Mem} {p : Addr} {n : Nat} {rs : List Region}
    (frame : Frame rs m m') (sep : ∀ r ∈ rs, (Region.mk p n).Disjoint r) (bound : n ≤ 2 ^ 64) :
    Spec.Rc2.bytesAt m' p n = Spec.Rc2.bytesAt m p n := by
  unfold Spec.Rc2.bytesAt
  apply List.map_congr_left
  intro i hi
  exact frame.bytes sep bound (List.mem_range.mp hi)

end VG.Proof.Rc2.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.Arm.Key`. -/
section

/-! # Verified RC2 key expansion -/

namespace VG.Proof.Rc2.Arm

open VG VG.Arm VG.Impl.Rc2.Arm

def keyContract : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let out : Region := ⟨State.addr (s.gpr .r3), 128⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 512⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [key, args] ∧ s.wr = [out, scratch] ∧ key.Disjoint out ∧ key.Disjoint scratch ∧
      out.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 128 ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + 512 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32 ∧
      Spec.Rc2.validKey (s.gpr .r1).toNat (s.gpr .r2).toNat
  post s s' := Spec.Rc2.scheduleAt s'.mem (State.addr (s.gpr .r3)) =
    Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) (s.gpr .r2).toNat
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

theorem key_body_correct (s : State) (hs : keyContract.pre s) :
    WP isa expandKey s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ keyContract.post s s') := by
  obtain ⟨hrd, hwr, keyOut, keyScratch, outScratch, _argsOut, _argsScratch, keyFit, outFit, scratchFit, _spFit, ht, ht', hb, hb'⟩ := hs
  rw [expandKey]
  apply WP.seq
  obtain ⟨s₀, run₀, scratch₀, keep₀⟩ := loadScratch_ok s (by
    rw [hrd, hwr]
    exact ⟨⟨stackArgAddr s 0, 4⟩, by simp, Region.contains_self _ _⟩)
  refine WP.of_runBlock ⟨s₀, run₀, ?_⟩
  have gpr₀ (r : Reg) (hr : r ≠ .r12) : s₀.gpr r = s.gpr r := keep₀.reg r (by simpa using hr)
  apply WP.seq
  rw [WP.block_append_iff, keySave_eq]
  apply WP.mono (Spill.save_block_ok keySlots_ok (by rw [scratch₀]; omega) fun d _ hd => by
    rw [keep₀.wr, scratch₀, hwr]
    exact ⟨⟨State.addr (stackArg s 0), 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩)
  intro s₁ h₁
  obtain ⟨s₂, run₂, r8₂, key₂, len₂, ptr₂, bits₂, zero₂, keep₂⟩ := pinKey_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [h₁.1, scratch₀] at r8₂
  rw [h₁.1, gpr₀ .r0 (by decide)] at key₂
  rw [h₁.1, gpr₀ .r1 (by decide)] at len₂
  rw [h₁.1, gpr₀ .r3 (by decide)] at ptr₂
  rw [h₁.1, gpr₀ .r2 (by decide)] at bits₂
  have scratchFrame : Frame [⟨State.addr (stackArg s 0), 512⟩] s.mem s₂.mem := by
    rw [keep₂.mem, h₁.2.2.2, keep₀.mem, scratch₀]
    exact Spill.saveMem_frame _ _ _ (by decide) _ (by decide)
  have rd₂ : s₂.rd = s.rd := keep₂.rd.trans (h₁.2.1.trans keep₀.rd)
  have wr₂ : s₂.wr = s.wr := keep₂.wr.trans (h₁.2.2.1.trans keep₀.wr)
  have source₂ : Spec.Rc2.bytesAt s₂.mem (State.addr (s₂.gpr .r4)) (s.gpr .r1).toNat =
      Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat := by
    rw [key₂]
    exact VG.Proof.Rc2.Arm.bytesAt_frame scratchFrame (by simpa using keyScratch) (by omega)
  have read₂ : ∀ i < (s.gpr .r1).toNat,
      InRegions (s₂.rd ++ s₂.wr) (State.addr (s₂.gpr .r4) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [rd₂, wr₂, key₂, hrd, hwr]
    exact ⟨⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, by simp,
      Offset.contains_base _ (by omega) (by omega)⟩
  have write₂ : ∀ i < 128, InRegions s₂.wr (State.addr (s₂.gpr .r6) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [wr₂, ptr₂, hwr]
    exact ⟨⟨State.addr (s.gpr .r3), 128⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  apply WP.seq
  apply WP.mono (expandCopyFill_ok s₂ (s.gpr .r1).toNat ht ht' (by rw [key₂]; exact keyFit) (by rw [ptr₂]; exact outFit)
    (by simpa using len₂) zero₂ read₂ write₂ (by rw [key₂, ptr₂]; exact keyOut))
  intro s₃ h₃
  apply WP.seq
  have write₃ : ∀ i < 128, InRegions s₃.wr (State.addr (s₃.gpr .r6) + BitVec.ofNat 64 i) 1 := by
    rw [h₃.1.wr, h₃.1.reg .r6 (by decide)]; exact write₂
  apply WP.mono (expandReduce_ok s₃ _ (s.gpr .r2).toNat hb hb' (by rw [h₃.1.reg .r6 (by decide), ptr₂]; exact outFit)
    (by simpa using (h₃.1.reg .r7 (by decide)).trans bits₂) write₃
    (by rw [h₃.1.reg .r6 (by decide)]; exact h₃.2))
  intro s₄ h₄
  have core := (CoreFrame.of_key h₃.1).trans h₄.1
  have outFrame : Frame [⟨State.addr (s.gpr .r3), 128⟩] s₂.mem s₄.mem := by
    have h := core.mem
    rw [ptr₂] at h; exact h
  have r8₄ : s₄.gpr .r8 = stackArg s 0 := (core.reg .r8 (by decide)).trans r8₂
  have rd₄ := core.rd.trans rd₂
  have wr₄ := core.wr.trans wr₂
  have expanded : BytesPrefix s₄.mem (State.addr (s.gpr .r3))
      (Spec.Rc2.expandBytes (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) (s.gpr .r2).toNat) 128 := by
    have h := h₄.2
    rw [h₃.1.reg .r6 (by decide), ptr₂, source₂] at h
    rw [expandBytes_eq]
    have length : (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat).length = (s.gpr .r1).toNat := by
      simp [Spec.Rc2.bytesAt]
    rw [length]; exact h
  rw [WP.block_append_iff]
  obtain ⟨s₅, run₅, base₅, keep₅⟩ := scratchBase_ok s₄
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  rw [r8₄] at base₅
  have rd₅ := keep₅.rd.trans rd₄
  have wr₅ := keep₅.wr.trans wr₄
  have stored : Spill.Saved s₅.mem (State.addr (s₅.gpr .r12)) s.gpr (slotsOf saved) := by
    intro p hp
    have bound := keySlots_ok.bound hp
    rw [keep₅.mem, base₅, outFrame.readW (r := ⟨State.addr (stackArg s 0), 512⟩)
      (Offset.contains_base _ (by omega) (by omega)) (by simpa using outScratch.symm) (by decide),
      keep₂.mem, h₁.2.2.2, scratch₀, Spill.saveMem_saved _ _ _ _ keySlots_ok p hp]
    have sep : ∀ p ∈ slotsOf saved, p.1 ≠ .r12 := by decide
    exact gpr₀ _ (sep p hp)
  rw [keyRestore_eq]
  apply WP.mono (Spill.restore_block_ok keySlots_ok (by decide) (by rw [base₅]; omega)
    (fun d _ hd => by
      rw [rd₅, wr₅, base₅, hrd, hwr]
      exact ⟨⟨State.addr (stackArg s 0), 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩) stored)
  intro s₆ h₆
  constructor
  · exact Spill.restored_of h₆.1 (by decide)
  · change Spec.Rc2.scheduleAt s₆.mem (State.addr (s.gpr .r3)) = _
    rw [h₆.2.2.1, keep₅.mem]
    exact scheduleAt_expanded expanded

def keySatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 1 | .r2 => 8 | .r3 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x4001 then 0x30 else 0
  rd := [⟨0x1000, 1⟩, ⟨0x4000, 4⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 512⟩]

theorem key_correct (s : State) (hs : keyContract.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ keyContract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := key_body_correct s hs
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

def keyTaint : VG.Arm.Taint.T := { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, argLen := 4 }

theorem keyTaint_wf {s : State} (h : keyContract.pre s) : VG.Arm.Taint.Wf keyTaint s := by
  obtain ⟨_, wr, _, _, _, ao, asc, _, _, _, spfit, _⟩ := h
  refine ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨spfit, ?_⟩, fun _ h => (List.not_mem_nil h).elim⟩
  have addr : State.addr s.sp = stackArgAddr s 0 := by simp [stackArgAddr]
  simp only [keyTaint, addr, wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact ao
  · exact asc

theorem keyTaint_agree {s₁ s₂ : State} (h₁ : keyContract.pre s₁) (h₂ : keyContract.pre s₂)
    (hp : keyContract.pub s₁ s₂) : VG.Arm.Taint.Agree keyTaint s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, a0⟩ := hp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h,
    keyTaint_wf h₁, keyTaint_wf h₂, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => psp, fun k hk => ?_⟩
  · simp only [keyTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · have argByte_eq (s : State) : Taint.argByte s k = stackArgAddr s 0 + BitVec.ofNat 64 k := by
      simp [Taint.argByte, stackArgAddr]
    simp only [keyTaint] at hk
    rw [argByte_eq, argByte_eq, Mem.readW_byte s₁.mem _ hk, Mem.readW_byte s₂.mem _ hk]
    exact congrArg _ a0

theorem expandKey_constantTime : ConstantTime isa keyContract.pre keyContract.pub expandKey := by
  exact VG.Taint.constantTime (A := taint) keyTaint (fun _ _ h₁ h₂ hp => keyTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem key_verified : Verified target expandKey (Spec.Rc2.expandKeyContract abi) := by
  refine Verified.of_correct key_correct expandKey_constantTime ?_
  sig_implies [Spec.Rc2.expandKeyContract, Spec.Rc2.expandKeySig, abi, argRegs,
    Arm.reduceClassify, Arm.Loc.val, State.addr, keyContract, Spec.Rc2.validKey]
    [keySatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using keySatState

end VG.Proof.Rc2.Arm

end
