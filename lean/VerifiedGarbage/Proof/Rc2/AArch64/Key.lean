import VerifiedGarbage.Impl.Rc2.AArch64.ExpandKey
import VerifiedGarbage.Proof.Rc2.AArch64.Block
import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc2.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.FillKey`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.KeySteps`. -/
section

/-! # Individual AArch64 RC2 key-expansion steps -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc2.AArch64

def keyTemps : List Reg := [.x8, .x23, .x3, .x5, .x6, .x7, .x9, .x10]

/-- The public comparison register represents the loop's zero test. -/
def zeroFlag (s : State) : Option Bool := some (s.gpr .x10 == 0)

theorem eval_zero (s : State) : eval (.zero .x .x10) s = VG.Proof.Rc2.AArch64.zeroFlag s := rfl

theorem eval_nonzero (s : State) :
    eval (.nonzero .x .x10) s = (VG.Proof.Rc2.AArch64.zeroFlag s).map (!·) := rfl

theorem copyKey_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .x19 + s.gpr .x23) 1)
    (writable : InRegions s.wr (s.gpr .x21 + s.gpr .x23) 1) :
    ∃ s', runBlock isa copyKey s = some s' ∧
      s'.gpr .x23 = s.gpr .x23 + 1 ∧
      VG.Proof.Rc2.AArch64.zeroFlag s' = some ((s.gpr .x23 + 1 - s.gpr .x20) == 0) ∧
      Keep VG.Proof.Rc2.AArch64.keyTemps
        {s with mem := s.mem.writeW (s.gpr .x21 + s.gpr .x23) (s.mem (s.gpr .x19 + s.gpr .x23))} s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [copyKey, runBlock_cons, runStep_some,
      runBlock_nil, exec, State.read, State.load, State.store, addr, readByte,
      BitVec.add_zero, Option.map_some, Option.bind_some, gpr_write, BitVec.setWidth_eq,
      mem_write, rd_write, wr_write, readable, writable, ite_true, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_false, ite_true]
    rfl
  · simp only [VG.Proof.Rc2.AArch64.zeroFlag, gpr_write_self, BitVec.setWidth_eq]
    rfl
  · constructor
    · intro r hr
      have h8 : r ≠ .x8 := by intro h; subst r; exact hr (by decide)
      have h23 : r ≠ .x23 := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .x9 := by intro h; subst r; exact hr (by decide)
      have h10 : r ≠ .x10 := by intro h; subst r; exact hr (by decide)
      simp only [gpr_write, BitVec.setWidth_eq, h8, h23, h9, h10, ite_false]
    · simp only [mem_write, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide),
        BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide), BitVec.setWidth_eq]
      rfl
    · rfl
    · rfl

theorem fillInput_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (s.gpr .x21 + s.gpr .x23 - 1#64) 1)
    (readHi : InRegions (s.rd ++ s.wr) (s.gpr .x21 + (s.gpr .x23 - s.gpr .x20)) 1) :
    ∃ s', runBlock isa fillInput s = some s' ∧
      s'.gpr .x8 = (s.mem (s.gpr .x21 + s.gpr .x23 - 1#64)).setWidth 64 +
        (s.mem (s.gpr .x21 + (s.gpr .x23 - s.gpr .x20))).setWidth 64 ∧
      Keep [.x8, .x3, .x5, .x9] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [fillInput, runBlock_cons, runStep_some,
      runBlock_nil, exec, State.read, State.load, addr, readByte,
      BitVec.add_zero, Option.map_some, Option.bind_some, gpr_write, BitVec.setWidth_eq,
      mem_write, rd_write, wr_write, readLo, readHi, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_write_self, BitVec.setWidth_eq,
      BitVec.setWidth_setWidth (by decide : ¬(32 < 8 ∧ 32 < 64))]
  · constructor
    · intro r hr
      have h8 : r ≠ .x8 := by intro h; subst r; exact hr (by decide)
      have h3 : r ≠ .x3 := by intro h; subst r; exact hr (by decide)
      have h5 : r ≠ .x5 := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .x9 := by intro h; subst r; exact hr (by decide)
      simp only [gpr_write, BitVec.setWidth_eq, h8, h3, h5, h9, ite_false]
    · rfl
    · rfl
    · rfl

theorem fillOutput_ok (s : State)
    (writable : InRegions s.wr (s.gpr .x21 + s.gpr .x23) 1) :
    ∃ s', runBlock isa fillFinish s = some s' ∧
      s'.gpr .x23 = s.gpr .x23 + 1 ∧
      VG.Proof.Rc2.AArch64.zeroFlag s' = some ((s.gpr .x23 + 1 - 128) == 0) ∧
      Keep VG.Proof.Rc2.AArch64.keyTemps {s with mem := s.mem.writeW (s.gpr .x21 + s.gpr .x23) ((s.gpr .x8).setWidth 8)} s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [fillFinish, storeKey, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
      runBlock_nil, exec, State.read, State.store, addr,
      BitVec.add_zero, Option.bind_some, gpr_write, BitVec.setWidth_eq,
      mem_write, rd_write, wr_write, writable, ite_true, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]
    rfl
  · simp only [VG.Proof.Rc2.AArch64.zeroFlag, gpr_write_self, BitVec.setWidth_eq]
    rfl
  · constructor
    · intro r hr
      have h23 : r ≠ .x23 := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .x9 := by intro h; subst r; exact hr (by decide)
      have h10 : r ≠ .x10 := by intro h; subst r; exact hr (by decide)
      simp only [gpr_write, BitVec.setWidth_eq, h23, h9, h10, ite_false]
    · simp only [mem_write, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide)]
      rfl
    · rfl
    · rfl

theorem reduceInput_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .x21 + s.gpr .x23) 1) :
    ∃ s', runBlock isa reduceInput s = some s' ∧
      s'.gpr .x8 = (s.mem (s.gpr .x21 + s.gpr .x23)).setWidth 64 &&& s.gpr .x2 ∧
      Keep [.x8, .x9] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [reduceInput, runBlock_cons, runStep_some,
      runBlock_nil, exec, State.read, State.load, addr, readByte,
      BitVec.add_zero, Option.map_some, Option.bind_some, gpr_write, BitVec.setWidth_eq,
      mem_write, rd_write, wr_write, readable, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_write_self, BitVec.setWidth_eq,
      BitVec.setWidth_setWidth (by decide : ¬(32 < 8 ∧ 32 < 64))]
  · constructor
    · intro r hr
      have h8 : r ≠ .x8 := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .x9 := by intro h; subst r; exact hr (by decide)
      simp only [gpr_write, BitVec.setWidth_eq, h8, h9, ite_false]
    · rfl
    · rfl
    · rfl

theorem storeByte_ok (s : State)
    (writable : InRegions s.wr (s.gpr .x21 + s.gpr .x23) 1) :
    ∃ s', runBlock isa storeKey s = some s' ∧ s'.gpr .x23 = s.gpr .x23 ∧
      Keep [.x9] {s with mem := s.mem.writeW (s.gpr .x21 + s.gpr .x23) ((s.gpr .x8).setWidth 8)} s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [storeKey, runBlock_cons, runStep_some,
      runBlock_nil, exec, State.read, State.store, addr,
      BitVec.add_zero, Option.bind_some, gpr_write, BitVec.setWidth_eq,
      mem_write, rd_write, wr_write, writable, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · rfl
  · constructor
    · intro r hr
      have h9 : r ≠ .x9 := by intro h; subst r; exact hr (by decide)
      simp only [gpr_write, BitVec.setWidth_eq, h9, ite_false]
    · simp only [BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide)]
      rfl
    · rfl
    · rfl

theorem descendInput_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (s.gpr .x21 + (s.gpr .x23 - 1#64) + 1#64) 1)
    (readHi : InRegions (s.rd ++ s.wr) (s.gpr .x21 + (s.gpr .x23 - 1#64 + s.gpr .x24)) 1) :
    ∃ s', runBlock isa descendInput s = some s' ∧
      s'.gpr .x23 = s.gpr .x23 - 1 ∧
      s'.gpr .x8 = (s.mem (s.gpr .x21 + (s.gpr .x23 - 1#64) + 1#64)).setWidth 64 ^^^
        (s.mem (s.gpr .x21 + (s.gpr .x23 - 1#64 + s.gpr .x24))).setWidth 64 ∧
      Keep [.x8, .x23, .x3, .x5, .x9] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [descendInput, runBlock_cons, runStep_some,
      runBlock_nil, exec, State.read, State.load, addr, readByte,
      BitVec.add_zero, Option.map_some, Option.bind_some, gpr_write, BitVec.setWidth_eq,
      mem_write, rd_write, wr_write, readLo, readHi, ite_true, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]
    rfl
  · simp only [gpr_write_self, BitVec.setWidth_eq,
      BitVec.setWidth_setWidth (by decide : ¬(32 < 8 ∧ 32 < 64))]
  · constructor
    · intro r hr
      have h8 : r ≠ .x8 := by intro h; subst r; exact hr (by decide)
      have h23 : r ≠ .x23 := by intro h; subst r; exact hr (by decide)
      have h3 : r ≠ .x3 := by intro h; subst r; exact hr (by decide)
      have h5 : r ≠ .x5 := by intro h; subst r; exact hr (by decide)
      have h9 : r ≠ .x9 := by intro h; subst r; exact hr (by decide)
      simp only [gpr_write, BitVec.setWidth_eq, h8, h23, h3, h5, h9, ite_false]
    · rfl
    · rfl
    · rfl

theorem cmpZero_ok (s : State) :
    ∃ s', runBlock isa [rr .x10 .x23] s = some s' ∧
      VG.Proof.Rc2.AArch64.zeroFlag s' = some (s.gpr .x23 == 0) ∧ Keep [.x10] s s' := by
  refine ⟨s.write .x .x10 (s.gpr .x23), ?_, ?_⟩
  · simp only [rr, runBlock_cons, exec, show 0 < 4096 by decide, ite_true,
      State.read, BitVec.setWidth_eq, BitVec.add_zero, runStep_some, runBlock_nil]
  constructor
  · rfl
  · exact ⟨fun r hr => gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl⟩

end VG.Proof.Rc2.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.KeyCompose`. -/
section

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.Impl.Rc2.AArch64

theorem fillKey_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (s.gpr .x21 + s.gpr .x23 - 1#64) 1)
    (readHi : InRegions (s.rd ++ s.wr) (s.gpr .x21 + (s.gpr .x23 - s.gpr .x20)) 1)
    (writable : InRegions s.wr (s.gpr .x21 + s.gpr .x23) 1) :
    WP isa (.block fillKey) s (fun s' =>
      s'.gpr .x23 = s.gpr .x23 + 1 ∧
      VG.Proof.Rc2.AArch64.zeroFlag s' = some ((s.gpr .x23 + 1 - 128) == 0) ∧
      Keep VG.Proof.Rc2.AArch64.keyTemps {s with
        mem := s.mem.writeW (s.gpr .x21 + s.gpr .x23)
          (Spec.Rc2.pi (s.mem (s.gpr .x21 + s.gpr .x23 - 1#64) +
          s.mem (s.gpr .x21 + (s.gpr .x23 - s.gpr .x20))))} s') := by
  rw [fillKey, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := VG.Proof.Rc2.AArch64.fillInput_ok s readLo readHi
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  apply WP.mono (piLookup_ok s₁)
  intro s₂ h₂
  have k₁ : Keep VG.Proof.Rc2.AArch64.keyTemps s s₁ := keep₁.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h <;> subst r <;> decide)
  have k₂ : Keep VG.Proof.Rc2.AArch64.keyTemps s₁ s₂ := h₂.2.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h <;> subst r <;> decide)
  have keep := k₁.trans k₂
  have ptr := keep.reg .x21 (by decide)
  have index := (keep₁.reg .x23 (by decide)).trans rfl
  have index₂ : s₂.gpr .x23 = s.gpr .x23 := (h₂.2.reg .x23 (by decide)).trans index
  have write₂ : InRegions s₂.wr (s₂.gpr .x21 + s₂.gpr .x23) 1 := by
    rw [keep.wr, ptr, index₂]; exact writable
  obtain ⟨s₃, run₃, out₃, flag₃, keep₃⟩ := VG.Proof.Rc2.AArch64.fillOutput_ok s₂ write₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  refine ⟨by rw [out₃, index₂], by rw [flag₃, index₂], ?_⟩
  constructor
  · intro r hr
    exact (keep₃.reg r hr).trans (keep.reg r hr)
  · rw [keep₃.mem, keep.mem, ptr, index₂, h₂.1, out₁]
    simp [BitVec.setWidth_add]
  · exact keep₃.rd.trans keep.rd
  · exact keep₃.wr.trans keep.wr

theorem piStore_ok (s : State) (writable : InRegions s.wr (s.gpr .x21 + s.gpr .x23) 1) :
    WP isa (.block (piLookup ++ storeKey)) s (fun s' =>
      s'.gpr .x23 = s.gpr .x23 ∧
      Keep VG.Proof.Rc2.AArch64.keyTemps {s with
        mem := s.mem.writeW (s.gpr .x21 + s.gpr .x23) (Spec.Rc2.pi ((s.gpr .x8).setWidth 8))} s') := by
  rw [WP.block_append_iff]
  apply WP.mono (piLookup_ok s)
  intro s₁ h₁
  have ptr := h₁.2.reg .x21 (by decide)
  have index := h₁.2.reg .x23 (by decide)
  have valid : InRegions s₁.wr (s₁.gpr .x21 + s₁.gpr .x23) 1 := by
    rw [h₁.2.wr, ptr, index]; exact writable
  obtain ⟨s₂, run₂, index₂, keep₂⟩ := VG.Proof.Rc2.AArch64.storeByte_ok s₁ valid
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
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .x21 + s.gpr .x23) 1)
    (writable : InRegions s.wr (s.gpr .x21 + s.gpr .x23) 1) :
    WP isa (.block reduceKey) s (fun s' => s'.gpr .x23 = s.gpr .x23 ∧
      Keep VG.Proof.Rc2.AArch64.keyTemps {s with
        mem := s.mem.writeW (s.gpr .x21 + s.gpr .x23)
          (Spec.Rc2.pi (s.mem (s.gpr .x21 + s.gpr .x23) &&& (s.gpr .x2).setWidth 8))} s') := by
  rw [reduceKey, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := VG.Proof.Rc2.AArch64.reduceInput_ok s readable
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have ptr := keep₁.reg .x21 (by decide)
  have index := keep₁.reg .x23 (by decide)
  have valid : InRegions s₁.wr (s₁.gpr .x21 + s₁.gpr .x23) 1 := by
    rw [keep₁.wr, ptr, index]; exact writable
  apply WP.mono (VG.Proof.Rc2.AArch64.piStore_ok s₁ valid)
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
    (readLo : InRegions (s.rd ++ s.wr) (s.gpr .x21 + (s.gpr .x23 - 1#64) + 1#64) 1)
    (readHi : InRegions (s.rd ++ s.wr) (s.gpr .x21 + (s.gpr .x23 - 1#64 + s.gpr .x24)) 1)
    (writable : InRegions s.wr (s.gpr .x21 + (s.gpr .x23 - 1#64)) 1) :
    WP isa (.block descendKey) s (fun s' =>
      s'.gpr .x23 = s.gpr .x23 - 1 ∧ VG.Proof.Rc2.AArch64.zeroFlag s' = some ((s.gpr .x23 - 1) == 0) ∧
      Keep VG.Proof.Rc2.AArch64.keyTemps {s with
        mem := s.mem.writeW (s.gpr .x21 + (s.gpr .x23 - 1#64))
          (Spec.Rc2.pi (s.mem (s.gpr .x21 + (s.gpr .x23 - 1#64) + 1#64) ^^^
            s.mem (s.gpr .x21 + (s.gpr .x23 - 1#64 + s.gpr .x24))))} s') := by
  rw [descendKey, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, index₁, out₁, keep₁⟩ := VG.Proof.Rc2.AArch64.descendInput_ok s readLo readHi
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have ptr := keep₁.reg .x21 (by decide)
  have valid : InRegions s₁.wr (s₁.gpr .x21 + s₁.gpr .x23) 1 := by
    rw [keep₁.wr, ptr, index₁]; exact writable
  rw [← List.append_assoc, WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.AArch64.piStore_ok s₁ valid)
  intro s₂ h₂
  obtain ⟨s₃, run₃, flag₃, keep₃⟩ := VG.Proof.Rc2.AArch64.cmpZero_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have index₂ := h₂.1.trans index₁
  refine ⟨(keep₃.reg .x23 (by decide)).trans index₂, by rw [flag₃, index₂], ?_⟩
  constructor
  · intro r hr
    exact ((keep₃.reg r (by intro hm; simp only [List.mem_singleton] at hm; subst r; exact hr (by decide))).trans (h₂.2.reg r hr)).trans (keep₁.reg r (fun hm => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h | h <;> subst r <;> decide)))
  · rw [keep₃.mem, h₂.2.mem, keep₁.mem, ptr, index₁, out₁]
    simp
  · exact keep₃.rd.trans (h₂.2.rd.trans keep₁.rd)
  · exact keep₃.wr.trans (h₂.2.wr.trans keep₁.wr)


end VG.Proof.Rc2.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.KeyLoop`. -/
section

/-! # A bounded loop rule and frame invariant for key expansion -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.Impl.Rc2.AArch64

theorem forwardLoop (body : Prog isa) (I : Nat → State → Prop) (stop : Nat)
    (step : ∀ i < stop, ∀ s, I i s → WP isa body s (fun s' =>
      I (i + 1) s' ∧ VG.Proof.Rc2.AArch64.zeroFlag s' = some (decide (i + 1 = stop))))
    (i : Nat) (hi : i < stop) (s : State) (hs : I i s) :
    WP isa (.loop body (.nonzero .x .x10)) s (I stop) := by
  let Inv (n : Nat) (s : State) := ∃ i, i < stop ∧ stop - i = n ∧ I i s
  refine WP.loop (M := isa) Inv ?_ (stop - i) s ⟨i, hi, rfl, hs⟩
  intro n s ⟨j, hj, hn, hI⟩
  apply WP.mono (step j hj s hI)
  intro s' h'
  by_cases he : j + 1 = stop
  · left
    constructor
    · simp only [VG.Proof.Rc2.AArch64.eval_nonzero, h'.2, he, decide_true, Option.map_some, Bool.not_true]
    · rw [he] at h'
      exact h'.1
  · right
    constructor
    · simp only [VG.Proof.Rc2.AArch64.eval_nonzero, h'.2, he, decide_false, Option.map_some, Bool.not_false]
    · exact ⟨stop - (j + 1), by omega, j + 1, by omega, rfl, h'.1⟩

/-- Across a key-expansion loop only the six temporaries and the schedule
buffer change. The key, scratch saves, and return address are separate. -/
structure KeyFrame (s₀ s : State) : Prop where
  reg : ∀ r, r ∉ VG.Proof.Rc2.AArch64.keyTemps → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Frame [⟨s₀.gpr .x21, 128⟩] s₀.mem s.mem

theorem KeyFrame.refl (s : State) : VG.Proof.Rc2.AArch64.KeyFrame s s :=
  ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩

theorem KeyFrame.trans {s₀ s₁ s₂ : State} (h₁ : VG.Proof.Rc2.AArch64.KeyFrame s₀ s₁) (h₂ : VG.Proof.Rc2.AArch64.KeyFrame s₁ s₂) :
    VG.Proof.Rc2.AArch64.KeyFrame s₀ s₂ := by
  refine ⟨fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, ?_⟩
  have frame₂ := h₂.mem
  rw [h₁.reg .x21 (by decide)] at frame₂
  exact h₁.mem.trans frame₂

theorem KeyFrame.step {s₀ s s' : State} (h : VG.Proof.Rc2.AArch64.KeyFrame s₀ s) (i : Nat) (hi : i < 128)
    (b : Byte) (keep : Keep VG.Proof.Rc2.AArch64.keyTemps {s with mem := s.mem.writeW (s₀.gpr .x21 + BitVec.ofNat 64 i) b} s') : VG.Proof.Rc2.AArch64.KeyFrame s₀ s' := by
  refine ⟨fun r hr => (keep.reg r hr).trans (h.reg r hr), keep.rd.trans h.rd,
    keep.wr.trans h.wr, ?_⟩
  rw [keep.mem]
  exact h.mem.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))

theorem KeyFrame.keep {s₀ s s' : State} (h : VG.Proof.Rc2.AArch64.KeyFrame s₀ s) (keep : Keep VG.Proof.Rc2.AArch64.keyTemps s s') :
    VG.Proof.Rc2.AArch64.KeyFrame s₀ s' := by
  refine ⟨fun r hr => (keep.reg r hr).trans (h.reg r hr), keep.rd.trans h.rd,
    keep.wr.trans h.wr, ?_⟩
  rw [keep.mem]; exact h.mem

theorem counter_add (i : Nat) : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
  rw [BitVec.ofNat_add]
  rfl

theorem counter_eq (i n : Nat) (hi : i < 2 ^ 64) (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 64 i - BitVec.ofNat 64 n) == 0#64) = decide (i = n) := by
  have he : (BitVec.ofNat 64 i - BitVec.ofNat 64 n = 0#64) ↔ i = n := by bv_omega
  apply Bool.eq_iff_iff.mpr
  simpa only [beq_iff_eq, decide_eq_true_eq] using he

end VG.Proof.Rc2.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.CopyKey`. -/
section

/-! # The key-copy loop -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.Impl.Rc2.AArch64

theorem copyLoop_ok (s : State) (t : Nat) (ht : 1 ≤ t) (ht' : t ≤ 128)
    (len : s.gpr .x20 = BitVec.ofNat 64 t) (zero : s.gpr .x23 = 0)
    (readable : ∀ i < t, InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 i) 1)
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .x21 + BitVec.ofNat 64 i) 1)
    (sep : (Region.mk (s.gpr .x19) t).Disjoint ⟨s.gpr .x21, 128⟩) :
    WP isa (.loop (.block copyKey) (.nonzero .x .x10)) s (fun s' =>
      s'.gpr .x23 = BitVec.ofNat 64 t ∧ VG.Proof.Rc2.AArch64.KeyFrame s s' ∧
      BytesPrefix s'.mem (s.gpr .x21) (fill (Spec.Rc2.bytesAt s.mem (s.gpr .x19) t) 0) t) := by
  let key := Spec.Rc2.bytesAt s.mem (s.gpr .x19) t
  let I (i : Nat) (s' : State) := s'.gpr .x23 = BitVec.ofNat 64 i ∧ VG.Proof.Rc2.AArch64.KeyFrame s s' ∧
    BytesPrefix s'.mem (s.gpr .x21) (fill key 0) i
  apply VG.Proof.Rc2.AArch64.forwardLoop (.block copyKey) I t _ 0 (by omega) s
    ⟨zero, KeyFrame.refl s, fun i hi => by omega⟩
  intro i hi s₁ ⟨index₁, frame₁, prefix₁⟩
  have keyPtr := frame₁.reg .x19 (by decide)
  have outPtr := frame₁.reg .x21 (by decide)
  have len₁ := (frame₁.reg .x20 (by decide)).trans len
  have read₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x19 + s₁.gpr .x23) 1 := by
    rw [frame₁.rd, frame₁.wr, keyPtr, index₁]
    exact readable i hi
  have write₁ : InRegions s₁.wr (s₁.gpr .x21 + s₁.gpr .x23) 1 := by
    rw [frame₁.wr, outPtr, index₁]
    exact writable i (by omega)
  have byte₁ : s₁.mem (s₁.gpr .x19 + s₁.gpr .x23) = key.getD i 0 := by
    rw [keyPtr, index₁, bytesAt_getD _ _ _ _ hi]
    exact frame₁.mem.bytes (by simpa using sep) (by change t ≤ 2 ^ 64; omega) hi
  obtain ⟨s₂, run₂, index₂, flag₂, keep₂⟩ := VG.Proof.Rc2.AArch64.copyKey_ok s₁ read₁ write₁
  have keep₂' : Keep VG.Proof.Rc2.AArch64.keyTemps
      {s₁ with mem := s₁.mem.writeW (s.gpr .x21 + BitVec.ofNat 64 i) (key.getD i 0)} s₂ := by
    rw [byte₁] at keep₂
    simpa only [outPtr, index₁] using keep₂
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  constructor
  · refine ⟨?_, frame₁.step i (by omega) _ keep₂', ?_⟩
    · rw [index₂, index₁, VG.Proof.Rc2.AArch64.counter_add]
    · rw [keep₂'.mem]
      have prefix₂ := prefix₁.extend (show i < 128 by omega) (key.getD i 0)
      rw [initial_set key i] at prefix₂
      exact prefix₂
  · rw [flag₂, index₁, len₁, VG.Proof.Rc2.AArch64.counter_add]
    exact congrArg some (VG.Proof.Rc2.AArch64.counter_eq (i + 1) t (by omega) (by omega))

end VG.Proof.Rc2.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.DescendKey`. -/
section

/-! # The descending effective-key reduction loop -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.Impl.Rc2.AArch64

theorem descendLoop_ok (s : State) (l : KeyBytes) (t8 : Nat) (ht : 1 ≤ t8) (ht' : t8 < 128)
    (len : s.gpr .x24 = BitVec.ofNat 64 t8) (start : s.gpr .x23 = BitVec.ofNat 64 (128 - t8))
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .x21 + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (s.gpr .x21) l 128) :
    WP isa (.loop (.block descendKey) (.nonzero .x .x10)) s (fun s' =>
      s'.gpr .x23 = 0 ∧ VG.Proof.Rc2.AArch64.KeyFrame s s' ∧
      BytesPrefix s'.mem (s.gpr .x21) (descend l t8 (128 - t8)) 128) := by
  let I (j : Nat) (s' : State) := s'.gpr .x23 = BitVec.ofNat 64 (128 - t8 - j) ∧ VG.Proof.Rc2.AArch64.KeyFrame s s' ∧
    BytesPrefix s'.mem (s.gpr .x21) (descend l t8 j) 128
  have finish : I (128 - t8) = (fun s' => s'.gpr .x23 = 0 ∧ VG.Proof.Rc2.AArch64.KeyFrame s s' ∧
      BytesPrefix s'.mem (s.gpr .x21) (descend l t8 (128 - t8)) 128) := by
    funext s'
    simp only [I, Nat.sub_self]
    rfl
  rw [← finish]
  apply VG.Proof.Rc2.AArch64.forwardLoop (.block descendKey) I (128 - t8) _ 0 (by omega) s
    ⟨start, KeyFrame.refl s, initialPrefix⟩
  intro j hj s₁ ⟨index₁, frame₁, prefix₁⟩
  have outPtr := frame₁.reg .x21 (by decide)
  have len₁ := (frame₁.reg .x24 (by decide)).trans len
  have indexNew : s₁.gpr .x23 - 1#64 = BitVec.ofNat 64 (127 - t8 - j) := by
    rw [index₁, Offset.ofNat_sub_ofNat (show 1 ≤ 128 - t8 - j by omega)]
    congr 1; omega
  have loAddr : s₁.gpr .x21 + (s₁.gpr .x23 - 1#64) + 1#64 =
      s.gpr .x21 + BitVec.ofNat 64 (127 - t8 - j + 1) := by
    rw [outPtr, indexNew, BitVec.add_assoc]
    exact congrArg (s.gpr .x21 + ·) (VG.Proof.Rc2.AArch64.counter_add _)
  have hiAddr : s₁.gpr .x21 + (s₁.gpr .x23 - 1#64 + s₁.gpr .x24) =
      s.gpr .x21 + BitVec.ofNat 64 (127 - t8 - j + t8) := by
    rw [outPtr, indexNew, len₁, ← BitVec.ofNat_add]
  have read₁ (i : Nat) (hi : i < 128) :
      InRegions (s₁.rd ++ s₁.wr) (s.gpr .x21 + BitVec.ofNat 64 i) 1 := by
    obtain ⟨r, hr, hc⟩ := writable i hi
    rw [frame₁.wr]
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have write₁ : InRegions s₁.wr (s₁.gpr .x21 + (s₁.gpr .x23 - 1#64)) 1 := by
    rw [frame₁.wr, outPtr, indexNew]
    exact writable _ (by omega)
  have readLo : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x21 + (s₁.gpr .x23 - 1#64) + 1#64) 1 := by
    rw [loAddr]; exact read₁ _ (by omega)
  have readHi : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x21 + (s₁.gpr .x23 - 1#64 + s₁.gpr .x24)) 1 := by
    rw [hiAddr]; exact read₁ _ (by omega)
  apply WP.mono (VG.Proof.Rc2.AArch64.descendKey_ok s₁ readLo readHi write₁)
  intro s₂ h₂
  let b := Spec.Rc2.pi ((descend l t8 j).getD (127 - t8 - j + 1) 0 ^^^
    (descend l t8 j).getD (127 - t8 - j + t8) 0)
  have keep₂ : Keep VG.Proof.Rc2.AArch64.keyTemps {s₁ with
      mem := s₁.mem.writeW (s.gpr .x21 + BitVec.ofNat 64 (127 - t8 - j)) b} s₂ := by
    have h := h₂.2.2
    rw [loAddr, hiAddr, prefix₁ _ (by omega), prefix₁ _ (by omega), outPtr, indexNew] at h
    exact h
  constructor
  · refine ⟨?_, frame₁.step (127 - t8 - j) (by omega) b keep₂, ?_⟩
    · rw [h₂.1]
      change s₁.gpr .x23 - 1#64 = _
      rw [indexNew]
      congr 1; omega
    · rw [keep₂.mem, descend_succ]
      exact prefix₁.write (by decide) (by omega) b
  · rw [h₂.2.1]
    change some ((s₁.gpr .x23 - 1#64) == 0#64) = _
    rw [indexNew]
    have he : 127 - t8 - j = 0 ↔ j + 1 = 128 - t8 := by omega
    have eqZero := VG.Proof.Rc2.AArch64.counter_eq (127 - t8 - j) 0 (by omega) (by decide)
    simp only [BitVec.sub_zero] at eqZero
    rw [eqZero]
    simp only [he]

end VG.Proof.Rc2.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.FillKey`. -/
section

/-! # Forward expansion to 128 bytes -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.Impl.Rc2.AArch64

theorem fillLoop_ok (s : State) (key : List Byte) (ht : 1 ≤ key.length) (ht' : key.length < 128)
    (len : s.gpr .x20 = BitVec.ofNat 64 key.length) (start : s.gpr .x23 = BitVec.ofNat 64 key.length)
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .x21 + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (s.gpr .x21) (fill key 0) key.length) :
    WP isa (.loop (.block fillKey) (.nonzero .x .x10)) s (fun s' =>
      s'.gpr .x23 = 128 ∧ VG.Proof.Rc2.AArch64.KeyFrame s s' ∧
      BytesPrefix s'.mem (s.gpr .x21) (fill key (128 - key.length)) 128) := by
  let I (j : Nat) (s' : State) := s'.gpr .x23 = BitVec.ofNat 64 (key.length + j) ∧ VG.Proof.Rc2.AArch64.KeyFrame s s' ∧
    BytesPrefix s'.mem (s.gpr .x21) (fill key j) (key.length + j)
  have finish : I (128 - key.length) = (fun s' => s'.gpr .x23 = 128 ∧ VG.Proof.Rc2.AArch64.KeyFrame s s' ∧
      BytesPrefix s'.mem (s.gpr .x21) (fill key (128 - key.length)) 128) := by
    funext s'
    simp only [I, Nat.add_sub_of_le (Nat.le_of_lt ht')]
    rfl
  rw [← finish]
  apply VG.Proof.Rc2.AArch64.forwardLoop (.block fillKey) I (128 - key.length) _ 0 (by omega) s
    ⟨start, KeyFrame.refl s, initialPrefix⟩
  intro j hj s₁ ⟨index₁, frame₁, prefix₁⟩
  have outPtr := frame₁.reg .x21 (by decide)
  have len₁ := (frame₁.reg .x20 (by decide)).trans len
  have loAddr : s₁.gpr .x21 + s₁.gpr .x23 - 1#64 =
      s.gpr .x21 + BitVec.ofNat 64 (key.length + j - 1) := by
    rw [outPtr, index₁]
    exact Offset.add_ofNat_sub _ (by omega)
  have hiAddr : s₁.gpr .x21 + (s₁.gpr .x23 - s₁.gpr .x20) =
      s.gpr .x21 + BitVec.ofNat 64 j := by
    rw [outPtr, index₁, len₁, Offset.ofNat_sub_ofNat (by omega), Nat.add_sub_cancel_left]
  have read₁ (i : Nat) (hi : i < 128) :
      InRegions (s₁.rd ++ s₁.wr) (s.gpr .x21 + BitVec.ofNat 64 i) 1 := by
    obtain ⟨r, hr, hc⟩ := writable i hi
    rw [frame₁.wr]
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have write₁ : InRegions s₁.wr (s₁.gpr .x21 + s₁.gpr .x23) 1 := by
    rw [frame₁.wr, outPtr, index₁]
    exact writable _ (by omega)
  have readLo : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x21 + s₁.gpr .x23 - 1#64) 1 := by
    rw [loAddr]; exact read₁ _ (by omega)
  have readHi : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x21 + (s₁.gpr .x23 - s₁.gpr .x20)) 1 := by
    rw [hiAddr]; exact read₁ _ (by omega)
  apply WP.mono (VG.Proof.Rc2.AArch64.fillKey_ok s₁ readLo readHi write₁)
  intro s₂ h₂
  let b := Spec.Rc2.pi ((fill key j).getD (key.length + j - 1) 0 + (fill key j).getD j 0)
  have keep₂ : Keep VG.Proof.Rc2.AArch64.keyTemps {s₁ with
      mem := s₁.mem.writeW (s.gpr .x21 + BitVec.ofNat 64 (key.length + j)) b} s₂ := by
    have h := h₂.2.2
    rw [loAddr, hiAddr, prefix₁ _ (by omega), prefix₁ _ (by omega), outPtr, index₁] at h
    exact h
  constructor
  · refine ⟨?_, frame₁.step (key.length + j) (by omega) b keep₂, ?_⟩
    · rw [h₂.1, index₁, VG.Proof.Rc2.AArch64.counter_add, Nat.add_assoc]
    · rw [keep₂.mem, fill_succ]
      have h := prefix₁.extend (show key.length + j < 128 by omega) b
      simpa only [fillStep, Nat.add_sub_cancel_left, Nat.add_assoc] using h
  · rw [h₂.2.1, index₁, VG.Proof.Rc2.AArch64.counter_add]
    have he : key.length + j + 1 = 128 ↔ j + 1 = 128 - key.length := by omega
    change some ((BitVec.ofNat 64 (key.length + j + 1) - BitVec.ofNat 64 128) == 0#64) = _
    rw [VG.Proof.Rc2.AArch64.counter_eq _ _ (by omega) (by decide)]
    simp only [he]

end VG.Proof.Rc2.AArch64

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Mask`. -/
section

/-! # Public effective-key mask selection -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc2.AArch64

theorem small_imm (i : Nat) (hi : i < 256) :
    (BitVec.ofNat 16 i).setWidth 64 = BitVec.ofNat 64 i := by
  rw [index_imm i hi]
  bv_omega

theorem cmpMask_ok (s : State) (i : Nat) (hi : i < 7) :
    ∃ s', runBlock isa [.subImm .x .x10 .x5 (i + 1)] s = some s' ∧
      zeroFlag s' = some (s.gpr .x5 == BitVec.ofNat 64 (i + 1)) ∧ Keep [.x10] s s' := by
  have bound : i + 1 < 4096 := by omega
  refine ⟨s.write .x .x10 (s.gpr .x5 - BitVec.ofNat 64 (i + 1)), ?_, ?_⟩
  · simp only [runBlock_cons, exec, bound, ite_true, State.read, BitVec.setWidth_eq,
      runStep_some, runBlock_nil]
  constructor
  · simp only [zeroFlag, gpr_write_self, BitVec.setWidth_eq]
    apply congrArg some
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    bv_omega
  · exact ⟨fun r hr => gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl⟩

theorem setMask_ok (s : State) (i : Nat) (hi : i < 7) :
    ∃ s', runBlock isa [imm .x2 (2 ^ (i + 1) - 1)] s = some s' ∧
      s'.gpr .x2 = BitVec.ofNat 64 (2 ^ (i + 1) - 1) ∧ Keep [.x2, .x10] s s' := by
  refine ⟨_, by
    simp only [imm, runBlock_cons, exec]
    rfl, ?_⟩
  constructor
  · simp only [gpr_write_self, BitVec.setWidth_eq, Nat.mul_zero, BitVec.shiftLeft_zero]
    apply small_imm
    have bound : ∀ i < 7, 2 ^ (i + 1) - 1 < 256 := by decide
    exact bound i hi
  · exact ⟨fun r hr => gpr_write_of_ne _ _ _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact hr.1), rfl, rfl, rfl⟩

theorem maskBranch_ok (s : State) (i : Nat) (hi : i < 7) :
    WP isa (.seq (.block [.subImm .x .x10 .x5 (i + 1)])
      (.ite (.zero .x .x10) (.block [imm .x2 (2 ^ (i + 1) - 1)]) (.block []))) s (fun s' =>
        s'.gpr .x2 = (if s.gpr .x5 = BitVec.ofNat 64 (i + 1)
          then BitVec.ofNat 64 (2 ^ (i + 1) - 1) else s.gpr .x2) ∧ Keep [.x2, .x10] s s') := by
  apply WP.seq
  obtain ⟨s₁, run₁, flag₁, keep₁⟩ := cmpMask_ok s i hi
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  apply WP.ite (s.gpr .x5 == BitVec.ofNat 64 (i + 1)) (by exact flag₁)
  · intro he
    have eq := beq_iff_eq.mp he
    obtain ⟨s₂, run₂, out₂, keep₂⟩ := setMask_ok s₁ i hi
    apply WP.of_runBlock
    refine ⟨s₂, run₂, ?_, ?_⟩
    · rw [ite_eq_left eq]; exact out₂
    · exact (keep₁.weaken (by simp)).trans keep₂
  · intro he
    have ne : s.gpr .x5 ≠ BitVec.ofNat 64 (i + 1) := by simpa using he
    apply WP.block_nil
    refine ⟨?_, keep₁.weaken (by simp)⟩
    rw [ite_eq_right ne]
    exact keep₁.reg .x2 (by simp)

private theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} :
    WP isa (.seq (.seq a b) c) s Q ↔ WP isa (.seq a (.seq b c)) s Q := by
  constructor
  · intro h
    exact WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)
  · intro h
    exact WP.seq (WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h => WP.seq_iff.mp h))

theorem maskBranches_ok (is : List Nat) (hi : ∀ i ∈ is, i < 7)
    (s : State) (k : Nat) (hk : k < 8) (index : s.gpr .x5 = BitVec.ofNat 64 k) :
    WP isa (is.foldr (fun i rest =>
      .seq (.block [.subImm .x .x10 .x5 (i + 1)])
        (.seq (.ite (.zero .x .x10) (.block [imm .x2 (2 ^ (i + 1) - 1)]) (.block [])) rest)) (.block []))
      s (fun s' => s'.gpr .x2 = (if k ∈ is.map (· + 1) then
        BitVec.ofNat 64 (2 ^ k - 1) else s.gpr .x2) ∧ Keep [.x2, .x10] s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.foldr_cons, ← seq_assoc]
    apply WP.seq
    apply WP.mono (maskBranch_ok s i (hi i List.mem_cons_self))
    intro s₁ h₁
    have index₁ := (h₁.2.reg .x5 (by decide)).trans index
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁ index₁)
    intro s₂ h₂
    refine ⟨?_, h₁.2.trans h₂.2⟩
    rw [h₂.1, h₁.1, index]
    have eq : BitVec.ofNat 64 k = BitVec.ofNat 64 (i + 1) ↔ k = i + 1 := by
      have bound := hi i List.mem_cons_self
      bv_omega
    simp only [eq, List.map_cons, List.mem_cons]
    by_cases he : k = i + 1
    · subst k; simp
    · by_cases hm : k ∈ is.map (· + 1) <;> simp [he, hm]

theorem maskStart_ok (s : State) :
    ∃ s', runBlock isa ([rr .x5 .x22] ++ mask .x5 3 ++ [imm .x2 255]) s = some s' ∧
      s'.gpr .x5 = s.gpr .x22 &&& 7 ∧ s'.gpr .x2 = 255 ∧ Keep [.x2, .x5, .x10] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [rr, imm, mask, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, State.read, gpr_write,
      BitVec.setWidth_eq, BitVec.add_zero, ite_true]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_false, ite_true]
    rw [maskBits _ 3 (by decide)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_and]
    change (s.gpr .x22).toNat % 8 % 2 ^ 64 = (s.gpr .x22).toNat &&& (2 ^ 3 - 1)
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  · rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_write, BitVec.setWidth_eq, hr.1, hr.2.1, ite_false]
    · rfl
    · rfl
    · rfl

theorem maskCode_ok (s : State) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (input : s.gpr .x22 = BitVec.ofNat 64 bits) :
    WP isa maskCode s (fun s' =>
      (s'.gpr .x2).setWidth 8 = BitVec.ofNat 8 (255 % 2 ^ (8 + bits - 8 * ((bits + 7) / 8))) ∧
      Keep [.x2, .x5, .x10] s s') := by
  rw [maskCode]
  apply WP.seq
  obtain ⟨s₁, run₁, index₁, mask₁, keep₁⟩ := maskStart_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have index : s₁.gpr .x5 = BitVec.ofNat 64 (bits % 8) := by
    rw [index₁, input]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    change bits % 2 ^ 64 &&& (2 ^ 3 - 1) = bits % 8 % 2 ^ 64
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
      ((if r ∈ (List.range 7).map (· + 1) then BitVec.ofNat 64 (2 ^ r - 1)
        else 255).setWidth 8) = BitVec.ofNat 8 (255 % 2 ^ (if r = 0 then 8 else r)) := by decide
  exact fact _ (Nat.mod_lt _ (by decide))

end VG.Proof.Rc2.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Key`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.KeySetup`. -/
section

/-! # Key-expansion control and register setup -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc2.AArch64

theorem cmp128_ok (s : State) :
    ∃ s', runBlock isa [.subImm .x .x10 .x23 128] s = some s' ∧
      zeroFlag s' = some ((s.gpr .x23 - 128) == 0) ∧ Keep [.x10] s s' := by
  refine ⟨s.write .x .x10 (s.gpr .x23 - 128), ?_, ?_⟩
  · simp (config := {decide := true}) only [runBlock_cons,
      exec, State.read, BitVec.setWidth_eq]
    rfl
  constructor
  · rfl
  · exact ⟨fun r hr => gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl⟩

theorem maybeFill_ok (s : State) (key : List Byte) (ht : 1 ≤ key.length) (ht' : key.length ≤ 128)
    (len : s.gpr .x20 = BitVec.ofNat 64 key.length) (start : s.gpr .x23 = BitVec.ofNat 64 key.length)
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .x21 + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (s.gpr .x21) (fill key 0) key.length) :
    WP isa (.seq (.block [.subImm .x .x10 .x23 128])
      (.ite (.nonzero .x .x10) (.loop (.block fillKey) (.nonzero .x .x10)) (.block []))) s (fun s' =>
        s'.gpr .x23 = 128 ∧ KeyFrame s s' ∧
        BytesPrefix s'.mem (s.gpr .x21) (fill key (128 - key.length)) 128) := by
  apply WP.seq
  obtain ⟨s₁, run₁, flag₁, keep₁⟩ := VG.Proof.Rc2.AArch64.cmp128_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have frame₁ := (KeyFrame.refl s).keep (keep₁.weaken (by simp [keyTemps]))
  have flag : zeroFlag s₁ = some (decide (key.length = 128)) := by
    rw [flag₁, start]
    exact congrArg some (counter_eq _ _ (by omega) (by decide))
  have ptr₁ := keep₁.reg .x21 (by simp)
  by_cases he : key.length = 128
  · apply WP.ite false (by simp only [eval_nonzero, flag, he, decide_true, Option.map_some, Bool.not_true])
    · simp
    · intro _
      apply WP.block_nil
      refine ⟨?_, frame₁, ?_⟩
      · rw [keep₁.reg .x23 (by simp), start, he]; rfl
      · rw [keep₁.mem]
        simpa only [he, Nat.sub_self] using initialPrefix
  · apply WP.ite true (by simp only [eval_nonzero, flag, he, decide_false, Option.map_some, Bool.not_false])
    · intro _
      have writes : ∀ i < 128, InRegions s₁.wr (s₁.gpr .x21 + BitVec.ofNat 64 i) 1 := by
        rw [keep₁.wr, ptr₁]; exact writable
      have initial : BytesPrefix s₁.mem (s₁.gpr .x21) (fill key 0) key.length := by
        rw [keep₁.mem, ptr₁]; exact initialPrefix
      apply WP.mono (fillLoop_ok s₁ key ht (by omega)
        ((keep₁.reg .x20 (by simp)).trans len) ((keep₁.reg .x23 (by simp)).trans start) writes initial)
      intro s₂ h₂
      exact ⟨h₂.1, frame₁.trans h₂.2.1, by rw [ptr₁] at h₂; exact h₂.2.2⟩
    · simp

theorem setReduction_ok (s : State) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (input : s.gpr .x22 = BitVec.ofNat 64 bits) :
    ∃ s', runBlock isa reduceSetup s = some s' ∧
      s'.gpr .x24 = BitVec.ofNat 64 ((bits + 7) / 8) ∧
      s'.gpr .x23 = BitVec.ofNat 64 (128 - (bits + 7) / 8) ∧ Keep [.x24, .x23] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [reduceSetup, imm, runBlock_cons, runStep_some, runBlock_nil,
      exec, State.read,
      gpr_write, BitVec.setWidth_eq, ite_true, ite_false]
    rfl, ?_⟩
  have t8 : (s.gpr .x22 + 7#64) >>> 3 = BitVec.ofNat 64 ((bits + 7) / 8) := by
    rw [input]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]
    exact t8
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]
    change 128#64 - (s.gpr .x22 + 7#64) >>> 3 = _
    rw [t8]
    exact Offset.ofNat_sub_ofNat (by omega)
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_write, BitVec.setWidth_eq, hr.1, hr.2, ite_false]
    · simp only [mem_write]
    · simp only [rd_write]
    · simp only [wr_write]

theorem maybeDescend_ok (s : State) (l : KeyBytes) (t8 : Nat) (ht : 1 ≤ t8) (ht' : t8 ≤ 128)
    (len : s.gpr .x24 = BitVec.ofNat 64 t8) (start : s.gpr .x23 = BitVec.ofNat 64 (128 - t8))
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .x21 + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (s.gpr .x21) l 128) :
    WP isa (.seq (.block [rr .x10 .x23])
      (.ite (.nonzero .x .x10) (.loop (.block descendKey) (.nonzero .x .x10)) (.block []))) s (fun s' =>
        KeyFrame s s' ∧ BytesPrefix s'.mem (s.gpr .x21) (descend l t8 (128 - t8)) 128) := by
  apply WP.seq
  obtain ⟨s₁, run₁, flag₁, keep₁⟩ := cmpZero_ok s
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have frame₁ := (KeyFrame.refl s).keep (keep₁.weaken (by simp [keyTemps]))
  have flag : zeroFlag s₁ = some (decide (t8 = 128)) := by
    rw [flag₁, start]
    have eqZero := counter_eq (128 - t8) 0 (by omega) (by decide)
    simp only [BitVec.sub_zero] at eqZero
    change some (BitVec.ofNat 64 (128 - t8) == 0#64) = _
    rw [eqZero]
    have he : 128 - t8 = 0 ↔ t8 = 128 := by omega
    simp only [he]
  have ptr₁ := keep₁.reg .x21 (by simp)
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
      have writes : ∀ i < 128, InRegions s₁.wr (s₁.gpr .x21 + BitVec.ofNat 64 i) 1 := by
        rw [keep₁.wr, ptr₁]; exact writable
      have initial : BytesPrefix s₁.mem (s₁.gpr .x21) l 128 := by
        rw [keep₁.mem, ptr₁]; exact initialPrefix
      apply WP.mono (descendLoop_ok s₁ l t8 ht (by omega)
        ((keep₁.reg .x24 (by simp)).trans len) ((keep₁.reg .x23 (by simp)).trans start) writes initial)
      intro s₂ h₂
      exact ⟨frame₁.trans h₂.2.1, by rw [ptr₁] at h₂; exact h₂.2.2⟩
    · simp

end VG.Proof.Rc2.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.KeyBody`. -/
section

/-! # Composing the RC2 key-expansion stages -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.Impl.Rc2.AArch64

def coreRegs : List Reg := [.x4, .x21, .x25, .x26, .x27, .x28, .x30]

structure CoreFrame (s₀ s : State) : Prop where
  reg : ∀ r ∈ VG.Proof.Rc2.AArch64.coreRegs, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Frame [⟨s₀.gpr .x21, 128⟩] s₀.mem s.mem

theorem CoreFrame.of_keep {s s' : State} {rs : List Reg} (keep : Keep rs s s')
    (sep : ∀ r ∈ VG.Proof.Rc2.AArch64.coreRegs, r ∉ rs) : VG.Proof.Rc2.AArch64.CoreFrame s s' := by
  refine ⟨fun r hr => keep.reg r (sep r hr), keep.rd, keep.wr, ?_⟩
  rw [keep.mem]; exact Frame.refl _ _

theorem CoreFrame.of_key {s s' : State} (h : KeyFrame s s') : VG.Proof.Rc2.AArch64.CoreFrame s s' := by
  have sep : ∀ r ∈ VG.Proof.Rc2.AArch64.coreRegs, r ∉ keyTemps := by decide
  exact ⟨fun r hr => h.reg r (sep r hr), h.rd, h.wr, h.mem⟩

theorem CoreFrame.trans {s₀ s₁ s₂ : State} (h₁ : VG.Proof.Rc2.AArch64.CoreFrame s₀ s₁) (h₂ : VG.Proof.Rc2.AArch64.CoreFrame s₁ s₂) :
    VG.Proof.Rc2.AArch64.CoreFrame s₀ s₂ := by
  refine ⟨fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, ?_⟩
  have frame₂ := h₂.mem
  rw [h₁.reg .x21 (by decide)] at frame₂
  exact h₁.mem.trans frame₂

theorem expandCopyFill_ok (s : State) (t : Nat) (ht : 1 ≤ t) (ht' : t ≤ 128)
    (len : s.gpr .x20 = BitVec.ofNat 64 t) (zero : s.gpr .x23 = 0)
    (readable : ∀ i < t, InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 i) 1)
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .x21 + BitVec.ofNat 64 i) 1)
    (sep : (Region.mk (s.gpr .x19) t).Disjoint ⟨s.gpr .x21, 128⟩) :
    WP isa expandCopyFill s (fun s' => KeyFrame s s' ∧
      BytesPrefix s'.mem (s.gpr .x21) (fill (Spec.Rc2.bytesAt s.mem (s.gpr .x19) t) (128 - t)) 128) := by
  rw [expandCopyFill]
  apply WP.seq
  apply WP.mono (copyLoop_ok s t ht ht' len zero readable writable sep)
  intro s₁ h₁
  have length : (Spec.Rc2.bytesAt s.mem (s.gpr .x19) t).length = t := by
    simp [Spec.Rc2.bytesAt]
  have ptr₁ := h₁.2.1.reg .x21 (by decide)
  have writes : ∀ i < 128, InRegions s₁.wr (s₁.gpr .x21 + BitVec.ofNat 64 i) 1 := by
    rw [h₁.2.1.wr, ptr₁]; exact writable
  apply WP.mono (VG.Proof.Rc2.AArch64.maybeFill_ok s₁ (Spec.Rc2.bytesAt s.mem (s.gpr .x19) t)
    (by rw [length]; exact ht) (by rw [length]; exact ht')
    (by rw [length]; exact (h₁.2.1.reg .x20 (by decide)).trans len)
    (by rw [length]; exact h₁.1) writes (by rw [ptr₁, length]; exact h₁.2.2))
  intro s₂ h₂
  exact ⟨h₁.2.1.trans h₂.2.1, by rw [length, ptr₁] at h₂; exact h₂.2.2⟩

theorem reduceDescend_ok (s : State) (l : KeyBytes) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (len : s.gpr .x24 = BitVec.ofNat 64 ((bits + 7) / 8))
    (index : s.gpr .x23 = BitVec.ofNat 64 (128 - (bits + 7) / 8))
    (mask : (s.gpr .x2).setWidth 8 = BitVec.ofNat 8 (255 % 2 ^ (8 + bits - 8 * ((bits + 7) / 8))))
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .x21 + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (s.gpr .x21) l 128) :
    WP isa (.seq (.block reduceKey) (.seq (.block [rr .x10 .x23])
      (.ite (.nonzero .x .x10) (.loop (.block descendKey) (.nonzero .x .x10)) (.block [])))) s (fun s' =>
        KeyFrame s s' ∧ BytesPrefix s'.mem (s.gpr .x21)
          (descend (reduce l bits) ((bits + 7) / 8) (128 - (bits + 7) / 8)) 128) := by
  have bound : 1 ≤ (bits + 7) / 8 ∧ (bits + 7) / 8 ≤ 128 := by omega
  have writes : InRegions s.wr (s.gpr .x21 + s.gpr .x23) 1 := by
    rw [index]; exact writable _ (by omega)
  have reads : InRegions (s.rd ++ s.wr) (s.gpr .x21 + s.gpr .x23) 1 := by
    obtain ⟨r, hr, hc⟩ := writes
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.seq
  apply WP.mono (reduceKey_ok s reads writes)
  intro s₁ h₁
  have keep₁ := h₁.2
  rw [index, initialPrefix _ (by omega), mask] at keep₁
  have frame₁ := (KeyFrame.refl s).step _ (by omega) _ keep₁
  have ptr₁ := keep₁.reg .x21 (by decide)
  have prefix₁ : BytesPrefix s₁.mem (s.gpr .x21) (reduce l bits) 128 := by
    rw [keep₁.mem]
    exact initialPrefix.write (by decide) (by omega) _
  have write₁ : ∀ i < 128, InRegions s₁.wr (s₁.gpr .x21 + BitVec.ofNat 64 i) 1 := by
    rw [keep₁.wr, ptr₁]; exact writable
  apply WP.mono (VG.Proof.Rc2.AArch64.maybeDescend_ok s₁ (reduce l bits) ((bits + 7) / 8) bound.1 bound.2
    ((keep₁.reg .x24 (by decide)).trans len) (h₁.1.trans index) write₁
    (by rw [ptr₁]; exact prefix₁))
  intro s₂ h₂
  exact ⟨frame₁.trans h₂.1, by rw [ptr₁] at h₂; exact h₂.2⟩

theorem expandReduce_ok (s : State) (l : KeyBytes) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (input : s.gpr .x22 = BitVec.ofNat 64 bits)
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .x21 + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (s.gpr .x21) l 128) :
    WP isa expandReduce s (fun s' => VG.Proof.Rc2.AArch64.CoreFrame s s' ∧ BytesPrefix s'.mem (s.gpr .x21)
      (descend (reduce l bits) ((bits + 7) / 8) (128 - (bits + 7) / 8)) 128) := by
  rw [expandReduce]
  apply WP.seq
  obtain ⟨s₁, run₁, len₁, index₁, keep₁⟩ := VG.Proof.Rc2.AArch64.setReduction_ok s bits hb hb' input
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  apply WP.seq
  apply WP.mono (maskCode_ok s₁ bits hb hb' ((keep₁.reg .x22 (by decide)).trans input))
  intro s₂ h₂
  have frame := (CoreFrame.of_keep keep₁ (by decide)).trans (CoreFrame.of_keep h₂.2 (by decide))
  have ptr₂ := frame.reg .x21 (by decide)
  have writes : ∀ i < 128, InRegions s₂.wr (s₂.gpr .x21 + BitVec.ofNat 64 i) 1 := by
    rw [frame.wr, ptr₂]; exact writable
  apply WP.mono (VG.Proof.Rc2.AArch64.reduceDescend_ok s₂ l bits hb hb'
    ((h₂.2.reg .x24 (by decide)).trans len₁) ((h₂.2.reg .x23 (by decide)).trans index₁) h₂.1 writes
    (by rw [ptr₂, h₂.2.mem, keep₁.mem]; exact initialPrefix))
  intro s₃ h₃
  exact ⟨frame.trans (CoreFrame.of_key h₃.1), by rw [ptr₂] at h₃; exact h₃.2⟩

end VG.Proof.Rc2.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.KeyIO`. -/
section

/-! # Register setup and scratch saves for key expansion -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc2.AArch64

def savedReg (i : Nat) : Reg := saved.getD i .x23

theorem keySave_eq : save .x4 0 = Spill.saveCode .x4 (Spill.slots VG.Proof.Rc2.AArch64.savedReg 6) := by rfl

theorem keyRestore_eq : restore .x4 0 = Spill.restoreCode .x4 (Spill.slots VG.Proof.Rc2.AArch64.savedReg 6) := by rfl

theorem pinKey_ok (s : State) :
    ∃ s', runBlock isa [rr .x19 .x0, rr .x20 .x1, rr .x21 .x3, rr .x22 .x2, imm .x23 0] s = some s' ∧
      s'.gpr .x19 = s.gpr .x0 ∧ s'.gpr .x20 = s.gpr .x1 ∧
      s'.gpr .x21 = s.gpr .x3 ∧ s'.gpr .x22 = s.gpr .x2 ∧ s'.gpr .x23 = 0 ∧ Keep saved s s' := by
  refine ⟨_, by
    simp only [rr, imm, runBlock_cons, exec]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · simp [gpr_write, State.read, BitVec.add_zero, BitVec.setWidth_eq]
  · exact gpr_write_self _ _ _ _
  · constructor
    · intro r hr
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_write, BitVec.setWidth_eq, State.read, BitVec.add_zero, hr.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]
    · simp only [mem_write]
    · simp only [rd_write]
    · simp only [wr_write]

theorem bytesAt_frame {m m' : Mem} {p : Addr} {n : Nat} {rs : List Region}
    (frame : Frame rs m m') (sep : ∀ r ∈ rs, (Region.mk p n).Disjoint r) (bound : n ≤ 2 ^ 64) :
    Spec.Rc2.bytesAt m' p n = Spec.Rc2.bytesAt m p n := by
  unfold Spec.Rc2.bytesAt
  apply List.map_congr_left
  intro i hi
  exact frame.bytes sep bound (List.mem_range.mp hi)

end VG.Proof.Rc2.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Key`. -/
section

/-! # Verified RC2 key expansion -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.Impl.Rc2.AArch64

def keyContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let out : Region := ⟨s.gpr .x3, 128⟩
    let scratch : Region := ⟨s.gpr .x4, 512⟩
    s.rd = [key] ∧ s.wr = [out, scratch] ∧ key.Disjoint out ∧ key.Disjoint scratch ∧
      out.Disjoint scratch ∧
      Spec.Rc2.validKey (s.gpr .x1).toNat (s.gpr .x2).toNat
  post s s' := Spec.Rc2.scheduleAt s'.mem (s.gpr .x3) =
    Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) (s.gpr .x2).toNat
  pub := PublicRegs [.x0, .x1, .x2, .x3, .x4]

theorem key_body_correct (s : State) (hs : keyContract.pre s) :
    WP isa expandKey s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ keyContract.post s s') := by
  obtain ⟨hrd, hwr, keyOut, keyScratch, outScratch, ht, ht', hb, hb'⟩ := hs
  have writes : ∀ i < 6, InRegions s.wr (s.gpr .x4 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .x4, 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  rw [expandKey]
  apply WP.seq
  rw [WP.block_append_iff, VG.Proof.Rc2.AArch64.keySave_eq]
  apply WP.mono (Spill.save_wp (by decide) (Spill.forall_slots writes))
  intro s₁ h₁
  obtain ⟨s₂, run₂, key₂, len₂, ptr₂, bits₂, zero₂, keep₂⟩ := VG.Proof.Rc2.AArch64.pinKey_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have scratchFrame : Frame [⟨s.gpr .x4, 512⟩] s.mem s₂.mem := by
    rw [keep₂.mem, h₁.mem]
    exact Spill.saveMem_frame_base (by decide) (by decide) _ _ _
  rw [h₁.gpr] at key₂ len₂ ptr₂ bits₂
  have rd₂ : s₂.rd = s.rd := keep₂.rd.trans h₁.rd
  have wr₂ : s₂.wr = s.wr := keep₂.wr.trans h₁.wr
  have r8₂ : s₂.gpr .x4 = s.gpr .x4 := (keep₂.reg .x4 (by decide)).trans (congrFun h₁.gpr .x4)
  have other₂ : ∀ r ∈ VG.Proof.Rc2.AArch64.coreRegs, r ≠ .x21 → s₂.gpr r = s.gpr r := by
    intro r hr hn
    have sep : ∀ r ∈ VG.Proof.Rc2.AArch64.coreRegs, r ≠ .x21 → r ∉ saved := by decide
    exact (keep₂.reg r (sep r hr hn)).trans (congrFun h₁.gpr r)
  have source₂ : Spec.Rc2.bytesAt s₂.mem (s₂.gpr .x19) (s.gpr .x1).toNat =
      Spec.Rc2.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat := by
    rw [key₂]
    exact VG.Proof.Rc2.AArch64.bytesAt_frame scratchFrame (by simpa using keyScratch) (by omega)
  have read₂ : ∀ i < (s.gpr .x1).toNat,
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x19 + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [rd₂, wr₂, key₂, hrd, hwr]
    exact ⟨⟨s.gpr .x0, (s.gpr .x1).toNat⟩, by simp,
      Offset.contains_base _ (by omega) (by omega)⟩
  have write₂ : ∀ i < 128, InRegions s₂.wr (s₂.gpr .x21 + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [wr₂, ptr₂, hwr]
    exact ⟨⟨s.gpr .x3, 128⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  apply WP.seq
  apply WP.mono (VG.Proof.Rc2.AArch64.expandCopyFill_ok s₂ (s.gpr .x1).toNat ht ht'
    (by simpa using len₂) zero₂ read₂ write₂ (by rw [key₂, ptr₂]; exact keyOut))
  intro s₃ h₃
  apply WP.seq
  have write₃ : ∀ i < 128, InRegions s₃.wr (s₃.gpr .x21 + BitVec.ofNat 64 i) 1 := by
    rw [h₃.1.wr, h₃.1.reg .x21 (by decide)]; exact write₂
  apply WP.mono (VG.Proof.Rc2.AArch64.expandReduce_ok s₃ _ (s.gpr .x2).toNat hb hb'
    (by simpa using (h₃.1.reg .x22 (by decide)).trans bits₂) write₃
    (by rw [h₃.1.reg .x21 (by decide)]; exact h₃.2))
  intro s₄ h₄
  have core := (CoreFrame.of_key h₃.1).trans h₄.1
  have outFrame : Frame [⟨s.gpr .x3, 128⟩] s₂.mem s₄.mem := by
    have h := core.mem
    rw [ptr₂] at h; exact h
  have r8₄ : s₄.gpr .x4 = s.gpr .x4 := (core.reg .x4 (by decide)).trans r8₂
  have other₄ : ∀ r ∈ VG.Proof.Rc2.AArch64.coreRegs, r ≠ .x21 → s₄.gpr r = s.gpr r := by
    intro r hr hn
    exact (core.reg r hr).trans (other₂ r hr hn)
  have rd₄ := core.rd.trans rd₂
  have wr₄ := core.wr.trans wr₂
  have expanded : BytesPrefix s₄.mem (s.gpr .x3)
      (Spec.Rc2.expandBytes (Spec.Rc2.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) (s.gpr .x2).toNat) 128 := by
    have h := h₄.2
    rw [h₃.1.reg .x21 (by decide), ptr₂, source₂] at h
    rw [expandBytes_eq]
    have length : (Spec.Rc2.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat).length = (s.gpr .x1).toNat := by
      simp [Spec.Rc2.bytesAt]
    rw [length]; exact h
  have scratchRead : ∀ i ∈ List.range 6,
      InRegions (s₄.rd ++ s₄.wr) (s₄.gpr .x4 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [rd₄, wr₄, r8₄, hrd, hwr]
    have bound := List.mem_range.mp hi
    exact ⟨⟨s.gpr .x4, 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have stored : ∀ i ∈ List.range 6,
      s₄.mem.readW (s₄.gpr .x4 + BitVec.ofNat 64 (8 * i)) 64 = s.gpr (VG.Proof.Rc2.AArch64.savedReg i) := by
    intro i hi
    have bound := List.mem_range.mp hi
    rw [r8₄, outFrame.readW (r := ⟨s.gpr .x4, 512⟩)
      (Offset.contains_base _ (by omega) (by omega)) (by simpa using outScratch.symm) (by decide),
      keep₂.mem, h₁.mem]
    exact Spill.saveMem_saved (l := Spill.slots VG.Proof.Rc2.AArch64.savedReg 6) (by decide) s.mem (s.gpr .x4) s.gpr
      (VG.Proof.Rc2.AArch64.savedReg i, 8 * i) (Spill.mem_slots bound)
  rw [VG.Proof.Rc2.AArch64.keyRestore_eq]
  apply WP.mono (Spill.restore_wp rfl (by decide) (by decide)
    (Spill.forall_slots fun i hi => scratchRead i (List.mem_range.mpr hi))
    (Spill.forall_slots fun i hi => stored i (List.mem_range.mpr hi)))
  intro s₅ h₅
  constructor
  · intro r hr
    by_cases hm : r ∈ (List.range 6).map VG.Proof.Rc2.AArch64.savedReg
    · exact h₅.gpr_of (.inl (by rwa [Spill.slots_fst]))
    · have covered : ∀ r ∈ preserved, r ∉ (List.range 6).map VG.Proof.Rc2.AArch64.savedReg →
          r ∈ VG.Proof.Rc2.AArch64.coreRegs ∧ r ≠ .x21 := by decide
      obtain ⟨hc, hn⟩ := covered r hr hm
      exact (h₅.other r (by rwa [Spill.slots_fst])).trans (other₄ r hc hn)
  · change Spec.Rc2.scheduleAt s₅.mem (s.gpr .x3) = _
    rw [h₅.mem]
    exact scheduleAt_expanded expanded

def keySatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 1 | .x2 => 8 | .x3 => 0x2000 | .x4 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 1⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 512⟩]

theorem key_correct (s : State) (hs : keyContract.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ keyContract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := VG.Proof.Rc2.AArch64.key_body_correct s hs
  exact ⟨t, s', he, ⟨ha, (VG.AArch64.Exec.regions he rfl).2.2.1, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

theorem publicRegs_five (s₁ s₂ : State) : PublicRegs [.x0, .x1, .x2, .x3, .x4] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 := by
  simp [PublicRegs]

theorem key_verified : Verified target expandKey (Spec.Rc2.expandKeyContract abi) := by
  refine Verified.of_correct VG.Proof.Rc2.AArch64.key_correct (expandKey_constantTime _) ?_
  sig_implies [Spec.Rc2.expandKeyContract, Spec.Rc2.expandKeySig, abi, argRegs,
    VG.Proof.Rc2.AArch64.keyContract, VG.Proof.Rc2.AArch64.publicRegs_five, Spec.Rc2.validKey] [keySatState] using VG.Proof.Rc2.AArch64.keySatState

end VG.Proof.Rc2.AArch64

end

end
