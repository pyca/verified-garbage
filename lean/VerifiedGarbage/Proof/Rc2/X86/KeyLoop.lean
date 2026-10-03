import VerifiedGarbage.Proof.Rc2.X86.KeySteps

section

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

theorem fillKey_ok (s : State)
    (readLo : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi + s.gpr .ecx - 1)) 1)
    (readHi : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi + (s.gpr .ecx - s.gpr .esi))) 1)
    (writable : InRegions s.wr (addr32 (s.gpr .edi + s.gpr .ecx)) 1) :
    WP isa (.block fillKey) s (fun s' =>
      s'.gpr .ecx = s.gpr .ecx + 1 ∧
      zeroFlag s' = some ((s.gpr .ecx + 1 - 128) == 0) ∧
      Keep keyTemps {s with
        mem := s.mem.writeW (addr32 (s.gpr .edi + s.gpr .ecx))
          (Spec.Rc2.pi (s.mem (addr32 (s.gpr .edi + s.gpr .ecx - 1)) +
          s.mem (addr32 (s.gpr .edi + (s.gpr .ecx - s.gpr .esi)))))} s') := by
  rw [fillKey, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := fillInput_ok s readLo readHi
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  apply WP.mono (piLookup_ok s₁)
  intro s₂ h₂
  have k₁ : Keep keyTemps s s₁ := keep₁.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h <;> subst r <;> decide)
  have k₂ : Keep keyTemps s₁ s₂ := h₂.2.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h <;> subst r <;> decide)
  have keep := k₁.trans k₂
  have ptr := keep.reg .edi (by decide)
  have index := (keep₁.reg .ecx (by decide)).trans rfl
  have index₂ : s₂.gpr .ecx = s.gpr .ecx := (h₂.2.reg .ecx (by decide)).trans index
  have write₂ : InRegions s₂.wr (addr32 (s₂.gpr .edi + s₂.gpr .ecx)) 1 := by
    rw [keep.wr, ptr, index₂]; exact writable
  obtain ⟨s₃, run₃, out₃, flag₃, keep₃⟩ := fillOutput_ok s₂ write₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  refine ⟨by rw [out₃, index₂], by rw [flag₃, index₂], ?_⟩
  constructor
  · intro r hr
    exact (keep₃.reg r hr).trans (keep.reg r hr)
  · rw [keep₃.mem, keep.mem, ptr, index₂, h₂.1, out₁]
    simp [BitVec.setWidth_add]
  · exact keep₃.rd.trans keep.rd
  · exact keep₃.wr.trans keep.wr

theorem piStore_ok (s : State) (writable : InRegions s.wr (addr32 (s.gpr .edi + s.gpr .ecx)) 1) :
    WP isa (.block (piLookup ++ storeKey)) s (fun s' =>
      s'.gpr .ecx = s.gpr .ecx ∧
      Keep keyTemps {s with
        mem := s.mem.writeW (addr32 (s.gpr .edi + s.gpr .ecx)) (Spec.Rc2.pi ((s.gpr .eax).setWidth 8))} s') := by
  rw [WP.block_append_iff]
  apply WP.mono (piLookup_ok s)
  intro s₁ h₁
  have ptr := h₁.2.reg .edi (by decide)
  have index := h₁.2.reg .ecx (by decide)
  have valid : InRegions s₁.wr (addr32 (s₁.gpr .edi + s₁.gpr .ecx)) 1 := by
    rw [h₁.2.wr, ptr, index]; exact writable
  obtain ⟨s₂, run₂, index₂, keep₂⟩ := storeByte_ok s₁ valid
  refine WP.of_runBlock ⟨s₂, run₂, index₂.trans index, ?_⟩
  constructor
  · intro r hr
    rw [keep₂.reg r (by intro hm; simp only [List.mem_singleton] at hm; subst r; exact hr (by decide))]
    exact h₁.2.reg r (fun hm => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h <;> subst r <;> decide))
  · rw [keep₂.mem, h₁.2.mem, ptr, index, h₁.1]
    simp
  · exact keep₂.rd.trans h₁.2.rd
  · exact keep₂.wr.trans h₁.2.wr

theorem reduceKey_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi + s.gpr .ecx)) 1)
    (writable : InRegions s.wr (addr32 (s.gpr .edi + s.gpr .ecx)) 1) :
    WP isa (.block reduceKey) s (fun s' => s'.gpr .ecx = s.gpr .ecx ∧
      Keep keyTemps {s with
        mem := s.mem.writeW (addr32 (s.gpr .edi + s.gpr .ecx))
          (Spec.Rc2.pi (s.mem (addr32 (s.gpr .edi + s.gpr .ecx)) &&& (s.gpr .ebx).setWidth 8))} s') := by
  rw [reduceKey, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := reduceInput_ok s readable
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have ptr := keep₁.reg .edi (by decide)
  have index := keep₁.reg .ecx (by decide)
  have valid : InRegions s₁.wr (addr32 (s₁.gpr .edi + s₁.gpr .ecx)) 1 := by
    rw [keep₁.wr, ptr, index]; exact writable
  apply WP.mono (piStore_ok s₁ valid)
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
    (readLo : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi + (s.gpr .ecx - 1) + 1)) 1)
    (readHi : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi + (s.gpr .ecx - 1 + s.gpr .esi))) 1)
    (writable : InRegions s.wr (addr32 (s.gpr .edi + (s.gpr .ecx - 1))) 1) :
    WP isa (.block descendKey) s (fun s' =>
      s'.gpr .ecx = s.gpr .ecx - 1 ∧ zeroFlag s' = some ((s.gpr .ecx - 1) == 0) ∧
      Keep keyTemps {s with
        mem := s.mem.writeW (addr32 (s.gpr .edi + (s.gpr .ecx - 1)))
          (Spec.Rc2.pi (s.mem (addr32 (s.gpr .edi + (s.gpr .ecx - 1) + 1)) ^^^
            s.mem (addr32 (s.gpr .edi + (s.gpr .ecx - 1 + s.gpr .esi)))))} s') := by
  rw [descendKey, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, index₁, out₁, keep₁⟩ := descendInput_ok s readLo readHi
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have ptr := keep₁.reg .edi (by decide)
  have valid : InRegions s₁.wr (addr32 (s₁.gpr .edi + s₁.gpr .ecx)) 1 := by
    rw [keep₁.wr, ptr, index₁]; exact writable
  rw [← List.append_assoc, WP.block_append_iff]
  apply WP.mono (piStore_ok s₁ valid)
  intro s₂ h₂
  obtain ⟨s₃, run₃, flag₃, keep₃⟩ := cmpZero_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have index₂ := h₂.1.trans index₁
  refine ⟨(keep₃.reg .ecx (by decide)).trans index₂, by rw [flag₃, index₂], ?_⟩
  constructor
  · intro r hr
    exact ((keep₃.reg r (by simp)).trans (h₂.2.reg r hr)).trans (keep₁.reg r (fun hm => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h <;> subst r <;> decide)))
  · rw [keep₃.mem, h₂.2.mem, keep₁.mem, ptr, index₁, out₁]
    simp
  · exact keep₃.rd.trans (h₂.2.rd.trans keep₁.rd)
  · exact keep₃.wr.trans (h₂.2.wr.trans keep₁.wr)


end VG.Proof.Rc2.X86

end

/-! # A bounded loop rule and frame invariant for key expansion -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

theorem forwardLoop (body : Prog isa) (I : Nat → State → Prop) (stop : Nat)
    (step : ∀ i < stop, ∀ s, I i s → WP isa body s (fun s' =>
      I (i + 1) s' ∧ zeroFlag s' = some (decide (i + 1 = stop))))
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
    · simp only [eval_nonzero, h'.2, he, decide_true, Option.map_some, Bool.not_true]
    · rw [he] at h'
      exact h'.1
  · right
    constructor
    · simp only [eval_nonzero, h'.2, he, decide_false, Option.map_some, Bool.not_false]
    · exact ⟨stop - (j + 1), by omega, j + 1, by omega, rfl, h'.1⟩

/-- Across a key-expansion loop only the four temporaries and the schedule
buffer change. The key, scratch saves, and return address are separate. -/
structure KeyFrame (s₀ s : State) : Prop where
  reg : ∀ r, r ∉ keyTemps → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Frame [⟨addr32 (s₀.gpr .edi), 128⟩] s₀.mem s.mem

theorem KeyFrame.refl (s : State) : KeyFrame s s :=
  ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩

theorem KeyFrame.trans {s₀ s₁ s₂ : State} (h₁ : KeyFrame s₀ s₁) (h₂ : KeyFrame s₁ s₂) :
    KeyFrame s₀ s₂ := by
  refine ⟨fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, ?_⟩
  have frame₂ := h₂.mem
  rw [h₁.reg .edi (by decide)] at frame₂
  exact h₁.mem.trans frame₂

theorem KeyFrame.step {s₀ s s' : State} (h : KeyFrame s₀ s) (i : Nat) (hi : i < 128)
    (b : Byte) (keep : Keep keyTemps {s with mem := s.mem.writeW (addr32 (s₀.gpr .edi) + BitVec.ofNat 64 i) b} s') : KeyFrame s₀ s' := by
  refine ⟨fun r hr => (keep.reg r hr).trans (h.reg r hr), keep.rd.trans h.rd,
    keep.wr.trans h.wr, ?_⟩
  rw [keep.mem]
  exact h.mem.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))

theorem KeyFrame.keep {s₀ s s' : State} (h : KeyFrame s₀ s) (keep : Keep keyTemps s s') :
    KeyFrame s₀ s' := by
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

end VG.Proof.Rc2.X86
