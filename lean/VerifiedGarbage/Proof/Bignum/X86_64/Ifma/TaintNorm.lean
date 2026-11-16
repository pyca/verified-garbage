module

public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase

/-!
# Taint tracking for x86-64: code as the steps the analysis makes

From a taint that knows no region bases and no public slots (`Taint.Plain`:
the registers alone, as `Taint.ofRegs`), which every step keeps so, `taint`
reads little of an instruction:

* of one that only writes vector registers, nothing;
* of a vector load, its address registers;
* of a store, its address registers: it leaves the taint as it is, as
  `ldmxcsr` does (the step of a store itself gives a taint whose slots are a
  term in the taint before and the operand, which the kernel never meets
  again, even for the same store from the same taint);
* of the integer instructions, not their displacements and immediates
  (`Instr.erase`).

`Instr.norm` is one instruction for each such step. Unrolled code whose
instructions differ in their vector registers and displacements (the IFMA
multiplications and the limb arithmetic around them) is then a few
instructions from a few taints, whose steps the kernel evaluates once:
`taint_normInv`, with `Taint.MapInv.check`, or `Taint.check_of_norm`.
-/

@[expose] public section

namespace VG.X86_64

/-- `Instr.norm`, as a `match`. -/
def Instr.normF : Instr → Instr
  | .vop _ | .zop _ | .eop _ | .e5op _ => .eop (.vpbroadcastq (.lo .xmm0) (.lo .xmm0))
  | .movdquLoad _ m | .vmovdquLoad _ _ m | .vbroadcasti128 _ m | .vbinLoad _ _ _ _ m | .vmovdqu32Load _ m
  | .vbroadcasti32x4 _ m | .vbroadcasti32x4H _ m | .zbcst _ _ _ m | .vpbroadcastdZ _ m | .zbcstd _ _ _ m
  | .vpmadd52Load _ _ _ m | .evLoad _ m | .evMadd52Load _ _ _ m | .evBroadcastLoad _ m
  | .e5InsertLoad _ _ m _ => .evLoad (.lo .xmm0) m.erase
  | .store m _ | .store32 m _ | .store8 m _ | .store16 m _ | .movdquStore m _ | .vmovdquStore _ m _
  | .vmovdqu32Store m _ | .evStore m _ | .e5ExtractStore m _ _ | .stmxcsr m => .ldmxcsr m.erase
  | i => i.erase

/-- An instruction on which `taint` makes the same step, from a taint that
knows no region bases and no public slots, with nothing left of what the
step does not read: one instruction for those that only write vector
registers, a load with its displacement zeroed for the vector loads,
`ldmxcsr` at the address with its displacement zeroed for the stores,
`Instr.erase` of the others. Its cases are closed (`inline_match%`), for the
kernel, which evaluates it at every instruction of the code. -/
def Instr.norm : Instr → Instr := inline_match% Instr.normF Instr.erase

theorem Instr.norm_eq (i : Instr) : i.norm = i.normF := by
  cases i with
  | mov d s => cases s <;> rfl
  | mov32 d s => cases s <;> rfl
  | alu op d s => cases s <;> rfl
  | alu32 op d s => cases s <;> rfl
  | mulx hi lo s => cases s <;> rfl
  | adcx d s => cases s <;> rfl
  | adox d s => cases s <;> rfl
  | cmov c d s => cases s <;> rfl
  | _ => rfl

namespace Taint

/-- The taint knows no region bases and no public slots. -/
def Plain (τ : T) : Prop := τ.bases = [] ∧ τ.slots = []

instance (τ : T) : Decidable (Plain τ) := inferInstanceAs (Decidable (_ ∧ _))

section
variable {τ : T}

/-- A store from such a taint leaves it as it is. -/
theorem storeStepKD_plain (h : Plain τ) (m : MemOp) (w : Nat) (p : Bool) :
    storeStepKD τ m w p = bif memPub τ m then some τ else none := by
  obtain ⟨rg, f, l, b, sl, lo, x⟩ := τ
  obtain ⟨rfl, rfl⟩ : b = [] ∧ sl = [] := h
  simp only [storeStepKD, storeSlotsKD, addrOfK_nil (τ := ⟨rg, f, l, [], [], lo, x⟩) rfl]
  cases p <;> rfl

theorem stepKD_normF (h : Plain τ) (i : Instr) : stepKD τ i.normF = stepKD τ i := by
  have st : ∀ m w p, stepKD τ (.ldmxcsr (MemOp.erase m)) = storeStepKD τ m w p := fun m w p =>
    (storeStepKD_plain h m w p).symm
  have key : i.normF = i.erase ∨ stepKD τ i.normF = stepKD τ i := by
    cases i with
    | vmovdquStore l m r => cases l <;> exact .inr (st _ _ _)
    | _ => first
      | exact .inl rfl
      | exact .inr rfl
      | exact .inr (st _ _ _)
  rcases key with e | e
  · rw [e]; exact stepKD_erase h.1 i
  · exact e

/-- A step keeps the slots empty (as `stepKD_nil` the bases). -/
theorem stepKD_slots_nil (h : Plain τ) {i : Instr} {τ' : T} (e : stepKD τ i = some τ') :
    τ'.slots = [] := by
  have hs : τ.slots = [] := h.2
  have st : ∀ {m : MemOp} {w : Nat} {p : Bool}, storeStepKD τ m w p = some τ' → τ'.slots = [] := fun e => by
    rw [storeStepKD_plain h] at e
    obtain ⟨-, rfl⟩ := some_cond e; exact hs
  have nx : (noX τ).slots = [] := hs
  cases i with
  | store m r | store32 m r | store8 m r | store16 m r | movdquStore m _ | vmovdqu32Store m _
  | evStore m _ | e5ExtractStore m _ _ | stmxcsr m => exact st e
  | vmovdquStore l m _ => cases l <;> exact st e
  | kStore m k _ | kStore8 m k _ =>
    simp only [stepKD, stepKDFn] at e
    cases hk : pub τ k <;> rw [hk] at e
    · cases e
    · exact st e
  | xop op => cases op <;> (cases e; exact hs)
  | push _ | callr _ | pop _ _ | alloc _ | free _ => cases e
  | _ => first
    | (cases e; first | exact hs | exact nx)
    | (obtain ⟨-, rfl⟩ := some_cond e; first | exact hs | exact nx)

theorem leK_slots_nil (h : τ.slots = []) {m : T} (hl : leK m τ = true) : m.slots = [] := by
  rw [leK_eq] at hl
  have hb : m.slots.all (τ.slots.contains ·) = true := by
    simp only [le, Bool.and_eq_true] at hl; exact hl.1.1.2
  rw [h] at hb
  cases e : m.slots with
  | nil => rfl
  | cons x _ => rw [e] at hb; cases hb

theorem meet_slots_nil {τ₁ τ₂ : T} (h : τ₁.slots = []) : (meet τ₁ τ₂).slots = [] := by
  simp only [meet, h, List.filter_nil, ite_self]

theorem callStep_slots_nil {τ' : T} (e : callStep τ = some τ') : τ'.slots = [] := by
  unfold callStep at e
  split at e <;> [skip; cases e]
  cases e; rfl

theorem retStep_slots_nil (h : τ.slots = []) {τ' : T} (e : retStep τ = some τ') : τ'.slots = [] := by
  unfold retStep at e
  split at e <;> [skip; cases e]
  cases e; exact h

end

end Taint

/-- `taint` makes the same step on an instruction and on `Instr.norm` of it,
from a taint that knows no region bases and no public slots. -/
theorem taint_normInv : taint.MapInv Instr.norm Taint.Plain where
  step i h := by
    rw [Instr.norm_eq]
    exact (taint_step _ _).trans ((Taint.stepKD_normF h i).trans (taint_step _ _).symm)
  step_P i h e := ⟨taint_eraseInv.step_P i h.1 e, Taint.stepKD_slots_nil h ((taint_step _ _).symm.trans e)⟩
  le_P h hl := ⟨taint_eraseInv.le_P h.1 hl, Taint.leK_slots_nil h.2 hl⟩
  meet_P h := ⟨taint_eraseInv.meet_P h.1, Taint.meet_slots_nil h.2⟩
  call_P h e := ⟨taint_eraseInv.call_P h.1 e, Taint.callStep_slots_nil e⟩
  ret_P h e := ⟨taint_eraseInv.ret_P h.1 e, Taint.retStep_slots_nil h.2 e⟩
  push_P _ _ e := by cases e
  pop_P _ _ e := by cases e

/-- The check of `c` from `τ`, which knows no region bases and no public
slots, is the check of `c'`, which is `c` with `Instr.norm` of its
instructions. -/
theorem Taint.check_of_norm {τ : Taint.T} {c c' : Prog isa} (hτ : Taint.Plain τ)
    (he : c.mapBlocks Instr.norm = c') {hc : VG.Taint.Hint Taint.T}
    (h : (taint.check τ c' hc).isSome = true) : (taint.check τ c hc).isSome = true := by
  have e := (taint_normInv.check c τ hc hτ).1
  rw [he] at e
  rw [← e]; exact h

/-- `Taint.check_of_norm`, from registers alone and for some hint. -/
theorem Taint.exists_check_of_norm {rs : List Reg} {c c' : Prog isa} (he : c.mapBlocks Instr.norm = c')
    (h : ∃ hc : VG.Taint.Hint Taint.T, (taint.check (Taint.ofRegs rs) c' hc).isSome = true) :
    ∃ hc : VG.Taint.Hint Taint.T, (taint.check (Taint.ofRegs rs) c hc).isSome = true :=
  let ⟨hc, h⟩ := h
  ⟨hc, Taint.check_of_norm ⟨rfl, rfl⟩ he h⟩

end VG.X86_64
