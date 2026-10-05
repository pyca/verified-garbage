import VerifiedGarbage.Proof.Framework.Arm.Taint

/-!
# Taint tracking for ARMv7: code without its offsets

From a taint that knows no region bases and no stack arguments (`NoBase`, as
`Taint.ofRegs`), the analysis never knows a region base, so it reads neither
the offsets of loads and stores nor the immediates of `movw`: it checks code
with them zeroed (`Code.eraseOff`) exactly as the code itself
(`check_eraseOff`). Field arithmetic on slots of a working space (e.g. X448's
multiplication, `Impl/X448/Arm.lean`) differs between its copies only in
those offsets: without them the copies are equal, and the kernel, which
caches the analysis of the same code from the same taint, analyses one copy
(`constantTime_eraseOff_of_eq`, with the code without its offsets written out
as a literal, whose copies are then equal terms).
-/

namespace VG.Arm

/-- The instruction with the offset of a load or store from a register, or
the immediate of a `movw`, zeroed. -/
def Instr.eraseOff : Instr → Instr
  | .ldr t n _ => .ldr t n 0
  | .str t n _ => .str t n 0
  | .ldrb t n _ => .ldrb t n 0
  | .strb t n _ => .strb t n 0
  | .movw d _ => .movw d 0
  | i => i

/-- The code with the offsets of its loads and stores from registers, and
the immediates of its `movw`, zeroed. -/
def Code.eraseOff : Prog isa → Prog isa
  | .block is => .block (is.map Instr.eraseOff)
  | .seq a b => .seq (eraseOff a) (eraseOff b)
  | .ite c t e => .ite c (eraseOff t) (eraseOff e)
  | .loop b c => .loop (eraseOff b) c
  | .call n b => .call n (eraseOff b)
  | .frame p b q => .frame p (eraseOff b) q

namespace Taint

/-- The taint knows no region base and no stack arguments. -/
def NoBase (τ : T) : Prop := τ.bases = [] ∧ τ.argLen = 0

theorem noBase_ofRegs (rs : List Reg) : NoBase (ofRegs rs) := ⟨rfl, rfl⟩

theorem step_eraseOff {τ : T} (h : NoBase τ) (i : Instr) :
    stepKD τ i.eraseOff = stepKD τ i := by
  obtain ⟨regs, flags, lens, bases, slots, argLen, argBases⟩ := τ
  obtain ⟨rfl, rfl⟩ := h
  cases i <;> rfl

theorem step_noBase {τ τ' : T} (h : NoBase τ) {i : Instr} (hs : stepKD τ i = some τ') :
    NoBase τ' := by
  obtain ⟨regs, flags, lens, bases, slots, argLen, argBases⟩ := τ
  obtain ⟨rfl, rfl⟩ := h
  cases i <;> simp only [stepKD, storeStepKD, Bool.cond_eq_ite] at hs <;>
    first
    | (cases hs; exact ⟨rfl, rfl⟩)
    | (cases hs; exact ⟨by rename_i o; cases o <;> rfl, rfl⟩)
    | (split at hs <;> cases hs; exact ⟨rfl, rfl⟩)
    | cases hs

theorem le_noBase {m σ : T} (hl : leK m σ = true) (h : NoBase σ) : NoBase m := by
  obtain ⟨regs, flags, lens, bases, slots, argLen, argBases⟩ := m
  obtain ⟨hb, ha⟩ := h
  simp only [leK, Bool.and_eq_true] at hl
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hbs⟩, -⟩, hal⟩, -⟩ := hl
  refine ⟨?_, ?_⟩
  · cases bases with
    | nil => rfl
    | cons b bs =>
      simp only [KList.all_eq, List.all_cons, Bool.and_eq_true, memB_eq, hb] at hbs
      cases hbs.1
  · exact (Nat.eq_of_beq_eq_true hal).trans ha

theorem meet_noBase {τ₁ τ₂ : T} (h : NoBase τ₁) : NoBase (meet τ₁ τ₂) := by
  refine ⟨by simp [meet, h.1], ?_⟩
  simp only [meet, h.2]
  split <;> rfl

theorem callStep_noBase {τ : T} (h : NoBase τ) : NoBase (callStep τ) := by
  refine ⟨by simp [callStep, h.1], h.2⟩

private theorem bind_congr {α β : Type} {o : Option α} {f g : α → Option β}
    (h : ∀ a, o = some a → f a = g a) : o.bind f = o.bind g := by
  cases o with
  | none => rfl
  | some a => exact h a rfl

theorem checkBlock_noBase {τ τ' : T} (h : NoBase τ) {is : List Instr}
    (hc : taint.checkBlock τ is = some τ') : NoBase τ' := by
  induction is generalizing τ with
  | nil => cases hc; exact h
  | cons i is ih =>
    have hc : (stepKD τ i).bind (taint.checkBlock · is) = some τ' := hc
    obtain ⟨σ, hσ, hc⟩ := Option.bind_eq_some_iff.mp hc
    exact ih (step_noBase h hσ) hc

theorem checkBlock_eraseOff {τ : T} (h : NoBase τ) (is : List Instr) :
    taint.checkBlock τ (is.map Instr.eraseOff) = taint.checkBlock τ is := by
  induction is generalizing τ with
  | nil => rfl
  | cons i is ih =>
    show (stepKD τ i.eraseOff).bind (taint.checkBlock · _) = (stepKD τ i).bind (taint.checkBlock · _)
    rw [step_eraseOff h]
    exact bind_congr fun σ hσ => ih (step_noBase h hσ)

theorem checkChunks_noBase {τ τ' : T} (h : NoBase τ) {is : List Instr} {ms : List T}
    (hc : taint.checkChunks τ is ms = some τ') : NoBase τ' := by
  induction ms generalizing τ is with
  | nil => exact checkBlock_noBase h hc
  | cons m ms ih =>
    have hc : (taint.checkBlock τ (is.take VG.Taint.chunk)).bind (fun τ' =>
        if taint.le m τ' then taint.checkChunks m (is.drop VG.Taint.chunk) ms else none) = some τ' := hc
    obtain ⟨σ, hσ, hc⟩ := Option.bind_eq_some_iff.mp hc
    split at hc
    · rename_i hl
      exact ih (le_noBase hl (checkBlock_noBase h hσ)) hc
    · cases hc

theorem checkChunks_eraseOff {τ : T} (h : NoBase τ) (is : List Instr) (ms : List T) :
    taint.checkChunks τ (is.map Instr.eraseOff) ms = taint.checkChunks τ is ms := by
  induction ms generalizing τ is with
  | nil => exact checkBlock_eraseOff h is
  | cons m ms ih =>
    simp only [VG.Taint.checkChunks, ← List.map_take, ← List.map_drop, checkBlock_eraseOff h]
    refine bind_congr fun σ hσ => ?_
    split
    · rename_i hl
      exact ih (le_noBase hl (checkBlock_noBase h hσ)) _
    · rfl

theorem check_noBase : ∀ (c : Prog isa) {τ τ' : T} {hc : VG.Taint.Hint taint.T}, NoBase τ →
    taint.check τ c hc = some τ' → NoBase τ'
  | .block is, τ, τ', hc, h, e => by
    cases hc <;> first | exact checkChunks_noBase h e | cases e
  | .seq a b, τ, τ', hc, h, e => by
    cases hc with
    | seq mid h₁ h₂ =>
      have e : (taint.check τ a h₁).bind (fun τ' =>
          if taint.le mid τ' then taint.check mid b h₂ else none) = some τ' := e
      obtain ⟨σ, hσ, e⟩ := Option.bind_eq_some_iff.mp e
      split at e
      · rename_i hl
        exact check_noBase b (le_noBase hl (check_noBase a h hσ)) e
      · cases e
    | _ => cases e
  | .ite c t f, τ, τ', hc, h, e => by
    cases hc with
    | ite h₁ h₂ =>
      have e : (if taint.condPub τ c then
          (taint.check τ t h₁).bind fun τ₁ => (taint.check τ f h₂).map fun τ₂ => taint.meet τ₁ τ₂
          else none) = some τ' := e
      split at e
      · obtain ⟨σ₁, hσ₁, e⟩ := Option.bind_eq_some_iff.mp e
        obtain ⟨σ₂, -, rfl⟩ := Option.map_eq_some_iff.mp e
        exact meet_noBase (check_noBase t h hσ₁)
      · cases e
    | _ => cases e
  | .loop body c, τ, τ', hc, h, e => by
    cases hc with
    | loop σ hb =>
      have e : (if taint.le σ τ then
          (taint.check σ body hb).bind fun σ' => if taint.le σ σ' && taint.condPub σ' c then some σ'
            else none
          else none) = some τ' := e
      split at e
      · rename_i hl
        obtain ⟨σ', hσ', e⟩ := Option.bind_eq_some_iff.mp e
        split at e
        · cases e; exact check_noBase body (le_noBase hl h) hσ'
        · cases e
      · cases e
    | _ => cases e
  | .call n body, τ, τ', hc, h, e => by
    cases hc with
    | call hb =>
      have e : (taint.check (callStep τ) body hb).bind (fun τ₂ => some τ₂) = some τ' := e
      obtain ⟨σ', hσ', e⟩ := Option.bind_eq_some_iff.mp e
      cases e
      exact check_noBase body (callStep_noBase h) hσ'
    | _ => cases e
  | .frame p body q, τ, τ', hc, h, e => by
    cases hc with
    | frame hb => cases e
    | _ => cases e

theorem check_eraseOff : ∀ (c : Prog isa) {τ : T} (hc : VG.Taint.Hint taint.T), NoBase τ →
    taint.check τ (Code.eraseOff c) hc = taint.check τ c hc
  | .block is, τ, hc, h => by
    cases hc <;> first | rfl | exact checkChunks_eraseOff h is _
  | .seq a b, τ, hc, h => by
    cases hc with
    | seq mid h₁ h₂ =>
      show (taint.check τ (Code.eraseOff a) h₁).bind _ = (taint.check τ a h₁).bind _
      rw [check_eraseOff a h₁ h]
      refine bind_congr fun σ hσ => ?_
      split
      · rename_i hl
        exact check_eraseOff b h₂ (le_noBase hl (check_noBase a h hσ))
      · rfl
    | _ => rfl
  | .ite c t f, τ, hc, h => by
    cases hc with
    | ite h₁ h₂ =>
      show (if taint.condPub τ c then (taint.check τ (Code.eraseOff t) h₁).bind fun τ₁ =>
          (taint.check τ (Code.eraseOff f) h₂).map fun τ₂ => taint.meet τ₁ τ₂ else none) = _
      rw [check_eraseOff t h₁ h, check_eraseOff f h₂ h]; rfl
    | _ => rfl
  | .loop body c, τ, hc, h => by
    cases hc with
    | loop σ hb =>
      show (if taint.le σ τ then _ else none) = (if taint.le σ τ then _ else none)
      split
      · rename_i hl
        rw [check_eraseOff body hb (le_noBase hl h)]
      · rfl
    | _ => rfl
  | .call n body, τ, hc, h => by
    cases hc with
    | call hb =>
      show ((some (callStep τ)).bind fun τ₁ => (taint.check τ₁ (Code.eraseOff body) hb).bind taint.ret) =
        (some (callStep τ)).bind fun τ₁ => (taint.check τ₁ body hb).bind taint.ret
      rw [Option.bind_some, Option.bind_some, check_eraseOff body hb (callStep_noBase h)]
    | _ => rfl
  | .frame p body q, τ, hc, h => by
    cases hc <;> rfl

end Taint

/-- Constant time from the analysis of code `c'` that is `c` without its
offsets (e.g. with copies that differ only in offsets made equal), from a
taint that knows no region bases. -/
theorem Taint.constantTime_eraseOff_of_eq {Pre : State → Prop} {Pub : State → State → Prop}
    {c c' : Prog isa} (τ : taint.T) (hτ : Taint.NoBase τ)
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → taint.Agree τ s₁ s₂)
    (he : Code.eraseOff c = c') {hc : VG.Taint.Hint taint.T}
    (h : (taint.check τ c' hc).isSome = true) : ConstantTime isa Pre Pub c :=
  VG.Taint.constantTime (A := taint) τ hpub (hc := hc)
    (Taint.check_eraseOff c hc hτ ▸ he ▸ h)

end VG.Arm
