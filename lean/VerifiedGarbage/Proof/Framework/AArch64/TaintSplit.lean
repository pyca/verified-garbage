import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.Framework.AArch64.TaintMono
import VerifiedGarbage.Proof.Framework.KernelList

/-!
# AArch64 taint tracking with statics: code without what the analysis does not read, in pieces

Untrusted: everything here is checked by Lean.

The kernel spends most of a constant-time check of unrolled field
arithmetic building the instructions and analysing each of them, though the
operations on the working space's slots differ only in offsets the analysis
(`taintS`) never reads. Two steps let it analyse each distinct operation once:

* `Code.eraseT` erases what `Taint.stepS` does not read (offsets, immediates,
  vector operations): the analysis of the erased code is the code's
  (`check_eraseT`), and the erased operations are the same code whatever
  their slots, which a proof shows once for any slots (`kernel_rfl`).
* A block whose list is a concatenation of pieces is analysed as a sequence
  of a block per piece (`Split`), the taint between them a literal of the
  hint: the kernel caches the analysis of each distinct piece from each
  taint. With more public between the pieces than the hint keeps, the
  block's analysis succeeds too, with more public after it (the analysis is
  monotone, `checkBlockS_mono`): `Split.le`.
-/

namespace VG.AArch64

/-! ## Erasing what the analysis does not read -/

/-- The instruction with everything the scalar analysis (`Taint.step`) does not read erased. -/
def Instr.eraseT : Instr → Instr
  | .movz sz d _ _ => .movz sz d 0 0
  | .movk sz d _ _ => .movk sz d 0 0
  | .ldr sz t n _ => .ldr sz t n 0
  | .str sz t n _ => .str sz t n 0
  | .ldrb t n _ => .ldrb t n 0
  | .strb t n _ => .strb t n 0
  | .addImm sz d n _ => .addImm sz d n 0
  | .subImm sz d n _ => .subImm sz d n 0
  | .lsl sz d n _ => .lsl sz d n 0
  | .lsr sz d n _ => .lsr sz d n 0
  | .ror sz d n _ => .ror sz d n 0
  | .vop _ => .vop (.movi0 .v0)
  | .ldrq _ n _ => .ldrq .v0 n 0
  | .strq _ n _ => .strq .v0 n 0
  | i => i

/-- The code with `Instr.eraseT` applied to every instruction. -/
def Code.eraseT : Prog isa → Prog isa
  | .block is => .block (is.map Instr.eraseT)
  | .seq a b => .seq (eraseT a) (eraseT b)
  | .ite c t e => .ite c (eraseT t) (eraseT e)
  | .loop b c => .loop (eraseT b) c
  | .call n b => .call n (eraseT b)
  | .frame p b q => .frame p (eraseT b) q

namespace Taint

theorem stepS_eraseT (L : List String) (τ : T) (i : Instr) : stepS L τ i.eraseT = stepS L τ i := by
  cases i <;> rfl

theorem stepS_mono {L : List String} {τ σ τ' : T} (i : Instr) (h : τ.subset σ = true)
    (hs : stepS L τ i = some τ') : ∃ σ', stepS L σ i = some σ' ∧ τ'.subset σ' = true := by
  unfold stepS at hs ⊢
  cases hi : i.sym with
  | none => simp only [hi] at hs; exact step_mono i h hs
  | some p =>
    obtain ⟨d, n⟩ := p
    simp only [hi] at hs
    by_cases hn : n ∈ L
    · simp only [hn, ↓reduceIte, Option.some.injEq] at hs ⊢
      subst hs
      exact ⟨_, rfl, set_mono h d id⟩
    · simp only [hn, ↓reduceIte] at hs ⊢
      exact step_mono i h hs

end Taint

section
variable {L : List String}

theorem checkBlockS_cons (τ : (taintS L).T) (i : Instr) (is : List Instr) :
    (taintS L).checkBlock τ (i :: is) = (Taint.stepS L τ i).bind fun τ' => (taintS L).checkBlock τ' is := rfl

theorem checkBlock_eraseT (τ : (taintS L).T) (is : List isa.Instr) :
    (taintS L).checkBlock τ (is.map Instr.eraseT) = (taintS L).checkBlock τ is := by
  induction is generalizing τ with
  | nil => rfl
  | cons i is ih =>
    show (Taint.stepS L τ i.eraseT).bind _ = (Taint.stepS L τ i).bind _
    exact congr (congrArg Option.bind (Taint.stepS_eraseT L τ i)) (funext ih)

theorem checkChunks_eraseT {chunkSize : Nat} (τ : (taintS L).T) (is : List isa.Instr)
    (ms : List (taintS L).T) :
    (taintS L).checkChunks chunkSize τ (is.map Instr.eraseT) ms = (taintS L).checkChunks chunkSize τ is ms := by
  induction ms generalizing τ is with
  | nil => exact checkBlock_eraseT τ is
  | cons m ms ih =>
    simp only [VG.Taint.checkChunks, KList.take_eq, KList.drop_eq, ← List.map_take, ← List.map_drop, ih]
    exact congrArg (Option.bind · _) (checkBlock_eraseT τ _)

theorem check_eraseT (τ : (taintS L).T) (c : Prog isa) (h : VG.Taint.Hint (taintS L).T) :
    (taintS L).check τ (Code.eraseT c) h = (taintS L).check τ c h := by
  induction c generalizing τ h with
  | block is => cases h <;> first | rfl | exact checkChunks_eraseT τ is _
  | seq a b iha ihb =>
    cases h <;> first | rfl | simp only [Code.eraseT, VG.Taint.check, iha, ihb]
  | ite c t e iht ihe =>
    cases h <;> first | rfl | simp only [Code.eraseT, VG.Taint.check, iht, ihe]
  | loop b c ih => cases h <;> first | rfl | simp only [Code.eraseT, VG.Taint.check, ih]
  | call n b ih => cases h <;> first | rfl | simp only [Code.eraseT, VG.Taint.check, ih]
  | frame p b q ih => cases h <;> first | rfl | simp only [Code.eraseT, VG.Taint.check, ih]

/-! ## Monotonicity -/

theorem checkBlockS_mono : ∀ (is : List Instr) {τ σ τ' : (taintS L).T}, τ.subset σ = true →
    (taintS L).checkBlock τ is = some τ' → ∃ σ', (taintS L).checkBlock σ is = some σ' ∧ τ'.subset σ' = true
  | [], _, _, _, h, hs => by cases hs; exact ⟨_, rfl, h⟩
  | i :: is, τ, σ, τ', h, hs => by
    rw [checkBlockS_cons] at hs ⊢
    cases e : Taint.stepS L τ i with
    | none => rw [e] at hs; cases hs
    | some τ₁ =>
      rw [e, Option.bind_some] at hs
      obtain ⟨σ₁, e', h₁⟩ := Taint.stepS_mono i h e
      rw [e', Option.bind_some]
      exact checkBlockS_mono is h₁ hs

theorem checkBlock_append {M : ISA} (A : VG.Taint M) (τ : A.T) (a b : List M.Instr) :
    A.checkBlock τ (a ++ b) = (A.checkBlock τ a).bind fun τ' => A.checkBlock τ' b := by
  induction a generalizing τ with
  | nil => rfl
  | cons i a ih =>
    show (A.step τ i).bind _ = ((A.step τ i).bind _).bind _
    cases A.step τ i with
    | none => rfl
    | some τ₁ => exact ih τ₁

/-- A check in chunks implies the check of the whole block, with as much public after it. -/
theorem checkChunksS_le {chunkSize : Nat} : ∀ (ms : List (taintS L).T) {τ : (taintS L).T} {is : List Instr}
    {r : (taintS L).T}, (taintS L).checkChunks chunkSize τ is ms = some r →
    ∃ r', (taintS L).checkBlock τ is = some r' ∧ r.subset r' = true
  | [], _, _, r, h => ⟨r, h, RegSet.subset_refl r⟩
  | m :: ms, τ, is, r, h => by
    simp only [VG.Taint.checkChunks, KList.take_eq, KList.drop_eq] at h
    cases e : (taintS L).checkBlock τ (is.take chunkSize) with
    | none => rw [e] at h; cases h
    | some τ₁ =>
      rw [e, Option.bind_some] at h
      split at h
      · rename_i hm
        obtain ⟨r₁, e₁, s₁⟩ := checkChunksS_le ms h
        obtain ⟨r₂, e₂, s₂⟩ := checkBlockS_mono _ hm e₁
        refine ⟨r₂, ?_, RegSet.subset_trans s₁ s₂⟩
        rw [← List.take_append_drop chunkSize is, checkBlock_append, e, Option.bind_some]
        exact e₂
      · cases h

/-! ## Blocks in pieces

The kernel analyses a block of instructions one by one, even where it
repeats a run of instructions it has analysed from the same taint (field
operations whose offsets were erased). Split into a block for each piece,
with the taint between them a literal of the hint, each distinct piece is
analysed once (`check` caches). With more public between the pieces than
the hint says, the block's own analysis succeeds too, with more public
(monotonicity): `Split.le`. -/

/-- The pieces as a sequence of blocks. -/
def piecesProg : List (List Instr) → Prog isa
  | [] => .block []
  | p :: ps => .seq (.block p) (piecesProg ps)

/-- `c'` is `c` with some of its blocks split into pieces. -/
inductive Split : Prog isa → Prog isa → Prop
  | refl (c : Prog isa) : Split c c
  | pieces (ps : List (List Instr)) : Split (.block ps.flatten) (piecesProg ps)
  | seq {a a' b b' : Prog isa} : Split a a' → Split b b' → Split (.seq a b) (.seq a' b')
  | loop {b b' : Prog isa} (c : Cond) : Split b b' → Split (.loop b c) (.loop b' c)

theorem check_block_le {τ r : (taintS L).T} {is : List Instr} {h : VG.Taint.Hint (taintS L).T}
    (hc : (taintS L).check τ (.block is) h = some r) :
    ∃ r', (taintS L).checkBlock τ is = some r' ∧ r.subset r' = true := by
  cases h with
  | block ms cs => exact checkChunksS_le ms hc
  | _ => cases hc

theorem pieces_le : ∀ (ps : List (List Instr)) {τ r : (taintS L).T} {h : VG.Taint.Hint (taintS L).T},
    (taintS L).check τ (piecesProg ps) h = some r →
    ∃ r', (taintS L).checkBlock τ ps.flatten = some r' ∧ r.subset r' = true
  | [], _, _, _, hc => check_block_le hc
  | p :: ps, τ, r, h, hc => by
    cases h with
    | seq mid h₁ h₂ =>
      simp only [piecesProg, VG.Taint.check] at hc
      cases e : (taintS L).check τ (.block p) h₁ with
      | none => rw [e] at hc; cases hc
      | some τ₁ =>
        rw [e, Option.bind_some] at hc
        split at hc
        · rename_i hm
          obtain ⟨τ₂, e₂, s₂⟩ := check_block_le e
          obtain ⟨r₁, e₃, s₃⟩ := pieces_le ps hc
          obtain ⟨r₂, e₄, s₄⟩ := checkBlockS_mono _ (RegSet.subset_trans hm s₂) e₃
          refine ⟨r₂, ?_, RegSet.subset_trans s₃ s₄⟩
          rw [List.flatten_cons, checkBlock_append, e₂, Option.bind_some]
          exact e₄
        · cases hc
    | _ => cases hc

theorem Split.le {c c' : Prog isa} (hs : Split c c') : ∀ {τ r : (taintS L).T} {h : VG.Taint.Hint (taintS L).T},
    (taintS L).check τ c' h = some r →
    ∃ h' r', (taintS L).check τ c h' = some r' ∧ r.subset r' = true := by
  induction hs with
  | refl c => exact fun hc => ⟨_, _, hc, RegSet.subset_refl _⟩
  | pieces ps =>
    intro τ r h hc
    obtain ⟨r', e, s⟩ := pieces_le ps hc
    exact ⟨.block [], r', e, s⟩
  | seq _ _ iha ihb =>
    intro τ r h hc
    cases h with
    | seq mid h₁ h₂ =>
      simp only [VG.Taint.check] at hc
      cases e : (taintS L).check τ _ h₁ with
      | none => rw [e] at hc; cases hc
      | some τ₁ =>
        rw [e, Option.bind_some] at hc
        split at hc
        · rename_i hm
          obtain ⟨h₁', τ₂, e₂, s₂⟩ := iha e
          obtain ⟨h₂', r', e₃, s₃⟩ := ihb hc
          refine ⟨.seq mid h₁' h₂', r', ?_, s₃⟩
          have hm' : (taintS L).le mid τ₂ = true := RegSet.subset_trans hm s₂
          simp only [VG.Taint.check, e₂, Option.bind_some, hm', ↓reduceIte]
          exact e₃
        · cases hc
    | _ => cases hc
  | loop c _ ih =>
    intro τ r h hc
    cases h with
    | loop σ hb =>
      simp only [VG.Taint.check] at hc
      split at hc
      · rename_i hσ
        cases e : (taintS L).check σ _ hb with
        | none => rw [e] at hc; cases hc
        | some σ₁ =>
          rw [e, Option.bind_some] at hc
          split at hc
          · rename_i hc'
            cases hc
            obtain ⟨hb', σ₂, e₂, s₂⟩ := ih e
            simp only [Bool.and_eq_true] at hc'
            refine ⟨.loop σ hb', σ₂, ?_, s₂⟩
            have h₂ : ((taintS L).le σ σ₂ && (taintS L).condPub σ₂ c) = true := by
              simp only [Bool.and_eq_true]
              exact ⟨RegSet.subset_trans hc'.1 s₂, Taint.condPub_mono c s₂ hc'.2⟩
            simp only [VG.Taint.check, hσ, ite_true, e₂, Option.bind_some, h₂]
          · cases hc
      · cases hc
    | _ => cases hc

/-- The analysis of `c` from that of `c'`, which is `c` with blocks split. -/
theorem Split.isSome {c c' : Prog isa} (hs : Split c c') {τ : (taintS L).T} {h : VG.Taint.Hint (taintS L).T}
    (hc : ((taintS L).check τ c' h).isSome = true) : ∃ h', ((taintS L).check τ c h').isSome = true := by
  obtain ⟨r, e⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨h', r', e', _⟩ := hs.le e
  exact ⟨h', by rw [e']; rfl⟩

/-- The analysis of `c` from that of `c'`, ending with at least `m` public. -/
theorem Split.map_le {c c' : Prog isa} (hs : Split c c') {τ m : (taintS L).T} {h : VG.Taint.Hint (taintS L).T}
    (hc : ((taintS L).check τ c' h).map ((taintS L).le m) = some true) :
    ∃ h', ((taintS L).check τ c h').map ((taintS L).le m) = some true := by
  cases e : (taintS L).check τ c' h with
  | none => rw [e] at hc; cases hc
  | some r =>
    rw [e, Option.map_some, Option.some.injEq] at hc
    obtain ⟨h', r', e', s⟩ := hs.le e
    exact ⟨h', by rw [e', Option.map_some]; exact congrArg some (RegSet.subset_trans hc s)⟩

theorem Split.exists_isSome {c c' : Prog isa} (hs : Split c c') {τ : (taintS L).T}
    (hc : ∃ h, ((taintS L).check τ c' h).isSome = true) : ∃ h', ((taintS L).check τ c h').isSome = true :=
  let ⟨_, e⟩ := hc; hs.isSome e

theorem Split.exists_map_le {c c' : Prog isa} (hs : Split c c') {τ m : (taintS L).T}
    (hc : ∃ h, ((taintS L).check τ c' h).map ((taintS L).le m) = some true) :
    ∃ h', ((taintS L).check τ c h').map ((taintS L).le m) = some true :=
  let ⟨_, e⟩ := hc; hs.map_le e

theorem exists_isSome_of_eraseT {τ : (taintS L).T} {c : Prog isa}
    (e : ∃ h, ((taintS L).check τ (Code.eraseT c) h).isSome = true) :
    ∃ h, ((taintS L).check τ c h).isSome = true := by
  simp only [check_eraseT] at e; exact e

theorem exists_map_le_of_eraseT {τ m : (taintS L).T} {c : Prog isa}
    (e : ∃ h, ((taintS L).check τ (Code.eraseT c) h).map ((taintS L).le m) = some true) :
    ∃ h, ((taintS L).check τ c h).map ((taintS L).le m) = some true := by
  simp only [check_eraseT] at e; exact e

theorem isSome_of_eraseT {τ : (taintS L).T} {c : Prog isa} {h : VG.Taint.Hint (taintS L).T}
    (e : ((taintS L).check τ (Code.eraseT c) h).isSome = true) : ((taintS L).check τ c h).isSome = true := by
  rw [← check_eraseT]; exact e

end

end VG.AArch64
