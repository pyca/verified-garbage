import VerifiedGarbage.Impl.Ed25519.X86.Comb
import VerifiedGarbage.Proof.Ed25519.X86.PointCTLit
import VerifiedGarbage.Proof.Ed25519.X86.PointCTSupport

/-! The comb has a public trace: its loops' counters (`esi`) are public, every address is the
workspace pointer `edi` plus a constant or `8 esi`, and the digits only reach masks.

The selection from the 32 tables (`combSelectFrom`) is most of the comb's code, 32 blocks of
immediates. Rather than have the kernel analyse each of their instructions, its analysis is
proven for any immediates (`selFrom_ok`): every instruction of a selection only moves an
immediate or a register into `eax`, `ebx`, `edx` or `ebp`, combines them with words at `edi`,
or stores them at `edi`, so `esi` and `edi` stay public. The rest of the comb is evaluated
(`taint_decide`), its parts joined with the taint `selL` (only `esi` and `edi` public) by the
rules of `Taint.check` (`CheckOk.seq`, `CheckOk.loop`). -/
namespace VG.Proof.Ed25519.X86

open VG VG.X86 VG.Impl.Ed25519.X86
open VG.Impl.X25519.X86 (sc)

/-! ## Joining checks -/

/-- The check of `c` from `τ` with the hint `h` succeeds, with a taint that satisfies `P`. -/
def CheckOk (τ : VG.X86.Taint.T) (c : Prog isa) (h : VG.Taint.Hint VG.X86.Taint.T) (P : VG.X86.Taint.T → Prop) :
    Prop :=
  ∃ τ', taint.check τ c h = some τ' ∧ P τ'

theorem CheckOk.of_map {τ : VG.X86.Taint.T} {c : Prog isa} {h : VG.Taint.Hint VG.X86.Taint.T}
    {p : VG.X86.Taint.T → Bool} (e : (taint.check τ c h).map p = some true) :
    CheckOk τ c h (p · = true) := by
  obtain ⟨τ', h₁, h₂⟩ := Option.map_eq_some_iff.mp e
  exact ⟨τ', h₁, h₂⟩

theorem CheckOk.seq {τ m : VG.X86.Taint.T} {c₁ c₂ : Prog isa} {h₁ h₂ : VG.Taint.Hint VG.X86.Taint.T}
    {P : VG.X86.Taint.T → Prop} (o₁ : CheckOk τ c₁ h₁ (taint.le m · = true)) (o₂ : CheckOk m c₂ h₂ P) :
    CheckOk τ (.seq c₁ c₂) (.seq m h₁ h₂) P := by
  obtain ⟨τ₁, e₁, l₁⟩ := o₁
  obtain ⟨τ₂, e₂, p₂⟩ := o₂
  refine ⟨τ₂, ?_, p₂⟩
  show (taint.check τ c₁ h₁).bind (fun τ' => if taint.le m τ' then taint.check m c₂ h₂ else none) =
    some τ₂
  simp only [e₁, Option.bind_some, l₁, ↓reduceIte, e₂]

theorem CheckOk.loop {τ σ : VG.X86.Taint.T} {body : Prog isa} {c : Cond} {h : VG.Taint.Hint VG.X86.Taint.T}
    {P : VG.X86.Taint.T → Prop} (hl : taint.le σ τ = true)
    (o : CheckOk σ body h fun σ' => taint.le σ σ' = true ∧ taint.condPub σ' c = true ∧ P σ') :
    CheckOk τ (.loop body c) (.loop σ h) P := by
  obtain ⟨σ', e, l, hc, p⟩ := o
  refine ⟨σ', ?_, p⟩
  show (if taint.le σ τ then (taint.check σ body h).bind fun σ' =>
    if taint.le σ σ' && taint.condPub σ' c then some σ' else none else none) = some σ'
  simp only [hl, ↓reduceIte, e, Option.bind_some, l, hc, Bool.and_self]

theorem CheckOk.ite {τ : VG.X86.Taint.T} {c : Cond} {t e : Prog isa} {h₁ h₂ : VG.Taint.Hint VG.X86.Taint.T}
    {P : VG.X86.Taint.T → Prop} (hc : taint.condPub τ c = true) (o₁ : CheckOk τ t h₁ P)
    (o₂ : CheckOk τ e h₂ P) (hm : ∀ a b, P a → P b → P (taint.meet a b)) :
    CheckOk τ (.ite c t e) (.ite h₁ h₂) P := by
  obtain ⟨τ₁, e₁, p₁⟩ := o₁
  obtain ⟨τ₂, e₂, p₂⟩ := o₂
  refine ⟨taint.meet τ₁ τ₂, ?_, hm _ _ p₁ p₂⟩
  show (if taint.condPub τ c then (taint.check τ t h₁).bind fun τ₁ =>
    (taint.check τ e h₂).map fun τ₂ => taint.meet τ₁ τ₂ else none) = some (taint.meet τ₁ τ₂)
  simp only [hc, ↓reduceIte, e₁, Option.bind_some, e₂, Option.map_some]

/-! ## The selection, for any immediates -/

/-- A taint that knows only which registers are public, and whether the flags are. -/
def selT (rs : RegSet Reg) (fl : Bool) : VG.X86.Taint.T := { regs := rs, flags := fl }

/-- The taint of the comb's loop: `esi` and `edi` public. -/
def selL : VG.X86.Taint.T := selT (.ofList [.esi, .edi]) false

/-- What a selection keeps: only registers known, `esi` and `edi` public. -/
def SelInv (τ : VG.X86.Taint.T) : Prop := ∃ rs fl, τ = selT rs fl ∧ Reg.esi ∈ rs ∧ Reg.edi ∈ rs

theorem subset_esi_edi {rs : RegSet Reg} (h₁ : Reg.esi ∈ rs) (h₂ : Reg.edi ∈ rs) :
    (RegSet.ofList [Reg.esi, .edi]).subset rs = true := by
  rw [RegSet.subset_eq, beq_iff_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  rw [RegSet.mem_iff] at h₁ h₂
  have hb : ∀ i < 8, (RegSet.ofList [Reg.esi, .edi]).bits.testBit i = true →
      i = RegIdx.idx Reg.esi ∨ i = RegIdx.idx Reg.edi := by decide
  cases hi : (RegSet.ofList [Reg.esi, .edi]).bits.testBit i
  · rfl
  · rcases Nat.lt_or_ge i 8 with h8 | h8
    · rcases hb i h8 hi with rfl | rfl
      · rw [h₁]; rfl
      · rw [h₂]; rfl
    · have : (RegSet.ofList [Reg.esi, .edi]).bits < 2 ^ i :=
        Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) h8)
      rw [Nat.testBit_lt_two_pow this] at hi
      cases hi

theorem SelInv.le {τ : VG.X86.Taint.T} (h : SelInv τ) {fl : Bool} (hf : fl = true → τ.flags = true) :
    taint.le (selT (.ofList [.esi, .edi]) fl) τ = true := by
  obtain ⟨rs, g, rfl, h₁, h₂⟩ := h
  show VG.X86.Taint.leK _ _ = true
  cases fl
  · simp only [VG.X86.Taint.leK, selT, subset_esi_edi h₁ h₂]; rfl
  · have hg : g = true := hf rfl
    subst hg
    simp only [VG.X86.Taint.leK, selT, subset_esi_edi h₁ h₂]; rfl

theorem SelInv.meet {a b : VG.X86.Taint.T} (ha : SelInv a) (hb : SelInv b) : SelInv (taint.meet a b) := by
  obtain ⟨ra, fa, rfl, ha₁, ha₂⟩ := ha
  obtain ⟨rb, fb, rfl, hb₁, hb₂⟩ := hb
  exact ⟨ra.inter rb, fa && fb, rfl, RegSet.mem_inter.mpr ⟨ha₁, hb₁⟩,
    RegSet.mem_inter.mpr ⟨ha₂, hb₂⟩⟩

/-- The instructions of a selection, for any immediates and displacements. -/
def SelInstr (i : Instr) : Prop :=
  (∃ x, i = .mov .eax (.imm x)) ∨ i = .mov .ebx (.imm 0) ∨ i = .mov .ebp (.imm 0) ∨
    i = .mov .edx (.reg .eax) ∨ (∃ o, i = .alu .and .eax (.mem (sc o))) ∨
    (∃ o, i = .alu .and .edx (.mem (sc o))) ∨ i = .alu .or .ebx (.reg .eax) ∨
    i = .alu .or .ebp (.reg .edx) ∨ (∃ o, i = .store (sc o) .ebx) ∨ (∃ o, i = .store (sc o) .ebp)

theorem setK_inv {rs : RegSet Reg} {fl p : Bool} {d : Reg} (hd₁ : d ≠ .esi) (hd₂ : d ≠ .edi)
    (h₁ : Reg.esi ∈ rs) (h₂ : Reg.edi ∈ rs) :
    Reg.esi ∈ VG.X86.Taint.setK (selT rs fl) d p ∧ Reg.edi ∈ VG.X86.Taint.setK (selT rs fl) d p := by
  cases p
  · exact ⟨RegSet.mem_erase.mpr ⟨hd₁.symm, h₁⟩, RegSet.mem_erase.mpr ⟨hd₂.symm, h₂⟩⟩
  · exact ⟨RegSet.mem_insert.mpr (Or.inr h₁), RegSet.mem_insert.mpr (Or.inr h₂)⟩

theorem step_sel {τ : VG.X86.Taint.T} {i : Instr} (hi : SelInstr i) (h : SelInv τ) :
    ∃ τ', taint.step τ i = some τ' ∧ SelInv τ' := by
  obtain ⟨rs, fl, rfl, h₁, h₂⟩ := h
  have hd : rs.mem .edi = true := h₂
  rcases hi with ⟨x, rfl⟩ | rfl | rfl | rfl | ⟨o, rfl⟩ | ⟨o, rfl⟩ | rfl | rfl | ⟨o, rfl⟩ | ⟨o, rfl⟩
  · exact ⟨_, rfl, _, _, rfl, setK_inv (d := .eax) (by decide) (by decide) h₁ h₂⟩
  · exact ⟨_, rfl, _, _, rfl, setK_inv (d := .ebx) (by decide) (by decide) h₁ h₂⟩
  · exact ⟨_, rfl, _, _, rfl, setK_inv (d := .ebp) (by decide) (by decide) h₁ h₂⟩
  · exact ⟨_, rfl, _, _, rfl, setK_inv (d := .edx) (by decide) (by decide) h₁ h₂⟩
  · have e : taint.step (selT rs fl) (.alu .and .eax (.mem (sc o))) =
        some (selT (VG.X86.Taint.setK (selT rs fl) .eax (VG.X86.Taint.pub (selT rs fl) .eax && false && true))
          (VG.X86.Taint.pub (selT rs fl) .eax && false && true)) := by
      show (bif true && rs.mem .edi then _ else none) = _
      rw [hd]; rfl
    exact ⟨_, e, _, _, rfl, setK_inv (d := .eax) (by decide) (by decide) h₁ h₂⟩
  · have e : taint.step (selT rs fl) (.alu .and .edx (.mem (sc o))) =
        some (selT (VG.X86.Taint.setK (selT rs fl) .edx (VG.X86.Taint.pub (selT rs fl) .edx && false && true))
          (VG.X86.Taint.pub (selT rs fl) .edx && false && true)) := by
      show (bif true && rs.mem .edi then _ else none) = _
      rw [hd]; rfl
    exact ⟨_, e, _, _, rfl, setK_inv (d := .edx) (by decide) (by decide) h₁ h₂⟩
  · exact ⟨_, rfl, _, _, rfl, setK_inv (d := .ebx) (by decide) (by decide) h₁ h₂⟩
  · exact ⟨_, rfl, _, _, rfl, setK_inv (d := .ebp) (by decide) (by decide) h₁ h₂⟩
  · refine ⟨selT rs fl, ?_, rs, fl, rfl, h₁, h₂⟩
    show (bif rs.mem .edi then _ else none) = _
    rw [hd]
    cases VG.X86.Taint.pub (selT rs fl) .ebx <;> rfl
  · refine ⟨selT rs fl, ?_, rs, fl, rfl, h₁, h₂⟩
    show (bif rs.mem .edi then _ else none) = _
    rw [hd]
    cases VG.X86.Taint.pub (selT rs fl) .ebp <;> rfl

theorem checkBlock_sel {is : List Instr} (hi : ∀ i ∈ is, SelInstr i) {τ : VG.X86.Taint.T}
    (h : SelInv τ) : ∃ τ', taint.checkBlock τ is = some τ' ∧ SelInv τ' := by
  induction is generalizing τ with
  | nil => exact ⟨τ, rfl, h⟩
  | cons i is ih =>
    obtain ⟨τ₁, e₁, h₁⟩ := step_sel (hi i (List.mem_cons_self ..)) h
    obtain ⟨τ₂, e₂, h₂⟩ := ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) h₁
    refine ⟨τ₂, ?_, h₂⟩
    show (taint.step τ i).bind (fun τ' => taint.checkBlock τ' is) = some τ₂
    rw [e₁, Option.bind_some, e₂]

theorem selectField_sel (vs : List Spec.X25519.Fe) (o e : Nat) :
    ∀ i ∈ selectField vs o e, SelInstr i := by
  intro i hi
  simp only [selectField, selectWord, List.mem_flatMap, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hi
  obtain ⟨w, -, hi⟩ := hi
  rcases hi with ((rfl | rfl) | ⟨k, -, hk⟩) | (rfl | rfl)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · unfold selectCand at hk
    split at hk
    · cases hk
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl ⟨_, rfl⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))))))))

theorem combSelect_sel (j : Nat) : ∀ i ∈ combSelect j, SelInstr i := by
  intro i hi
  simp only [combSelect, List.mem_append] at hi
  rcases hi with (h | h) | h <;> exact selectField_sel _ _ _ i h

/-- The hint of `combSelectFrom`: after each comparison, `esi`, `edi` and the flags public. -/
def selHint : List Nat → VG.Taint.Hint VG.X86.Taint.T
  | [] => .block []
  | _ :: js => .seq (selT (.ofList [.esi, .edi]) true) (.block []) (.ite (.block []) (selHint js))

theorem selFrom_ok (js : List Nat) {τ : VG.X86.Taint.T} (h : SelInv τ) :
    CheckOk τ (combSelectFrom js) (selHint js) SelInv := by
  induction js generalizing τ with
  | nil => exact ⟨τ, rfl, h⟩
  | cons j js ih =>
    obtain ⟨rs, fl, rfl, h₁, h₂⟩ := h
    have hc : SelInv (selT rs (rs.mem .esi && true && (!false || fl))) :=
      ⟨_, _, rfl, h₁, h₂⟩
    have hm : SelInv (selT (.ofList [.esi, .edi]) true) := ⟨_, _, rfl, by decide, by decide⟩
    refine CheckOk.seq ⟨_, rfl, hc.le fun _ => ?_⟩ ?_
    · show (rs.mem .esi && true && (!false || fl)) = true
      have : rs.mem .esi = true := h₁
      rw [this]; rfl
    · refine CheckOk.ite rfl ?_ (ih hm) fun _ _ => SelInv.meet
      obtain ⟨τ', e, h'⟩ := checkBlock_sel (combSelect_sel j) hm
      exact ⟨τ', e, h'⟩

/-! ## The comb -/

theorem combMultiply_check :
    ∃ h, (taint.check (regsTaint [.edi]) combMultiply h).isSome = true := by
  have init : CheckOk (regsTaint [.edi]) (.block combInit) _ (taint.le selL · = true) :=
    CheckOk.of_map (by taint_decide)
  have digits : CheckOk selL (.block combDigits) _ (taint.le selL · = true) :=
    CheckOk.of_map (by taint_decide)
  have addOdd : CheckOk selL (.block (combNeg 4 5 6 combOddSign ++ fieldCode addOddOps)) _
      (taint.le selL · = true) :=
    CheckOk.of_map (by taint_decide)
  have addEven : CheckOk selL (.block (combNeg 13 14 15 combEvenSign ++ fieldCode addEvenOps ++
      [.alu .add .esi (.imm 1), .alu .cmp .esi (.imm 32)])) _
      (fun σ => (taint.le selL σ && taint.condPub σ .ne) = true) :=
    CheckOk.of_map (by taint_decide)
  have finish : CheckOk selL combFinish _ (fun σ => (fun _ => true) σ = true) :=
    CheckOk.of_map (by taint_decide)
  have sel : CheckOk selL (combSelectFrom (List.range 32)) (selHint (List.range 32))
      (taint.le selL · = true) := by
    obtain ⟨τ, e, h⟩ := selFrom_ok (List.range 32) (τ := selL) ⟨_, _, rfl, by decide, by decide⟩
    exact ⟨τ, e, h.le nofun⟩
  obtain ⟨τ₁, e₁, hp⟩ := addEven
  rw [Bool.and_eq_true] at hp
  have body := digits.seq (sel.seq (addOdd.seq
    (P := fun σ' => taint.le selL σ' = true ∧ taint.condPub σ' .ne = true ∧ taint.le selL σ' = true)
    ⟨τ₁, e₁, hp.1, hp.2, hp.1⟩))
  obtain ⟨τ, e, -⟩ := init.seq ((CheckOk.loop (by decide) body).seq finish)
  exact ⟨_, Option.isSome_iff_exists.mpr ⟨τ, e⟩⟩

theorem combMultiply_ct : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi) combMultiply
    (fun _ _ => True) := by
  obtain ⟨_, hc⟩ := combMultiply_check
  apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ hc
  intro s t h
  exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ h)

end VG.Proof.Ed25519.X86
