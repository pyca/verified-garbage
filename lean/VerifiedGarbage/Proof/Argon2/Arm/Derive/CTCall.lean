import VerifiedGarbage.Proof.Argon2.Arm.Derive.CTBase
import VerifiedGarbage.Proof.Argon2.Arm.HPrime.Verified

/-!
# Argon2 on ARMv7: two runs of the body

`Two s₀₁ s₀₂`: two runs of the derivation with the same public data.
`Two.leaf` relates a piece of the body the taint analysis proves, from the
public words of the locals (`slots_of_words`), and adds what each run
satisfies by correctness; `ccall_rel` and `hcall_rel` relate the calls of G
and H′, from their preconditions in both runs and their public arguments.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.Argon2.Arm (compressArm)

/-- Two runs of the derivation, with the same public data. -/
structure Two (s₀₁ s₀₂ : State) : Prop where
  hp₁ : DPre s₀₁
  hp₂ : DPre s₀₂
  pb : Pub2 s₀₁ s₀₂

namespace Pub2
variable {s₀₁ s₀₂ : State} (h : Pub2 s₀₁ s₀₂)
include h

theorem arg_eq {i : Nat} (hi : i < 18) : arg s₀₁ i = arg s₀₂ i := h.2 i hi
theorem memP_eq : memP s₀₁ = memP s₀₂ := h.2 13 (by decide)
theorem scrP_eq : scrP s₀₁ = scrP s₀₂ := h.2 15 (by decide)
theorem outP_eq : outP s₀₁ = outP s₀₂ := h.2 16 (by decide)
theorem outL_eq : outL s₀₁ = outL s₀₂ := by simp only [outL, h.2 17 (by decide)]
theorem blocksN_eq : blocksN s₀₁ = blocksN s₀₂ := by simp only [blocksN, h.2 14 (by decide)]
theorem lanesN_eq : lanesN s₀₁ = lanesN s₀₂ := by simp only [lanesN, h.2 7 (by decide)]
theorem itersN_eq : itersN s₀₁ = itersN s₀₂ := by simp only [itersN, h.2 5 (by decide)]

theorem prm_eq : prm s₀₁ = prm s₀₂ := by
  simp only [prm, kindV, itersN, mcostN, lanesN, outL, h.2 0 (by decide), h.2 5 (by decide),
    h.2 6 (by decide), h.2 7 (by decide), h.2 17 (by decide)]

end Pub2

/-- The slots `sl` of the locals hold the words `ws`. -/
theorem slots_of_words {s₀₁ s₀₂ s₁ s₂ : State} {ws : List Nat} {sl : List (Nat × Nat × Nat)}
    (hw : ∀ d ∈ ws, lw s₀₁ s₁ d = lw s₀₂ s₂ d)
    (hc : ∀ x ∈ sl, x.1 = 0 ∧ ∀ j < x.2.2, 4 * ((x.2.1 + j) / 4) ∈ ws) :
    ∀ x ∈ sl, x.1 = 0 ∧ ∀ k, x.2.1 ≤ k → k < x.2.1 + x.2.2 →
      lw s₀₁ s₁ (4 * (k / 4)) = lw s₀₂ s₂ (4 * (k / 4)) := by
  intro x hx
  obtain ⟨h0, hj⟩ := hc x hx
  refine ⟨h0, fun k h₁ h₂ => hw _ ?_⟩
  have := hj (k - x.2.1) (by omega)
  rwa [Nat.add_sub_cancel' h₁] at this

/-- A relation proved for each pair of related states. -/
theorem RelCT.of_eq {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ s₁ s₂, P s₁ s₂ → RelCT isa (fun a b => a = s₁ ∧ b = s₂) c Q) : RelCT isa P c Q :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => h s₁ s₂ hp s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

theorem execBlock_append (l₁ l₂ : List Instr) (s : State) :
    execBlock isa (l₁ ++ l₂) s = (execBlock isa l₁ s).bind fun p =>
      (execBlock isa l₂ p.1).map fun q => (q.1, p.2 ++ q.2) := by
  induction l₁ generalizing s with
  | nil => simp [execBlock]
  | cons i is ih =>
    simp only [List.cons_append, execBlock]
    split
    · rfl
    · rw [ih]
      cases execBlock isa is _ with
      | none => rfl
      | some p => simp [Function.comp_def, List.append_assoc]

/-- A block in two parts leaks as their sequence. -/
theorem RelCT.block_split {P Q : State → State → Prop} {l₁ l₂ : List Instr}
    (h : RelCT isa P (.seq (.block l₁) (.block l₂)) Q) : RelCT isa P (.block (l₁ ++ l₂)) Q := by
  have split : ∀ {s t s'}, Exec isa (.block (l₁ ++ l₂)) s t s' →
      Exec isa (.seq (.block l₁) (.block l₂)) s t s' := by
    intro s t s' e
    rw [Exec.block_iff, execBlock_append, Option.bind_eq_some_iff] at e
    obtain ⟨⟨s₁, t₁⟩, h₁, h₂⟩ := e
    rw [Option.map_eq_some_iff] at h₂
    obtain ⟨⟨s₂, t₂⟩, h₂, he⟩ := h₂
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact .seq (.block h₁) (.block h₂)
  exact fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (split e₁) (split e₂)

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- A piece of the body the taint analysis proves, from the slots `sl` of the
locals, which hold the words `ws`, public, and the registers `rs`. -/
theorem leaf {P : State → State → Prop} {c : Prog isa} (ws : List Nat) (sl : List (Nat × Nat × Nat))
    (rs : List Reg) (hok : VG.Arm.Taint.SlotsOk (τB sl rs))
    (hsl : ∀ x ∈ sl, x.1 = 0 ∧ ∀ j < x.2.2, 4 * ((x.2.1 + j) / 4) ∈ ws)
    (hag : ∀ s₁ s₂, P s₁ s₂ → Inv s₀₁ s₁ ∧ Inv s₀₂ s₂ ∧ (∀ d ∈ ws, lw s₀₁ s₁ d = lw s₀₂ s₂ d) ∧
      ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (VG.Taint.check taint (τB sl rs) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  refine RelCT.taintW (τB sl rs) (fun s₁ s₂ h => ?_) hc
  obtain ⟨i₁, i₂, hw, hr⟩ := hag s₁ s₂ h
  exact agreeB T.hp₁ T.hp₂ T.pb i₁ i₂ sl rs hr hok (slots_of_words hw hsl)

/-- A call of G: `compress(r0, r1, r2, r3)` to `scratch + o`, with the same
blocks in both runs. -/
theorem ccall_rel {o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 16384) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ →
      (Inv s₀₁ s₁ ∧ s₁.gpr .r3 = scrP s₀₁ ∧ s₁.gpr .r2 = scrP s₀₁ + BitVec.ofNat 32 o ∧
        GArg s₀₁ o (s₁.gpr .r0) ∧ GArg s₀₁ o (s₁.gpr .r1)) ∧
      (Inv s₀₂ s₂ ∧ s₂.gpr .r3 = scrP s₀₂ ∧ s₂.gpr .r2 = scrP s₀₂ + BitVec.ofNat 32 o ∧
        GArg s₀₂ o (s₂.gpr .r0) ∧ GArg s₀₂ o (s₂.gpr .r1)) ∧
      s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1) :
    RelCT isa P Impl.Argon2.Arm.Derive.compressCall fun _ _ => True := by
  refine RelCT.of_eq fun s₁ s₂ hP => ?_
  obtain ⟨⟨i₁, d₁, c₁, x₁, y₁⟩, ⟨i₂, d₂, c₂, x₂, y₂⟩, ea, es⟩ := h s₁ s₂ hP
  obtain ⟨p₁, v₁, w₁⟩ := ccall_pre T.hp₁ i₁ d₁ ho ho' c₁ x₁ y₁
  obtain ⟨p₂, v₂, w₂⟩ := ccall_pre T.hp₂ i₂ d₂ ho ho' c₂ x₂ y₂
  have eR : cRd s₂ = cRd s₁ := by simp only [cRd, ea, es]
  have eW : cWr s₀₂ o = cWr s₀₁ o := by simp only [cWr, scrB, T.pb.scrP_eq]
  rw [eR, eW] at p₂ v₂
  rw [eW] at w₂
  unfold Impl.Argon2.Arm.Derive.compressCall
  refine RelCT.call (k := compressArm) Proof.Argon2.Arm.compress_verified'.1 Proof.Argon2.Arm.compress_ct
    (cRd s₁) (cWr s₀₁ o) fun a b ⟨ha, hb⟩ => ?_
  subst a b
  refine ⟨p₁, p₂, ?_, v₁, w₁, v₂, w₂⟩
  simp only [compressArm, State.withRegions_gpr,
    State.callEntry_gpr _ (show Reg.r0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.r2 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide)]
  exact ⟨ea, es, by rw [c₁, c₂, T.pb.scrP_eq], by rw [d₁, d₂, T.pb.scrP_eq]⟩

/-- A call of H′: `hprime(r0, r1, r2, r3, r12)`, with the same arguments in
both runs. -/
theorem hcall_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ →
      (Inv s₀₁ s₁ ∧ s₁.gpr .r12 = scrP s₀₁ ∧
        (∃ R ∈ [memR s₀₁, locR s₀₁], ∃ off, State.addr (s₁.gpr .r0) = R.base + BitVec.ofNat 64 off ∧
          off + (s₁.gpr .r1).toNat ≤ R.len) ∧ (s₁.gpr .r0).toNat + (s₁.gpr .r1).toNat ≤ 2 ^ 32 ∧
        (∃ R ∈ [memR s₀₁, outR s₀₁], ∃ off, State.addr (s₁.gpr .r2) = R.base + BitVec.ofNat 64 off ∧
          off + (s₁.gpr .r3).toNat ≤ R.len) ∧ (s₁.gpr .r2).toNat + (s₁.gpr .r3).toNat ≤ 2 ^ 32 ∧
        1 ≤ (s₁.gpr .r3).toNat) ∧
      (Inv s₀₂ s₂ ∧ s₂.gpr .r12 = scrP s₀₂ ∧
        (∃ R ∈ [memR s₀₂, locR s₀₂], ∃ off, State.addr (s₂.gpr .r0) = R.base + BitVec.ofNat 64 off ∧
          off + (s₂.gpr .r1).toNat ≤ R.len) ∧ (s₂.gpr .r0).toNat + (s₂.gpr .r1).toNat ≤ 2 ^ 32 ∧
        (∃ R ∈ [memR s₀₂, outR s₀₂], ∃ off, State.addr (s₂.gpr .r2) = R.base + BitVec.ofNat 64 off ∧
          off + (s₂.gpr .r3).toNat ≤ R.len) ∧ (s₂.gpr .r2).toNat + (s₂.gpr .r3).toNat ≤ 2 ^ 32 ∧
        1 ≤ (s₂.gpr .r3).toNat) ∧
      s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
        s₁.gpr .r3 = s₂.gpr .r3) :
    RelCT isa P Impl.Argon2.Arm.Derive.hPrimeCall fun _ _ => True := by
  unfold Impl.Argon2.Arm.Derive.hPrimeCall
  refine RelCT.of_eq fun s₁ s₂ hP => ?_
  obtain ⟨⟨i₁, d₁, n₁, nf₁, o₁, of₁, l₁⟩, ⟨i₂, d₂, n₂, nf₂, o₂, of₂, l₂⟩, e0, e1, e2, e3⟩ := h s₁ s₂ hP
  have hsp : s₁.sp = s₂.sp := by rw [i₁.sp, i₂.sp, T.pb.E]
  obtain ⟨p₁, v₁, w₁⟩ := hcall_pre T.hp₁ i₁ d₁ n₁ nf₁ o₁ of₁ l₁
  obtain ⟨p₂, v₂, w₂⟩ := hcall_pre T.hp₂ i₂ d₂ n₂ nf₂ o₂ of₂ l₂
  have eR : hRd s₂ = hRd s₁ := by simp only [hRd, e0, e1, hsp]
  have eW : hWr s₀₂ s₂ = hWr s₀₁ s₁ := by simp only [hWr, e2, e3, scrR, scrP, T.pb.scrP_eq]
  rw [eR, eW] at p₂ v₂
  rw [eW] at w₂
  have hn₁ : 4 * hregs.length ≤ s₁.sp.toNat := by
    have := T.hp₁.sp_lo
    simp only [List.length_cons, List.length_nil]; rw [i₁.sp, E_nat T.hp₁]; omega
  have hn₂ : 4 * hregs.length ≤ s₂.sp.toNat := by rw [← hsp]; exact hn₁
  refine frameCall_rel (rs := hregs) (t := .r12) (by decide) (k := HPrime.hPrimeArm) HPrime.hPrime_verified.1
    HPrime.hPrime_verified.2.1 (hRd s₁) (hWr s₀₁ s₁) fun a b ⟨ha, hb⟩ => ?_
  subst a b
  refine ⟨hsp, p₁, p₂, ⟨by simp [hsp], ?_, ?_, ?_, ?_, ?_⟩, v₁, w₁, v₂, w₂⟩
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r0 ∉ linkRegs by decide), pushed_gpr, e0]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r1 ∉ linkRegs by decide), pushed_gpr, e1]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r2 ∉ linkRegs by decide), pushed_gpr, e2]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), pushed_gpr, e3]
  · exact VG.Proof.Argon2.Arm.pushed_arg_eq hn₁ hn₂ (i := 0) (by decide)
      (by show s₁.gpr .r12 = s₂.gpr .r12; rw [d₁, d₂, T.pb.scrP_eq])

end Two

end VG.Proof.Argon2.Arm.Derive
