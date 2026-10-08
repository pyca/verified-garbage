import VerifiedGarbage.Proof.Bignum.X86_64.Mont

/-!
# A candidate on x86-64: constant time, the taint of a piece

The code keeps its public values (the lengths, the pointers, the counters)
in the header of the scratch space, and reloads them after every loop. The
taint analysis knows them public while they are *public slots*: `kT rs S`
says that `rdi` is the base of the scratch space (writable region 2, after
`out` and `used`) and that its header words `S` are public. A store of a
secret into the arrays forgets every slot, so the code is cut into pieces
there, and each piece starts from what correctness says about the header
(`HP`): two runs with the same public data (`Two`) agree on it.
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.Bignum.X86_64

/-- The taint of a piece: `rs` and `rdi` public, `rdi` the base of writable
region 2 (the scratch space), whose header words `S` are public. -/
def kT (rs : List Reg) (S : List Nat) : VG.X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.rdi]), flags := false, lens := [0, 8, 256], bases := [(.rdi, 2, 0)],
    slots := S.map fun j => (2, 8 * j, 8) }

/-- The writable regions: `out`, `used` (8 bytes) and the scratch space at
`B` (with at least its header), disjoint. -/
def KW (B : Addr) (wr : List Region) : Prop :=
  ∃ o u : Region, ∃ n : Nat, wr = [o, u, ⟨B, n⟩] ∧ 8 ≤ u.len ∧ 256 ≤ n ∧ wr.Pairwise Region.Disjoint ∧
    ∀ r ∈ wr, r.len ≤ 2 ^ 64

/-- What every piece knows of a state: `rdi` is `B`, the writable regions
are `wr`, and each header word `j` of `vs` holds its `x`. -/
structure HP (B : Addr) (wr : List Region) (vs : List (Nat × BitVec 64)) (s : State) : Prop where
  rdi : s.gpr .rdi = B
  wr : s.wr = wr
  hdr : ∀ e ∈ vs, word s.mem B (8 * e.1) = e.2

/-- Equal words have equal bytes. -/
theorem word_bytes {m₁ m₂ : Mem} {a : Addr} (h : m₁.readW a 64 = m₂.readW a 64) {j : Nat} (hj : j < 8) :
    m₁ (a + BitVec.ofNat 64 j) = m₂ (a + BitVec.ofNat 64 j) := by
  rw [← Mem.extractLsb'_read m₁ a hj, ← Mem.extractLsb'_read m₂ a hj]
  exact congrArg (BitVec.extractLsb' (8 * j) 8) h

theorem kT_agree {B : Addr} {wr : List Region} {vs : List (Nat × BitVec 64)} {rs : List Reg}
    {s₁ s₂ : State} (hk : KW B wr) (hS : ∀ e ∈ vs, e.1 < 32) (h₁ : HP B wr vs s₁) (h₂ : HP B wr vs s₂)
    (hr' : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : VG.X86_64.Taint.Agree (kT rs (vs.map (·.1))) s₁ s₂ := by
  obtain ⟨o, u, n, hw, hu, hn, hd, hl⟩ := hk
  have wf : ∀ {s : State}, HP B wr vs s → VG.X86_64.Taint.Wf (kT rs (vs.map (·.1))) s := fun h => by
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp => ?_⟩
    · rw [h.wr, hw]; exact .cons (Nat.zero_le _) (.cons hu (.cons hn .nil))
    · rw [h.wr]; exact hd
    · rw [h.wr]; exact hl
    · simp only [kT, List.mem_singleton] at hp; subst hp
      simp only [VG.X86_64.Taint.region, h.wr, hw, List.getD_cons_succ, List.getD_cons_zero]
      rw [h.rdi]; exact (BitVec.add_zero B).symm
  have hb : ∀ {s : State}, HP B wr vs s → ∀ k, VG.X86_64.Taint.byteAddr s 2 k = B + BitVec.ofNat 64 k := fun h k => by
    simp only [VG.X86_64.Taint.byteAddr, VG.X86_64.Taint.region, h.wr, hw, List.getD_cons_succ, List.getD_cons_zero]
  refine ⟨⟨fun r hr => ?_, fun hf => by cases hf⟩, fun _ => by rw [h₁.wr, h₂.wr], wf h₁, wf h₂,
    fun sl hsl => ?_, fun sl hsl k hk₁ hk₂ => ?_, VG.X86_64.Taint.noLo, VG.X86_64.Taint.noXr⟩
  · rcases List.mem_append.mp (RegSet.mem_ofList.mp hr) with h | h
    · exact hr' r h
    · simp only [List.mem_singleton] at h; subst h; rw [h₁.rdi, h₂.rdi]
  · simp only [kT, List.map_map, List.mem_map] at hsl
    obtain ⟨e, he, rfl⟩ := hsl
    have := hS e he
    simp only [kT, List.getD_cons_succ, List.getD_cons_zero, Function.comp]
    omega
  · simp only [kT, List.map_map, List.mem_map] at hsl
    obtain ⟨e, he, rfl⟩ := hsl
    simp only [Function.comp] at hk₁ hk₂ ⊢
    have ea : B + BitVec.ofNat 64 k = off B (8 * e.1) + BitVec.ofNat 64 (k - 8 * e.1) := by
      rw [off, VG.Offset.add_ofNat_add_ofNat]; congr 2; omega
    rw [hb h₁, hb h₂, ea]
    exact word_bytes ((h₁.hdr e he).trans (h₂.hdr e he).symm) (by omega)

/-- A piece the taint analysis checks from `kT rs S`, for runs that agree
on the public data. -/
theorem kt_ct {α : Type} {Φ : α → State → Prop} {c : Prog isa} (B : α → Addr) (wr : α → List Region)
    (S : List Nat) (vs : α → List (Nat × BitVec 64)) (rs : List Reg) (hS : ∀ j ∈ S, j < 32)
    (hvs : ∀ a, (vs a).map (·.1) = S)
    (hΦ : ∀ a s, Φ a s → KW (B a) (wr a) ∧ HP (B a) (wr a) (vs a) s) (hpin : Pins Φ rs)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (kT rs S) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  RelCT.taint (A := taint) (kT rs S) (fun _ _ ⟨a, h₁, h₂⟩ => by
    rw [← hvs a]
    exact kT_agree (hΦ a _ h₁).1 (fun e he => hS _ (by rw [← hvs a]; exact List.mem_map_of_mem he))
      (hΦ a _ h₁).2 (hΦ a _ h₂).2 (hpin a _ _ h₁ h₂)) h

/-- `kt_ct`, with what correctness gives after the piece. -/
theorem kt_piece {α : Type} {Φ Ψ : α → State → Prop} {c : Prog isa} (B : α → Addr) (wr : α → List Region)
    (S : List Nat) (vs : α → List (Nat × BitVec 64)) (rs : List Reg) (hS : ∀ j ∈ S, j < 32)
    (hvs : ∀ a, (vs a).map (·.1) = S)
    (hΦ : ∀ a s, Φ a s → KW (B a) (wr a) ∧ HP (B a) (wr a) (vs a) s) (hpin : Pins Φ rs)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T} (h : (taint.check (kT rs S) c hc).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) : RelCT isa (Two Φ) c (Two Ψ) :=
  two_post (kt_ct B wr S vs rs hS hvs hΦ hpin h) hw

theorem exec_seqs_app {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ []) {s s' : State} {t : List Leak}
    (e : Exec isa (seqs (a ++ b)) s t s') : Exec isa (.seq (seqs a) (seqs b)) s t s' := by
  induction a generalizing s t with
  | nil => exact absurd rfl ha
  | cons c a ih =>
    cases a with
    | nil =>
      obtain ⟨d, rest, rfl⟩ := List.exists_cons_of_ne_nil hb
      exact e
    | cons d rest =>
      change Exec isa (.seq c (seqs (d :: rest ++ b))) s t s' at e
      change Exec isa (.seq (.seq c (seqs (d :: rest))) (seqs b)) s t s'
      obtain ⟨t₁, t₂, s₁, rfl, e₁, e₂⟩ : ∃ t₁ t₂ s₁, t = t₁ ++ t₂ ∧ Exec isa c s t₁ s₁ ∧
          Exec isa (seqs (d :: rest ++ b)) s₁ t₂ s' := by
        cases e with
        | seq e₁ e₂ => exact ⟨_, _, _, rfl, e₁, e₂⟩
      obtain ⟨u₁, u₂, s₂, rfl, f₁, f₂⟩ : ∃ u₁ u₂ s₂, t₂ = u₁ ++ u₂ ∧ Exec isa (seqs (d :: rest)) s₁ u₁ s₂ ∧
          Exec isa (seqs b) s₂ u₂ s' := by
        cases ih (by simp) e₂ with
        | seq f₁ f₂ => exact ⟨_, _, _, rfl, f₁, f₂⟩
      rw [← List.append_assoc]
      exact .seq (.seq e₁ f₁) f₂

/-- A sequence in two parts. -/
theorem RelCT.seqs_app {P Q : State → State → Prop} {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ [])
    (h : RelCT isa P (.seq (seqs a) (seqs b)) Q) : RelCT isa P (seqs (a ++ b)) Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (exec_seqs_app ha hb e₁) (exec_seqs_app ha hb e₂)

/-- Two runs related with the same `a` are related with the same `b`. -/
theorem two_bind {α β : Type} {Φ : α → State → Prop} {Ψ : β → State → Prop}
    (f : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → ∃ b, Ψ b s₁ ∧ Ψ b s₂) {s₁ s₂ : State} (h : Two Φ s₁ s₂) :
    Two Ψ s₁ s₂ :=
  let ⟨a, h₁, h₂⟩ := h; f a s₁ s₂ h₁ h₂

/-- A branch followed by more code: each branch with what follows. -/
theorem RelCT.ite_seq {P Q : State → State → Prop} {c : isa.Cond} {t e k : Prog isa}
    (hc : ∀ s₁ s₂, P s₁ s₂ → isa.eval c s₁ = isa.eval c s₂)
    (ht : RelCT isa (fun s₁ s₂ => P s₁ s₂ ∧ isa.eval c s₁ = some true) (.seq t k) Q)
    (he : RelCT isa (fun s₁ s₂ => P s₁ s₂ ∧ isa.eval c s₁ = some false) (.seq e k) Q) :
    RelCT isa P (.seq (.ite c t e) k) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have hce := hc _ _ hp
  cases e₁ with
  | seq a₁ b₁ =>
    cases e₂ with
    | seq a₂ b₂ =>
      cases a₁ with
      | iteT c₁ x₁ =>
        cases a₂ with
        | iteT _ x₂ =>
          obtain ⟨ht', hq⟩ := ht _ _ _ _ _ _ ⟨hp, c₁⟩ (.seq x₁ b₁) (.seq x₂ b₂)
          exact ⟨by simpa using ht', hq⟩
        | iteF c₂ _ => rw [hce, c₂] at c₁; cases c₁
      | iteF c₁ x₁ =>
        cases a₂ with
        | iteT c₂ _ => rw [hce, c₂] at c₁; cases c₁
        | iteF _ x₂ =>
          obtain ⟨ht', hq⟩ := he _ _ _ _ _ _ ⟨hp, c₁⟩ (.seq x₁ b₁) (.seq x₂ b₂)
          exact ⟨by simpa using ht', hq⟩

/-- `RelCT.ite_seq` for runs that agree on the public data, which fixes the
condition. -/
theorem two_ite_seq {α : Type} {Φ : α → State → Prop} {cond : isa.Cond} {th el k : Prog isa}
    {Q : State → State → Prop}
    (hc : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → isa.eval cond s₁ = isa.eval cond s₂)
    (ht : RelCT isa (Two fun a s => Φ a s ∧ isa.eval cond s = some true) (.seq th k) Q)
    (he : RelCT isa (Two fun a s => Φ a s ∧ isa.eval cond s = some false) (.seq el k) Q) :
    RelCT isa (Two Φ) (.seq (.ite cond th el) k) Q := by
  refine RelCT.ite_seq (fun _ _ ⟨a, h₁, h₂⟩ => hc a _ _ h₁ h₂) (ht.mono ?_ fun _ _ h => h) (he.mono ?_ fun _ _ h => h)
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩

theorem pins_nil {α : Type} (Φ : α → State → Prop) : Pins Φ [] := fun _ _ _ _ _ _ hr => absurd hr (List.not_mem_nil)

/-- `HP` survives changes to the arrays alone (past the header). -/
theorem HP.frm {B : Addr} {wr : List Region} {vs : List (Nat × BitVec 64)} {s t : State} {rs : List (Nat × Nat)}
    (h : HP B wr vs s) (hf : Frm B rs s.mem t.mem) (hrs : ∀ r ∈ rs, 256 ≤ r.1) (hvs : ∀ e ∈ vs, e.1 < 32)
    (hdi : t.gpr .rdi = B) (hw : t.wr = s.wr) : HP B wr vs t :=
  ⟨hdi, hw.trans h.wr, fun e he => by
    have := hvs e he
    rw [hf.word_eq (fun r hr => Or.inl (by have := hrs r hr; omega)) (by omega)]; exact h.hdr e he⟩

/-- Header words survive changes away from them. -/
theorem hdr_frm {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} {vs : List (Nat × BitVec 64)} (hf : Frm B rs m m')
    (hd : ∀ e ∈ vs, e.1 < 32 ∧ ∀ r ∈ rs, 8 * e.1 + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * e.1)
    (h : ∀ e ∈ vs, word m B (8 * e.1) = e.2) : ∀ e ∈ vs, word m' B (8 * e.1) = e.2 := fun e he => by
  have := hd e he
  rw [hf.word_eq this.2 (by omega)]; exact h e he

end VG.Proof.RsaKeyGen.X86_64
