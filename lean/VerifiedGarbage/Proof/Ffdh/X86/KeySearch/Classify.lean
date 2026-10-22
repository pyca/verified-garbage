module

public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Call
public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Exits
import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Entry

/-! # After an attempt (x86)

`classify` consumes the attempt's `p_len` octets (`advance_ok`) and, by its
status, finishes the search with the key pair, or counts a rejection and
asks the loop for another attempt (`classify_ok`): the search from there
ends as the search from before the attempt does (`Same`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeySearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.KeySearch
open VG.Proof.Ffdh.KeyGeneration
open VG.Proof.Dsa.X86 (argumentPointer)

/-- Two searches that end alike: what a finished search leaves depends on its outcome and the octets
it consumed, not on the statuses before. -/
def Same (r₁ r₂ : KeySearchResult) : Prop := r₁.outcome = r₂.outcome ∧ r₁.used = r₂.used

theorem Same.refl (r : KeySearchResult) : Same r r := ⟨rfl, rfl⟩

theorem Same.trans {r₁ r₂ r₃ : KeySearchResult} (h₁ : Same r₁ r₂) (h₂ : Same r₂ r₃) : Same r₁ r₃ :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem Done.congr {p : KPub} {o s : State} {r₁ r₂ : KeySearchResult} (h : Done p o r₁ s) (e : Same r₁ r₂) :
    Done p o r₂ s := by
  have es : r₁.status = r₂.status := by simp only [KeySearchResult.status, e.1]
  have er : r₁.retries = r₂.retries := by simp only [KeySearchResult.retries, e.1]
  refine ⟨h.input, h.rd, h.wr, h.esp, h.esi, h.saved, h.frame, h.words.congr fun d _ => ?_, ?_,
    by rw [← er, ← e.2]; exact h.small⟩
  · simp only [doneF, es, er, e.2]
  · have := h.output; unfold Output at this ⊢; rw [← e.1]; exact this

/-- A loop state after a rejection: the status word says so. -/
def Rej (p : KPub) (o : State) (used keys scalars : Nat) (s : State) : Prop :=
  Live p o used keys scalars s ∧ s.mem.readW (addr p.S statusOff) 32 = 4

/-- After an iteration: the search finished as `R`, or a loop state with a smaller measure from which
it ends as `R` does. -/
def Next (p : KPub) (o : State) (R : KeySearchResult) (n : Nat) (s : State) : Prop :=
  Done p o R s ∨ ∃ used keys scalars, 129 * keys + scalars < n ∧ Rej p o used keys scalars s ∧
    Same (p.tail (randOf o) used keys scalars) R

/-- A run's state with a loop state's words. -/
theorem St.live {o s : State} {used keys scalars : Nat}
    (h : St o liveDs (liveF (ofState o) (o.gpr .esi) used keys scalars) s) (hu : used ≤ (ofState o).randLen)
    (hk : keys ≤ 128) (hc : scalars ≤ 128) : Live (ofState o) o used keys scalars s :=
  ⟨⟨h.abi, rfl⟩, hu, hk, hc, h.rd, h.wr, h.esp, h.esi, h.saved, h.frame, h.words⟩

theorem advance_ok {o u : State} {e : BitVec 32} {used keys scalars : Nat}
    (S : St o liveDs (liveF (ofState o) e used keys scalars) u) (hr : used + (ofState o).len ≤ (ofState o).randLen)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, St o liveDs (liveF (ofState o) e (used + (ofState o).len) keys scalars) t → t.gpr .edx = u.gpr .eax →
      Frame [sR o] u.mem t.mem → WP isa (.block rest) t Q) :
    WP isa (.block (advance ++ rest)) u Q := by
  have hA := liveDs_aligned
  have hb := S.abi.rBound
  unfold advance
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun t₁ U₁ => ?_
  have S₁ := S.reg U₁ (Or.inr (Or.inr rfl))
  refine S₁.ld (Or.inr (Or.inl rfl)) (d := lenOff) (by decide) (by decide) fun t₂ S₂ g₂ o₂ _ m₂ => ?_
  refine S₂.ld (Or.inl rfl) (d := randOff) (by decide) (by decide) fun t₃ S₃ g₃ o₃ _ m₃ => ?_
  refine wp_add fun t₄ U₄ _ => ?_
  have S₄ := S₃.reg U₄ (Or.inl rfl)
  refine S₄.stw hA (d := randOff) (by decide) (by decide) fun t₅ S₅ G₅ _ _ F₅ => ?_
  have hA₅ := hA.cons (d := randOff) (by decide) (by decide)
  refine S₅.ld (Or.inl rfl) (d := leftOff) (by decide) (by decide) fun t₆ S₆ g₆ o₆ _ m₆ => ?_
  refine wp_sub fun t₇ U₇ _ => ?_
  have S₇ := S₆.reg U₇ (Or.inl rfl)
  refine S₇.stw hA₅ (d := leftOff) (by decide) (by decide) fun t₈ S₈ G₈ _ _ F₈ => ?_
  have hA₈ := hA₅.cons (d := leftOff) (by decide) (by decide)
  refine S₈.ld (Or.inl rfl) (d := usedOff) (by decide) (by decide) fun t₉ S₉ g₉ o₉ _ m₉ => ?_
  refine wp_add fun t₁₀ U₁₀ _ => ?_
  have S₁₀ := S₉.reg U₁₀ (Or.inl rfl)
  refine S₁₀.stw hA₈ (d := usedOff) (by decide) (by decide) fun t₁₁ S₁₁ G₁₁ _ _ F₁₁ => k t₁₁ ?_ ?_ ?_
  · -- The values stored.
    have c₃ : t₃.gpr .ecx = BitVec.ofNat 32 (ofState o).len := by rw [o₃ .ecx (by decide), g₂]; rfl
    have c₆ : t₆.gpr .ecx = BitVec.ofNat 32 (ofState o).len := by
      rw [o₆ .ecx (by decide), G₅, U₄.other .ecx (by decide), c₃]
    have c₉ : t₉.gpr .ecx = BitVec.ofNat 32 (ofState o).len := by
      rw [o₉ .ecx (by decide), G₈, U₇.other .ecx (by decide), c₆]
    have v₄ : t₄.gpr .eax = (ofState o).rp + BitVec.ofNat 32 (used + (ofState o).len) := by
      rw [U₄.gpr, g₃, c₃, BitVec.ofNat_add, ← BitVec.add_assoc]; rfl
    have v₇ : t₇.gpr .eax = BitVec.ofNat 32 ((ofState o).randLen - (used + (ofState o).len)) := by
      rw [U₇.gpr, g₆, c₆, show upd (liveF (ofState o) e used keys scalars) randOff (t₄.gpr .eax) leftOff =
        BitVec.ofNat 32 ((ofState o).randLen - used) from rfl, sub_ofNat (by omega), Nat.sub_add_eq]
    have v₁₀ : t₁₀.gpr .eax = BitVec.ofNat 32 (used + (ofState o).len) := by
      rw [U₁₀.gpr, g₉, c₉, show upd (upd (liveF (ofState o) e used keys scalars) randOff (t₄.gpr .eax)) leftOff
        (t₇.gpr .eax) usedOff = BitVec.ofNat 32 used from rfl, BitVec.ofNat_add_ofNat]
    rw [v₄, v₇, v₁₀] at S₁₁
    refine (S₁₁.sub fun d hd => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd))).congr ?_
    simp only [liveDs, List.mem_cons, List.not_mem_nil, or_false]
    rintro d (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl) <;> simp [upd, liveF, randOff, leftOff, usedOff]
  · rw [G₁₁, U₁₀.other _ (by decide), o₉ _ (by decide), G₈, U₇.other _ (by decide), o₆ _ (by decide), G₅,
      U₄.other _ (by decide), o₃ _ (by decide), o₂ _ (by decide), U₁.gpr]

  · have e₄ : t₄.mem = u.mem := by rw [U₄.mem, m₃, m₂, U₁.mem]
    have e₇ : t₇.mem = t₅.mem := by rw [U₇.mem, m₆]
    have e₁₀ : t₁₀.mem = t₈.mem := by rw [U₁₀.mem, m₉]
    rw [e₄] at F₅; rw [e₇] at F₈; rw [e₁₀] at F₁₁
    exact (F₅.trans F₈).trans F₁₁

/-- `terminal k`: the budgets and the request zero, the status `k`. -/
theorem St.terminal {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (hA : Aligned ds)
    (k : Nat) :
    WP isa (.block (VG.Impl.Ffdh.X86.KeySearch.terminal k)) s fun t =>
      St o (statusOff :: requestOff :: scalarsOff :: keysOff :: ds)
        (upd (upd (upd (upd f keysOff 0) scalarsOff 0) requestOff 0) statusOff (BitVec.ofNat 32 k)) t ∧
      Frame [sR o] s.mem t.mem := by
  unfold VG.Impl.Ffdh.X86.KeySearch.terminal
  refine wp_movi fun t₁ U₁ => ?_
  have S₁ := h.reg U₁ (Or.inl rfl)
  refine S₁.stw hA (d := keysOff) (by decide) (by decide) fun t₂ S₂ G₂ _ _ F₂ => ?_
  have hA₂ := hA.cons (d := keysOff) (by decide) (by decide)
  refine S₂.stw hA₂ (d := scalarsOff) (by decide) (by decide) fun t₃ S₃ G₃ _ _ F₃ => ?_
  have hA₃ := hA₂.cons (d := scalarsOff) (by decide) (by decide)
  refine S₃.stw hA₃ (d := requestOff) (by decide) (by decide) fun t₄ S₄ G₄ _ _ F₄ => ?_
  have hA₄ := hA₃.cons (d := requestOff) (by decide) (by decide)
  refine wp_movi fun t₅ U₅ => ?_
  have S₅ := S₄.reg U₅ (Or.inl rfl)
  refine S₅.stw hA₄ (d := statusOff) (by decide) (by decide) fun t₆ S₆ G₆ _ _ F₆ => WP.block_nil ?_
  have e₂ : t₂.gpr .eax = 0 := by rw [G₂, U₁.gpr]
  have e₃ : t₃.gpr .eax = 0 := by rw [G₃, e₂]
  rw [U₁.gpr, e₂, e₃, U₅.gpr] at S₆
  rw [U₅.mem] at F₆
  rw [U₁.mem] at F₂
  exact ⟨S₆, ((F₂.trans F₃).trans F₄).trans F₆⟩

/-- A scalar out of range: one fewer scalar, the status 4. -/
theorem St.rejectedScalar {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (hA : Aligned ds)
    (hd : scalarsOff ∈ ds) {c : Nat} (hc : f scalarsOff = BitVec.ofNat 32 c) (hc1 : 1 ≤ c) :
    WP isa (.block VG.Impl.Ffdh.X86.KeySearch.rejectedScalar) s fun t =>
      St o (statusOff :: scalarsOff :: ds) (upd (upd f scalarsOff (BitVec.ofNat 32 (c - 1))) statusOff 4) t := by
  unfold VG.Impl.Ffdh.X86.KeySearch.rejectedScalar
  refine h.ld (Or.inl rfl) (d := scalarsOff) hd (by decide) fun t₁ S₁ g₁ _ _ _ => ?_
  refine wp_subi fun t₂ U₂ _ _ => ?_
  have S₂ := S₁.reg U₂ (Or.inl rfl)
  refine S₂.stw hA (d := scalarsOff) (by decide) (by decide) fun t₃ S₃ G₃ _ _ _ => ?_
  have hA₃ := hA.cons (d := scalarsOff) (by decide) (by decide)
  refine wp_movi fun t₄ U₄ => ?_
  have S₄ := S₃.reg U₄ (Or.inl rfl)
  refine S₄.stw hA₃ (d := statusOff) (by decide) (by decide) fun t₅ S₅ _ _ _ _ => WP.block_nil ?_
  rw [U₂.gpr, g₁, hc, ofNat_pred hc1, U₄.gpr] at S₅
  exact S₅

/-- A degenerate public value: one fewer key, the scalar budget again, the status 4. -/
theorem St.rejectedPublic {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (hA : Aligned ds)
    (hd : keysOff ∈ ds) {k : Nat} (hk : f keysOff = BitVec.ofNat 32 k) (hk1 : 1 ≤ k) :
    WP isa (.block VG.Impl.Ffdh.X86.KeySearch.rejectedPublic) s fun t =>
      St o (statusOff :: scalarsOff :: keysOff :: ds)
        (upd (upd (upd f keysOff (BitVec.ofNat 32 (k - 1))) scalarsOff 128) statusOff 4) t := by
  unfold VG.Impl.Ffdh.X86.KeySearch.rejectedPublic
  refine h.ld (Or.inl rfl) (d := keysOff) hd (by decide) fun t₁ S₁ g₁ _ _ _ => ?_
  refine wp_subi fun t₂ U₂ _ _ => ?_
  have S₂ := S₁.reg U₂ (Or.inl rfl)
  refine S₂.stw hA (d := keysOff) (by decide) (by decide) fun t₃ S₃ G₃ _ _ _ => ?_
  have hA₃ := hA.cons (d := keysOff) (by decide) (by decide)
  refine wp_movi fun t₄ U₄ => ?_
  have S₄ := S₃.reg U₄ (Or.inl rfl)
  refine S₄.stw hA₃ (d := scalarsOff) (by decide) (by decide) fun t₅ S₅ G₅ _ _ _ => ?_
  have hA₅ := hA₃.cons (d := scalarsOff) (by decide) (by decide)
  refine wp_movi fun t₆ U₆ => ?_
  have S₆ := S₅.reg U₆ (Or.inl rfl)
  refine S₆.stw hA₅ (d := statusOff) (by decide) (by decide) fun t₇ S₇ _ _ _ _ => WP.block_nil ?_
  rw [U₂.gpr, g₁, hk, ofNat_pred hk1, U₄.gpr, U₆.gpr] at S₇
  exact S₇

/-- The bytes at an output, through writes of the state. -/
theorem out_keep {o : State} (A : KeySearchABI o) {m m' : Mem} (h : Frame [sR o] m m') {i : Nat} (hi : i = 0 ∨ i = 2) :
    Spec.Rsa.bytesAt m' (argumentPointer o i) (arg o 7).toNat = Spec.Rsa.bytesAt m (argumentPointer o i) (arg o 7).toNat := by
  have hp := A.pLen
  unfold Spec.Ffdh.pLenValid at hp
  refine bytes_frame h (fun r hr => ?_) (by omega)
  simp only [List.mem_singleton] at hr; subst hr
  rcases hi with rfl | rfl
  · rw [← xR_eq A]; exact A.xs
  · rw [← yR_eq A]; exact A.ys

theorem cmp_status {s t : State} {k j : Nat} (hk : k ≤ 3) (hj : j ≤ 3) (he : s.gpr .edx = BitVec.ofNat 32 k)
    (z : t.zf = some (s.gpr .edx - BitVec.ofNat 32 j == 0)) : isa.eval .e t = some (decide (k = j)) := by
  show t.zf = _
  rw [z, he, sub_beq (by omega) (by omega)]

theorem classify_ok {p : KPub} {o s₀ u : State} {used keys scalars : Nat} (h : Live p o used keys scalars s₀)
    (S : St o liveDs (liveF p (o.gpr .esi) used keys scalars) u)
    (he : u.gpr .eax = BitVec.ofNat 32 (attemptStatus p.a p.len ((randOf o).drop used)))
    (ho : AttemptOut o used u.mem) (hk : keys ≠ 0) (hs : scalars ≠ 0) (hr : used + p.len ≤ p.randLen) :
    WP isa classify u (Next p o (p.tail (randOf o) used keys scalars) (129 * keys + scalars)) := by
  obtain ⟨A, rfl⟩ := h.input
  have hA := liveDs_aligned
  have hkl := h.keys_le
  have hcl := h.scalars_le
  have hr' : (ofState o).len ≤ (randOf o).length - used := by
    simp only [randOf, Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact Nat.le_sub_of_add_le' hr
  unfold classify
  refine WP.seq (advance_ok S hr fun t S' hed Ft => wp_cmpi fun t' F _ z => WP.block_nil ?_)
  have S'' := S'.fupd F
  have Ft' : Frame [sR o] u.mem t'.mem := by rw [F.mem]; exact Ft
  have hed' : t'.gpr .edx = BitVec.ofNat 32 (attemptStatus (ofState o).a (ofState o).len ((randOf o).drop used)) := by
    rw [F.gpr, hed, he]
  have hedT : t.gpr .edx = BitVec.ofNat 32 (attemptStatus (ofState o).a (ofState o).len ((randOf o).drop used)) :=
    hed.trans he
  have hst := attemptStatus_cases (ofState o).a (ofState o).len ((randOf o).drop used)
  have hle : attemptStatus (ofState o).a (ofState o).len ((randOf o).drop used) ≤ 3 := by
    rcases hst with h1 | h1 | h1 <;> omega
  rcases hst with h1 | h2 | h3
  · -- Accepted.
    refine WP.ite true (by rw [cmp_status hle (j := 1) (by decide) hedT z, h1]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.mono (S''.terminal hA 1) fun v ⟨Sv, Fv⟩ => Or.inl ?_
    show Done _ _ (keyTail _ _ _ _ _ _) v
    rw [keyTail_accepted hk hs hr' h1]
    refine Sv.done (by decide) ?_ ?_ ⟨Nat.zero_le _, Nat.zero_le _, by simp only [ofState] at hr ⊢; omega⟩
    · simp only [doneDs, List.mem_cons, List.not_mem_nil, or_false]
      rintro d (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
        simp [upd, liveF, doneF, statusOff, requestOff, scalarsOff, keysOff, KeySearchResult.retries,
          KeySearchResult.status]
    · have h1' : keyStatus (ofState o).a (scalarOfOctets (ofState o).a
          (List.take (arg o 7).toNat (List.drop used (randOf o)))) = 1 := h1
      have ho' := ho
      unfold AttemptOut at ho'
      dsimp only at ho'
      rw [ite_eq_left h1'] at ho'
      exact ⟨(out_keep A (Ft'.trans Fv) (Or.inl rfl)).trans ho'.1, (out_keep A (Ft'.trans Fv) (Or.inr rfl)).trans ho'.2⟩
  · -- A scalar out of range.
    refine WP.ite false (by rw [cmp_status hle (j := 1) (by decide) hedT z, h2]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq (wp_cmpi fun t₂ F₂ _ z₂ => WP.block_nil ?_)
    have S₂ := S''.fupd F₂
    have hed₂ : t₂.gpr .edx = _ := (congrFun F₂.gpr .edx).trans hed'
    refine WP.ite true (by rw [cmp_status hle (j := 2) (by decide) hed' z₂, h2]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.mono (S₂.rejectedScalar hA (by decide) (c := scalars) (by simp [liveF, scalarsOff]) (by omega))
      fun v Sv => Or.inr ⟨used + (ofState o).len, keys, scalars - 1, by omega, ⟨Sv.sub (fun d hd => by
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd)) |>.congr ?_ |>.live (by omega) hkl (by omega),
        ?_⟩, ?_⟩
    · simp only [liveDs, List.mem_cons, List.not_mem_nil, or_false]
      rintro d (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl) <;> simp [upd, liveF, statusOff, scalarsOff]
    · show v.mem.readW (addr (arg o 12) statusOff) 32 = 4
      rw [Sv.words.get (List.mem_cons_self ..)]; simp [upd, statusOff]
    · show Same (keyTail _ _ _ _ _ _) (keyTail _ _ _ _ _ _)
      rw [keyTail_scalar hk hs hr' h2]; exact Same.refl _
  · -- A degenerate public value.
    refine WP.ite false (by rw [cmp_status hle (j := 1) (by decide) hedT z, h3]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq (wp_cmpi fun t₂ F₂ _ z₂ => WP.block_nil ?_)
    have S₂ := S''.fupd F₂
    have hed₂ : t₂.gpr .edx = _ := (congrFun F₂.gpr .edx).trans hed'
    refine WP.ite false (by rw [cmp_status hle (j := 2) (by decide) hed' z₂, h3]; rfl) (fun h => absurd h (by decide))
      (fun _ => ?_)
    refine WP.seq (wp_cmpi fun t₃ F₃ _ z₃ => WP.block_nil ?_)
    have S₃ := S₂.fupd F₃
    have hed₃ : t₃.gpr .edx = _ := (congrFun F₃.gpr .edx).trans hed₂
    refine WP.ite true (by rw [cmp_status hle (j := 3) (by decide) hed₂ z₃, h3]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.mono (S₃.rejectedPublic hA (by decide) (k := keys) (by simp [liveF, keysOff]) (by omega))
      fun v Sv => Or.inr ⟨used + (ofState o).len, keys - 1, 128, by omega, ⟨Sv.sub (fun d hd => by
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd))) |>.congr ?_
        |>.live (by omega) (by omega) (by decide), ?_⟩, ?_⟩
    · simp only [liveDs, List.mem_cons, List.not_mem_nil, or_false]
      rintro d (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl) <;> simp [upd, liveF, statusOff, scalarsOff, keysOff]
    · show v.mem.readW (addr (arg o 12) statusOff) 32 = 4
      rw [Sv.words.get (List.mem_cons_self ..)]; simp [upd, statusOff]
    · show Same (keyTail _ _ _ _ _ _) (keyTail _ _ _ _ _ _)
      rw [keyTail_public hk hs hr' h3]; exact Same.refl _

end VG.Proof.Ffdh.X86.KeySearch
