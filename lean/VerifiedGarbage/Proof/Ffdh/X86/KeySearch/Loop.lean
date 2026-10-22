module

public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Classify
import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Entry

/-! # The key search's loop (x86)

An iteration from a loop state ends the search as the search from there
does, or counts a rejection and loops (`branch_ok`, `iteration_ok`); the
loop, from a loop state, ends in the search from there (`loop_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeySearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.KeySearch
open VG.Proof.Ffdh.KeyGeneration
open VG.Proof.Dsa.X86 (argumentPointer)

theorem Live.reg {p : KPub} {o s t : State} {used keys scalars : Nat} (h : Live p o used keys scalars s) {r : Reg}
    {v : BitVec 32} (U : Upd s t r v) (hr : Scratch r) : Live p o used keys scalars t := by
  have S := h.st.reg U hr
  obtain ⟨A, rfl⟩ := h.input
  exact S.live h.used_le h.keys_le h.scalars_le

theorem Live.fupd {p : KPub} {o s t : State} {used keys scalars : Nat} (h : Live p o used keys scalars s)
    (F : Fupd s t) : Live p o used keys scalars t := by
  have S := h.st.fupd F
  obtain ⟨A, rfl⟩ := h.input
  exact S.live h.used_le h.keys_le h.scalars_le

/-- `test eax, eax` after loading a budget below `2³²`. -/
theorem test_zero {s t : State} {k : Nat} (hk : k < 2 ^ 32) (he : s.gpr .eax = BitVec.ofNat 32 k)
    (z : t.zf = some (s.gpr .eax &&& s.gpr .eax == 0)) : isa.eval .e t = some (decide (k = 0)) := by
  show t.zf = _
  rw [z, he, BitVec.and_self, ofNat_beq_zero hk]

theorem branch_ok {p : KPub} {o s : State} {used keys scalars : Nat} (h : Live p o used keys scalars s) :
    WP isa branch s (Next p o (p.tail (randOf o) used keys scalars) (129 * keys + scalars)) := by
  have S := h.st
  have hkl := h.keys_le
  have hcl := h.scalars_le
  have hul := h.used_le
  obtain ⟨A, rfl⟩ := h.input
  have hlen : (randOf o).length = (ofState o).randLen := by
    simp only [randOf, Spec.Rsa.bytesAt, List.length_map, List.length_range]; rfl
  have hR : (ofState o).randLen < 2 ^ 32 := (arg o 9).isLt
  have hL : (ofState o).len < 2 ^ 32 := (arg o 7).isLt
  unfold branch
  refine WP.seq (S.ld (Or.inl rfl) (d := keysOff) (by decide) (by decide) fun t₁ S₁ g₁ _ _ _ => ?_)
  refine wp_test fun t₂ F₂ z₂ => WP.block_nil ?_
  have L₂ := (S₁.fupd F₂).live hul hkl hcl
  have e₂ := test_zero (k := keys) (by omega) g₁ z₂
  by_cases hk : keys = 0
  · refine WP.ite true (by rw [e₂]; simp [hk]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.mono (exhausted_ok L₂) fun v hv => Or.inl ?_
    show Done _ _ (keyTail _ _ _ _ _ _) v
    rw [keyTail_exhausted (Or.inl hk)]; exact hv
  refine WP.ite false (by rw [e₂]; simp [hk]) (fun h => absurd h (by decide)) (fun _ => ?_)
  refine WP.seq (L₂.st.ld (Or.inl rfl) (d := scalarsOff) (by decide) (by decide) fun t₃ S₃ g₃ _ _ _ => ?_)
  refine wp_test fun t₄ F₄ z₄ => WP.block_nil ?_
  have L₄ := (S₃.fupd F₄).live hul hkl hcl
  have e₄ := test_zero (k := scalars) (by omega) g₃ z₄
  by_cases hs : scalars = 0
  · refine WP.ite true (by rw [e₄]; simp [hs]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.mono (exhausted_ok L₄) fun v hv => Or.inl ?_
    show Done _ _ (keyTail _ _ _ _ _ _) v
    rw [keyTail_exhausted (Or.inr hs)]; exact hv
  refine WP.ite false (by rw [e₄]; simp [hs]) (fun h => absurd h (by decide)) (fun _ => ?_)
  unfold attemptOrRequest room
  refine WP.seq (L₄.st.ld (Or.inl rfl) (d := leftOff) (by decide) (by decide) fun t₅ S₅ g₅ _ _ _ => ?_)
  refine S₅.ld (Or.inr (Or.inl rfl)) (d := lenOff) (by decide) (by decide) fun t₆ S₆ g₆ o₆ _ _ => ?_
  refine wp_cmp fun t₇ F₇ c₇ _ => WP.block_nil ?_
  have L₇ := (S₆.fupd F₇).live hul hkl hcl
  have hb : isa.eval .b t₇ = some (decide ((ofState o).randLen - used < (ofState o).len)) := by
    show t₇.cf = _
    rw [c₇, o₆ .eax (by decide), g₅, g₆]
    simp only [liveF, leftOff, lenOff, ↓reduceIte, Nat.reduceEqDiff]
    rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt hL]
  by_cases hr : (ofState o).randLen - used < (ofState o).len
  · refine WP.ite true (by rw [hb]; simp [hr]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.mono (request_ok L₇) fun v hv => Or.inl ?_
    show Done _ _ (keyTail _ _ _ _ _ _) v
    rw [keyTail_short hk hs (by rw [hlen]; exact hr)]; exact hv
  refine WP.ite false (by rw [hb]; simp [hr]) (fun h => absurd h (by decide)) (fun _ => ?_)
  refine WP.seq (WP.mono (attempt_ok L₇ (by omega)) fun u ⟨Su, eu, ou⟩ => ?_)
  exact classify_ok L₇ Su eu ou hk hs (by omega)

theorem Done.reg {p : KPub} {o s t : State} {r : KeySearchResult} (h : Done p o r s) {q : Reg} {v : BitVec 32}
    (U : Upd s t q v) (hq : Scratch q) : Done p o r t := by
  obtain ⟨A, rfl⟩ := h.input
  refine ⟨⟨A, rfl⟩, U.rd.trans h.rd, U.wr.trans h.wr, ?_, ?_, fun r' hr hne => ?_, U.mem ▸ h.frame,
    U.mem ▸ h.words, U.mem ▸ h.output, h.small⟩
  · rw [U.other _ (saved_ne hq (by decide)), h.esp]
  · rw [U.other _ (saved_ne hq (by decide)), h.esi]
  · rw [U.other _ (saved_ne hq hr), h.saved r' hr hne]

theorem Done.fupd {p : KPub} {o s t : State} {r : KeySearchResult} (h : Done p o r s) (F : Fupd s t) :
    Done p o r t :=
  ⟨h.input, F.rd.trans h.rd, F.wr.trans h.wr, by rw [F.gpr, h.esp], by rw [F.gpr, h.esi],
    fun q hq hne => by rw [F.gpr, h.saved q hq hne], F.mem ▸ h.frame, F.mem ▸ h.words, F.mem ▸ h.output,
    h.small⟩

theorem status_le (r : KeySearchResult) : r.status ≤ 3 := by
  unfold KeySearchResult.status; split <;> decide

/-- What an iteration leaves: the search finished as `R`, or a loop state with a smaller measure from
which it ends as `R` does, and the loop's condition says which. -/
def IterPost (p : KPub) (o : State) (R : KeySearchResult) (n : Nat) (s : State) : Prop :=
  (isa.eval .e s = some false ∧ Done p o R s) ∨
    (isa.eval .e s = some true ∧ ∃ m < n, ∃ used keys scalars, m = 129 * keys + scalars ∧
      Live p o used keys scalars s ∧ Same (p.tail (randOf o) used keys scalars) R)

theorem iteration_ok {p : KPub} {o s : State} {used keys scalars : Nat} {R : KeySearchResult}
    (h : Live p o used keys scalars s) (hR : Same (p.tail (randOf o) used keys scalars) R) :
    WP isa iteration s (IterPost p o R (129 * keys + scalars)) := by
  have A := h.input.1
  have hp := h.input.2
  unfold iteration
  refine WP.seq (WP.mono (branch_ok h) fun v hv => ?_)
  rcases hv with D | ⟨u', k', c', hm, ⟨L, hst⟩, hs⟩
  · have dS : v.gpr .esi = arg o 12 := by rw [D.esi, ← hp]; rfl
    refine wp_ldm dS (by rw [D.rd, D.wr]; exact ⟨_, List.mem_append_right _ (sR_mem A), st_in A (by decide)⟩)
      fun t₁ U₁ => wp_cmpi fun t₂ F₂ _ z₂ => WP.block_nil (Or.inl ⟨?_, ((D.reg U₁ (Or.inl rfl)).fupd F₂).congr hR⟩)
    subst hp
    have w : v.mem.readW (addr (arg o 12) statusOff) 32 =
        doneF (ofState o) (o.gpr .esi) ((ofState o).tail (randOf o) used keys scalars) statusOff :=
      D.words.get (by decide)
    show t₂.zf = _
    rw [z₂, U₁.gpr, w]
    simp only [doneF, statusOff, ↓reduceIte, Nat.reduceEqDiff]
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, sub_beq (by have := status_le ((ofState o).tail (randOf o) used keys scalars); omega)
      (by decide)]
    have := status_le ((ofState o).tail (randOf o) used keys scalars)
    simp only [Option.some.injEq, decide_eq_false_iff_not]
    omega
  · have lS : v.gpr .esi = arg o 12 := by rw [L.esi, ← hp]; rfl
    refine wp_ldm lS (by rw [L.rd, L.wr]; exact ⟨_, List.mem_append_right _ (sR_mem A), st_in A (by decide)⟩)
      fun t₁ U₁ => wp_cmpi fun t₂ F₂ _ z₂ => WP.block_nil (Or.inr ⟨?_, _, hm, u', k', c', rfl,
        (L.reg U₁ (Or.inl rfl)).fupd F₂, hs.trans hR⟩)
    show t₂.zf = _
    rw [z₂, U₁.gpr, show v.mem.readW (addr (arg o 12) statusOff) 32 = 4 by rw [← hp] at hst; exact hst]
    rfl

theorem loop_ok {p : KPub} {o s : State} {used keys scalars : Nat} (h : Live p o used keys scalars s) :
    WP isa (.loop iteration .e) s (Done p o (p.tail (randOf o) used keys scalars)) := by
  refine WP.loop (M := isa) (fun n t => ∃ u k c, n = 129 * k + c ∧ Live p o u k c t ∧
      Same (p.tail (randOf o) u k c) (p.tail (randOf o) used keys scalars)) (fun n t ⟨u, k, c, hn, L, hS⟩ => ?_)
    _ s ⟨used, keys, scalars, rfl, h, Same.refl _⟩
  subst hn
  refine WP.mono (iteration_ok L hS) fun v hv => ?_
  rcases hv with ⟨he, D⟩ | ⟨he, m, hm, u', k', c', rfl, L', hS'⟩
  · exact Or.inl ⟨he, D⟩
  · exact Or.inr ⟨he, _, hm, u', k', c', rfl, L', hS'⟩

end VG.Proof.Ffdh.X86.KeySearch
