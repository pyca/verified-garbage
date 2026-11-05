module

public import VerifiedGarbage.Impl.RsaPss.AArch64.Encoding
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.MlKem.AArch64.Wp
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Two
meta import VerifiedGarbage.Impl.RsaPss.AArch64.Encoding

/-!
# The choice of the code for the hash function of a table, on AArch64

`byIdx b is` runs `b i` for the index `i` in `x27`, by comparisons with each
of `is` (`x9 := x27 - j`): `byIdx_wp` from the state before the comparisons,
`byIdx_ct` in two runs whose `x27` is the same, each comparison writing only
`x9`, as on x86-64 (`Proof/RsaPss/X86_64/ByIdx.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (Only wp_nil wp_subImm eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (Two two_post two_ite two_mono two_taint)

/-- The comparison of `x27` with `j`. -/
abbrev cmpIdx (j : Nat) : Prog isa := .block [.subImm .x .x9 .x27 j]

theorem sub_eq_zero {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    (BitVec.ofNat 64 i - BitVec.ofNat 64 j == 0) = decide (i = j) := by
  by_cases h : i = j
  · subst h; simp
  · have : BitVec.ofNat 64 i - BitVec.ofNat 64 j ≠ 0 := fun e => h (by
      have e' : BitVec.ofNat 64 i = BitVec.ofNat 64 j := by
        rw [← BitVec.sub_add_cancel (BitVec.ofNat 64 i) (BitVec.ofNat 64 j), e]; exact BitVec.zero_add _
      have := congrArg BitVec.toNat e'
      simpa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using this)
    rw [decide_eq_false h]
    exact beq_false_of_ne this

/-- A comparison of `x27` with `j`: `x9` is zero exactly when `i = j`. -/
theorem cmpIdx_ok {t : State} {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 4096) (h27 : t.gpr .x27 = BitVec.ofNat 64 i) :
    WP isa (cmpIdx j) t fun t' => Only [.x9] t t' ∧ (t'.gpr .x9 == 0) = decide (i = j) ∧ t'.syms = t.syms :=
  WP.of_syms (wp_subImm hj fun t' o e => wp_nil fun sy => ⟨o, by rw [e, h27, sub_eq_zero hi (by omega)], sy⟩)

/-- `byIdx b is` runs `b i`. -/
theorem byIdx_wp {b : Nat → Prog isa} {Q : State → Prop} : ∀ {is : List Nat} {i : Nat} {t : State},
    i ∈ is → (∀ j ∈ is, j < 4096) → t.gpr .x27 = BitVec.ofNat 64 i →
    (∀ t', Only [.x9] t t' → t'.syms = t.syms → WP isa (b i) t' Q) → WP isa (byIdx b is) t Q
  | [], _, _, hi, _, _, _ => absurd hi List.not_mem_nil
  | [j], i, t, hi, _, _, h => by
    obtain rfl := List.mem_singleton.mp hi
    exact h t (Only.refl _ _) rfl
  | j :: k :: is, i, t, hi, hlt, h27, h => by
    have hil : i < 2 ^ 64 := by have := hlt i hi; omega
    simp only [byIdx]
    refine WP.seq (WP.mono (cmpIdx_ok hil (hlt j List.mem_cons_self) h27) fun t' ⟨o, hz, sy⟩ => ?_)
    refine WP.ite (M := isa) _ (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
    · rw [hz, decide_eq_true_eq] at hb
      subst hb
      exact h t' o sy
    · rw [hz, decide_eq_false_iff_not] at hb
      have hi' : i ∈ k :: is := (List.mem_cons.mp hi).resolve_left hb
      exact byIdx_wp hi' (fun x hx => hlt x (List.mem_cons_of_mem _ hx)) ((o.get .x27).trans h27)
        fun t'' o' sy' => h t'' ((o.trans o').mono) (sy'.trans sy)

/-- `byIdx b is` in two runs whose `x27` is the index `idx a` of the anchor:
the comparisons from the same public `x27`, then `b (idx a)`. -/
theorem byIdx_ct {α : Type} {b : Nat → Prog isa} {Q : State → State → Prop} (idx : α → Nat) :
    ∀ {is : List Nat} {Φ : α → State → Prop},
    (∀ a t t', Φ a t → Only [.x9] t t' → t'.syms = t.syms → Φ a t') →
    (∀ a t, Φ a t → idx a ∈ is ∧ t.gpr .x27 = BitVec.ofNat 64 (idx a) ∧ t.sp = t.sp) →
    (∀ j ∈ is, j < 4096) →
    (∀ j ∈ is, RelCT isa (Two Φ) (cmpIdx j) fun _ _ => True) →
    (∀ j ∈ is, RelCT isa (Two fun a t => Φ a t ∧ idx a = j) (b j) Q) →
    RelCT isa (Two Φ) (byIdx b is) Q
  | [], _, _, hΦ, _, _, _ => RelCT.of_false fun _ _ ⟨a, h₁, _⟩ => by simpa using (hΦ a _ h₁).1
  | [j], _, _, hΦ, _, _, hb => (hb j (List.mem_singleton_self _)).mono
    (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, ⟨h₁, List.mem_singleton.mp (hΦ a _ h₁).1⟩, ⟨h₂, List.mem_singleton.mp (hΦ a _ h₁).1⟩⟩)
    fun _ _ h => h
  | j :: k :: is, Φ, hkeep, hΦ, hlt, hc, hb => by
    simp only [byIdx]
    have ih := byIdx_ct idx (is := k :: is) (Φ := fun a t => Φ a t ∧ idx a ≠ j)
      (fun a t t' ⟨h, hn⟩ o sy => ⟨hkeep a t t' h o sy, hn⟩)
      (fun a t ⟨h, hn⟩ => ⟨(List.mem_cons.mp (hΦ a t h).1).resolve_left hn, (hΦ a t h).2⟩)
      (fun x hx => hlt x (List.mem_cons_of_mem _ hx))
      (fun x hx => (hc x (List.mem_cons_of_mem _ hx)).mono (fun _ _ => two_mono fun _ _ h => h.1) fun _ _ h => h)
      (fun x hx => (hb x (List.mem_cons_of_mem _ hx)).mono (fun _ _ => two_mono fun _ _ h => ⟨h.1.1, h.2⟩)
        fun _ _ h => h)
    refine RelCT.seq (two_post (Ψ := fun a t => Φ a t ∧ (t.gpr .x9 == 0) = decide (idx a = j))
      (hc j List.mem_cons_self) fun a t h => ?_) (two_ite (fun a t₁ t₂ h₁ h₂ => ?_)
        ((hb j List.mem_cons_self).mono (fun _ _ => two_mono fun a t ⟨⟨h, hz⟩, he⟩ => ⟨h, ?_⟩) fun _ _ h => h)
        (ih.mono (fun _ _ => two_mono fun a t ⟨⟨h, hz⟩, he⟩ => ⟨h, ?_⟩) fun _ _ h => h))
    · obtain ⟨hm, h27, _⟩ := hΦ a t h
      exact WP.mono (cmpIdx_ok (by have := hlt _ hm; omega) (hlt j List.mem_cons_self) h27)
        fun t' ⟨o, hz, sy⟩ => ⟨hkeep a t t' h o sy, hz⟩
    · rw [eval_zero, eval_zero, h₁.2, h₂.2]
    · rw [eval_zero, hz] at he
      simpa using he
    · rw [eval_zero, hz] at he
      simpa using he

end VG.Proof.RsaPss.AArch64
