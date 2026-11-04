module

public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.AArch64
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# Deterministic ECDSA on AArch64: the choice of the code for the hash function of a table

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/ByIdx.lean`): `byIdx b is` runs
`b i` for the index `i` in `x16`, by comparisons with each of `is`
(`x17 = x16 - j`, then `cbz x17`): `byIdx_wp` from the state before the
comparisons, `byIdx_ct` in two runs whose `x16` is the same, each
comparison keeping the state but `x17`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Bignum.AArch64 (Two two_post two_mono two_ite)

/-- What a comparison keeps: everything but `x17`. -/
structure Keep17 (t t' : State) : Prop where
  gpr : ∀ r, r ≠ .x17 → t'.gpr r = t.gpr r
  mem : t'.mem = t.mem
  syms : t'.syms = t.syms
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  sp : t'.sp = t.sp

theorem Keep17.refl (t : State) : Keep17 t t := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Keep17.trans {t u w : State} (h₁ : Keep17 t u) (h₂ : Keep17 u w) : Keep17 t w :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.mem.trans h₁.mem, h₂.syms.trans h₁.syms,
    h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

/-- The comparison of `x16` with `j`. -/
abbrev cmpIdx (j : Nat) : Prog isa := .block [.subImm .x .x17 .x16 j]

theorem sub_beq {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    (BitVec.ofNat 64 i - BitVec.ofNat 64 j == 0) = decide (i = j) := by
  by_cases h : i = j
  · subst h; simp
  · have hne : BitVec.ofNat 64 i ≠ BitVec.ofNat 64 j := fun e => h (by
      have := congrArg BitVec.toNat e
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this)
    have : BitVec.ofNat 64 i - BitVec.ofNat 64 j ≠ 0 := fun e => hne (by
      have := congrArg (· + BitVec.ofNat 64 j) e
      simp only [BitVec.sub_add_cancel] at this
      exact this.trans (BitVec.zero_add _))
    simp only [h, decide_false, beq_eq_false_iff_ne]
    exact this

/-- A comparison of `x16` with `j`: the state kept but for `x17`, which is
zero iff `i = j`. -/
theorem cmpIdx_ok {t : State} {i j : Nat} (hi : i < 4096) (hj : j < 4096) (h16 : t.gpr .x16 = BitVec.ofNat 64 i) :
    WP isa (cmpIdx j) t fun t' => Keep17 t t' ∧ isa.eval (.zero .x .x17) t' = some (decide (i = j)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hj, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  show some (((t.write .x .x17 (t.read .x .x16 - BitVec.ofNat 64 j)).gpr .x17).setWidth 64 == 0) = _
  rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.setWidth_eq]
  show some ((t.gpr .x16).setWidth 64 - BitVec.ofNat 64 j == 0) = _
  rw [BitVec.setWidth_eq, h16, sub_beq (by omega) (by omega)]

/-- `byIdx b is` runs `b i`. -/
theorem byIdx_wp {b : Nat → Prog isa} {Q : State → Prop} : ∀ {is : List Nat} {i : Nat} {t : State},
    i ∈ is → (∀ j ∈ is, j < 4096) → t.gpr .x16 = BitVec.ofNat 64 i →
    (∀ t', Keep17 t t' → WP isa (b i) t' Q) → WP isa (byIdx b is) t Q
  | [], _, _, hi, _, _, _ => absurd hi List.not_mem_nil
  | [j], i, t, hi, _, _, h => by
    obtain rfl := List.mem_singleton.mp hi
    exact h t (Keep17.refl t)
  | j :: k :: is, i, t, hi, hlt, h16, h => by
    simp only [byIdx]
    refine WP.seq (WP.mono (cmpIdx_ok (hlt i hi) (hlt j (List.mem_cons_self ..)) h16) fun t' ⟨k', hz⟩ => ?_)
    refine WP.ite (M := isa) _ hz (fun hb => ?_) (fun hb => ?_)
    · rw [decide_eq_true_eq] at hb
      subst hb
      exact h t' k'
    · rw [decide_eq_false_iff_not] at hb
      exact byIdx_wp ((List.mem_cons.mp hi).resolve_left hb) (fun x hx => hlt x (List.mem_cons_of_mem _ hx))
        ((k'.gpr _ (by decide)).trans h16) fun t'' k'' => h t'' (k'.trans k'')

/-- `byIdx b is` in two runs whose `x16` is the index `idx a` of the
anchor: the comparisons from the same public `x16`, then `b (idx a)`. -/
theorem byIdx_ct {α : Type} {b : Nat → Prog isa} {Q : State → State → Prop} (idx : α → Nat) :
    ∀ {is : List Nat} {Φ : α → State → Prop},
    (∀ a t t', Φ a t → Keep17 t t' → Φ a t') →
    (∀ a t, Φ a t → idx a ∈ is ∧ t.gpr .x16 = BitVec.ofNat 64 (idx a)) →
    (∀ j ∈ is, j < 4096) →
    (∀ j ∈ is, RelCT isa (Two Φ) (cmpIdx j) fun _ _ => True) →
    (∀ j ∈ is, RelCT isa (Two fun a t => Φ a t ∧ idx a = j) (b j) Q) →
    RelCT isa (Two Φ) (byIdx b is) Q
  | [], _, _, hΦ, _, _, _ => RelCT.of_false fun _ _ ⟨a, h₁, _⟩ => by simpa using (hΦ a _ h₁).1
  | [j], _, _, hΦ, _, _, hb => (hb j (List.mem_singleton_self _)).mono
    (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨a, ⟨h₁, List.mem_singleton.mp (hΦ a _ h₁).1⟩,
      ⟨h₂, List.mem_singleton.mp (hΦ a _ h₁).1⟩, hsp⟩)
    fun _ _ h => h
  | j :: k :: is, Φ, hkeep, hΦ, hlt, hc, hb => by
    simp only [byIdx]
    have ih := byIdx_ct idx (is := k :: is) (Φ := fun a t => Φ a t ∧ idx a ≠ j)
      (fun a t t' ⟨h, hn⟩ k' => ⟨hkeep a t t' h k', hn⟩)
      (fun a t ⟨h, hn⟩ => ⟨(List.mem_cons.mp (hΦ a t h).1).resolve_left hn, (hΦ a t h).2⟩)
      (fun x hx => hlt x (List.mem_cons_of_mem _ hx))
      (fun x hx => (hc x (List.mem_cons_of_mem _ hx)).mono (fun _ _ => two_mono fun _ _ h => h.1) fun _ _ h => h)
      (fun x hx => (hb x (List.mem_cons_of_mem _ hx)).mono (fun _ _ => two_mono fun _ _ h => ⟨h.1.1, h.2⟩)
        fun _ _ h => h)
    refine RelCT.seq (two_post (Ψ := fun a t => Φ a t ∧ isa.eval (.zero .x .x17) t = some (decide (idx a = j)))
      (hc j (List.mem_cons_self ..)) fun a t h => ?_) (two_ite (fun a t₁ t₂ h₁ h₂ => ?_)
        ((hb j (List.mem_cons_self ..)).mono (fun _ _ => two_mono fun a t ⟨⟨h, hz⟩, he⟩ => ⟨h, ?_⟩) fun _ _ h => h)
        (ih.mono (fun _ _ => two_mono fun a t ⟨⟨h, hz⟩, he⟩ => ⟨h, ?_⟩) fun _ _ h => h))
    · obtain ⟨hm, h16⟩ := hΦ a t h
      exact WP.mono (cmpIdx_ok (hlt _ hm) (hlt j (List.mem_cons_self ..)) h16)
        fun t' ⟨k', hz⟩ => ⟨hkeep a t t' h k', hz⟩
    · rw [h₁.2, h₂.2]
    · rw [hz] at he; simpa using he
    · rw [hz] at he; simpa using he

end VG.Proof.Ecdsa.Rfc6979.AArch64
