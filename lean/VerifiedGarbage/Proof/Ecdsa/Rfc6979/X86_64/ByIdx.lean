module

public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.X86_64
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# Deterministic ECDSA on x86-64: the choice of the code for the hash function of a table

`byIdx b is` runs `b i` for the index `i` in `r11`, by comparisons with each
of `is`: `byIdx_wp` from the state before the comparisons, `byIdx_ct` in two
runs whose `r11` is the same, each comparison keeping the state but its
flags.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- The comparison of `r11` with `j`. -/
abbrev cmpIdx (j : Nat) : Prog isa := .block [.alu .cmp .r11 (.imm (BitVec.ofNat 32 j))]

/-- What the comparisons with the indices `is` write and load: the flags. -/
def CmpOk (is : List Nat) : Prop :=
  ∀ j ∈ is, j < 2 ^ 31 ∧ VG.Proof.MlKem.X86_64.writesOnly [.r11] (cmpIdx j) = true ∧
    (cmpIdx j).allInstrs (fun i => !loadsMxcsr i) = true

theorem cmpOk_idxs : CmpOk idxs := by unfold CmpOk idxs; decide

/-- `WP.mono` that also keeps the symbols and MXCSR. -/
theorem WP.mono_mxs {c : Prog isa} (hc : c.allInstrs (fun i => !loadsMxcsr i) = true) {s : State}
    {Q R : State → Prop} (h : WP isa c s Q) (hq : ∀ s', Q s' → s'.syms = s.syms → s'.mxcsr = s.mxcsr → R s') :
    WP isa c s R :=
  WP.mono_mx hc (X86_64.WP.mono_syms h fun s' q sy => (⟨q, sy⟩ : Q s' ∧ s'.syms = s.syms))
    fun s' ⟨q, sy⟩ hx => hq s' q sy hx

/-- A comparison of `r11` with `j`: the state kept but for the flags. -/
theorem cmpIdx_ok {t : State} {i j : Nat} (hi : i < 2 ^ 31) (hj : j < 2 ^ 31)
    (hw : VG.Proof.MlKem.X86_64.writesOnly [.r11] (cmpIdx j) = true) (h11 : t.gpr .r11 = BitVec.ofNat 64 i) :
    WP isa (.block [.alu .cmp .r11 (.imm (BitVec.ofNat 32 j))]) t fun t' => Keep [] t t' ∧ t'.mem = t.mem ∧
      t'.zf = some (decide (i = j)) ∧ t'.syms = t.syms := by
  refine WP.of_syms <| WP.mono (WP.keep [.r11] (Q := fun t' => t'.mem = t.mem ∧ t'.zf = some (decide (i = j)) ∧
    t'.gpr .r11 = t.gpr .r11) ?_ hw)
    fun t' ⟨⟨hm, hz, h11'⟩, k⟩ sy => ⟨⟨fun r _ => if e : r = .r11 then e ▸ h11' else k.gpr (by simpa using e), k.2.1,
      k.2.2⟩, hm, hz, sy⟩
  xrun [h11, VG.Proof.MlKem.X86_64.sx_ofNat hj,
    VG.Proof.Bignum.X86_64.ofNat_sub_beq (show i < 2 ^ 64 by omega) (show j < 2 ^ 64 by omega)]

/-- `byIdx b is` runs `b i`. -/
theorem byIdx_wp {b : Nat → Prog isa} {Q : State → Prop} : ∀ {is : List Nat} {i : Nat} {t : State},
    i ∈ is → CmpOk is → t.gpr .r11 = BitVec.ofNat 64 i →
    (∀ t', Keep [] t t' → t'.mem = t.mem → t'.syms = t.syms → t'.mxcsr = t.mxcsr → WP isa (b i) t' Q) →
    WP isa (byIdx b is) t Q
  | [], _, _, hi, _, _, _ => absurd hi (List.not_mem_nil)
  | [j], i, t, hi, _, _, h => by
    obtain rfl := List.mem_singleton.mp hi
    exact h t ⟨fun _ _ => rfl, rfl, rfl⟩ rfl rfl rfl
  | j :: k :: is, i, t, hi, hlt, h11, h => by
    have hil := (hlt i hi).1
    obtain ⟨hjl, hjw, hjm⟩ := hlt j (List.mem_cons_self ..)
    simp only [byIdx]
    refine WP.seq (WP.mono_mx hjm (cmpIdx_ok hil hjl hjw h11) fun t' ⟨k', hm, hz, sy⟩ hx => ?_)
    refine WP.ite (M := isa) _ (show isa.eval .e t' = _ from hz) (fun hb => ?_) (fun hb => ?_)
    · rw [decide_eq_true_eq] at hb
      subst hb
      exact h t' k' hm sy hx
    · rw [decide_eq_false_iff_not] at hb
      have hi' : i ∈ k :: is := (List.mem_cons.mp hi).resolve_left hb
      exact byIdx_wp hi' (fun x hx => hlt x (List.mem_cons_of_mem _ hx)) ((k'.gpr (by simp)).trans h11)
        fun t'' k'' hm' sy' hx' => h t'' ⟨fun r hr => (k''.gpr hr).trans (k'.gpr hr), k''.2.1.trans k'.2.1,
          k''.2.2.trans k'.2.2⟩ (hm'.trans hm) (sy'.trans sy) (hx'.trans hx)

/-- `byIdx b is` in two runs whose `r11` is the index `idx a` of the
anchor: the comparisons from the same public `r11`, then `b (idx a)`. -/
theorem byIdx_ct {α : Type} {b : Nat → Prog isa} {Q : State → State → Prop} (idx : α → Nat) :
    ∀ {is : List Nat} {Φ : α → State → Prop},
    (∀ a t t', Φ a t → Keep [] t t' → t'.mem = t.mem → t'.syms = t.syms → Φ a t') →
    (∀ a t, Φ a t → idx a ∈ is ∧ t.gpr .r11 = BitVec.ofNat 64 (idx a)) →
    CmpOk is →
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
      (fun a t t' ⟨h, hn⟩ k' hm sy => ⟨hkeep a t t' h k' hm sy, hn⟩)
      (fun a t ⟨h, hn⟩ => ⟨(List.mem_cons.mp (hΦ a t h).1).resolve_left hn, (hΦ a t h).2⟩)
      (fun x hx => hlt x (List.mem_cons_of_mem _ hx))
      (fun x hx => (hc x (List.mem_cons_of_mem _ hx)).mono (fun _ _ => two_mono fun _ _ h => h.1) fun _ _ h => h)
      (fun x hx => (hb x (List.mem_cons_of_mem _ hx)).mono (fun _ _ => two_mono fun _ _ h => ⟨h.1.1, h.2⟩)
        fun _ _ h => h)
    refine RelCT.seq (two_post (Ψ := fun a t => Φ a t ∧ t.zf = some (decide (idx a = j)))
      (hc j (List.mem_cons_self ..)) fun a t h => ?_) (two_ite (fun a t₁ t₂ h₁ h₂ => ?_)
        ((hb j (List.mem_cons_self ..)).mono (fun _ _ => two_mono fun a t ⟨⟨h, hz⟩, he⟩ => ⟨h, ?_⟩) fun _ _ h => h)
        (ih.mono (fun _ _ => two_mono fun a t ⟨⟨h, hz⟩, he⟩ => ⟨h, ?_⟩) fun _ _ h => h))
    · obtain ⟨hm, h11⟩ := hΦ a t h
      exact WP.mono (cmpIdx_ok (hlt _ hm).1 (hlt j (List.mem_cons_self ..)).1
        (hlt j (List.mem_cons_self ..)).2.1 h11)
        fun t' ⟨k', hm', hz, sy⟩ => ⟨hkeep a t t' h k' hm' sy, hz⟩
    · show t₁.zf = t₂.zf; rw [h₁.2, h₂.2]
    · rw [show isa.eval .e t = t.zf from rfl, hz] at he
      simpa using he
    · rw [show isa.eval .e t = t.zf from rfl, hz] at he
      simpa using he

end VG.Proof.Ecdsa.Rfc6979.X86_64
