module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeBase
import VerifiedGarbage.Proof.Ffdh.X86.StagesCT
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Ffdh.X86.Domain
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeExp

/-!
# The FFDH candidate on i686: what its timing is checked from

The contract releases the tape, so every value the candidate branches on is
public; the taint analysis, which keeps only the arguments, `edi` and `esp`
public (`τA`), cannot see that. Each run is pinned to the same public
values: registers that hold them are public in `τP rs` (`pinned_both`), and
a branch or a loop condition that both runs evaluate alike takes the same
side (`ite_fixed`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both)

/-- `τA`, with the registers `rs` public too. -/
def τP (rs : List Reg) : VG.X86.Taint.T := { regs := .ofList ([.edi, .esp] ++ rs), flags := false, argLen := 76 }

/-- The taint analysis passes `p` with the registers `rs` public. -/
abbrev PCheck (rs : List Reg) (p : Prog isa) : Prop :=
  (VG.Taint.check taint (τP rs) p (VG.Taint.hintOf taint (τP rs) p)).isSome = true

theorem τP_wf {rs : List Reg} {s : State} (A : ArgsOk s) : VG.X86.Taint.Wf (τP rs) s :=
  VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => A, fun _ h => (List.not_mem_nil h).elim⟩

variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32}

/-- Two runs that agree on the registers `rs`. -/
theorem agreeP {rs : List Reg} {s₁ s₂ : State} (R₁ : Run Ex base bytes len args sp s₁)
    (R₂ : Run Ex base bytes len args sp s₂) (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.X86.Taint.Agree (τP rs) s₁ s₂ := by
  have G := R₁.agree R₂
  refine ⟨⟨fun r hr' => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, τP_wf R₁.2.1, τP_wf R₂.2.1,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => R₁.2.2.trans R₂.2.2.symm,
    fun k h4 hk => G.argMem k h4 hk⟩
  simp only [τP, RegSet.mem_ofList, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with (rfl | rfl) | hr'
  · exact G.rf.1 _ (by simp [τA])
  · exact R₁.2.2.trans R₂.2.2.symm
  · exact hr _ hr'

/-- Code the taint analysis checks with the registers `rs` public, which the runs pin. -/
theorem pinned_both {rs : List Reg} {P F : State → Prop} {c : Prog isa}
    (hP : ∀ x, P x → Run Ex base bytes len args sp x)
    (hv : ∀ x y, P x → P y → ∀ r ∈ rs, x.gpr r = y.gpr r)
    (hc : PCheck rs c)
    (hw : ∀ x, P x → WP isa c x F) : RelCT isa (Both P) c (Both F) :=
  relCT_both (RelCT.taint (A := taint) (τP rs) (fun _ _ h => agreeP (hP _ h.1) (hP _ h.2) (hv _ _ h.1 h.2)) hc) hw

/-- Code the taint analysis checks with the registers `rs` public, which the runs pin, at the end. -/
theorem pinned_end {rs : List Reg} {P : State → Prop} {c : Prog isa}
    (hP : ∀ x, P x → Run Ex base bytes len args sp x)
    (hv : ∀ x y, P x → P y → ∀ r ∈ rs, x.gpr r = y.gpr r)
    (hc : PCheck rs c) :
    RelCT isa (Both P) c fun _ _ => True :=
  RelCT.taint (A := taint) (τP rs) (fun _ _ h => agreeP (hP _ h.1) (hP _ h.2) (hv _ _ h.1 h.2)) hc

/-- Two postconditions of the same run. -/
theorem wp_and {c : Prog isa} {s : State} {Q₁ Q₂ : State → Prop} (h₁ : WP isa c s Q₁) (h₂ : WP isa c s Q₂) :
    WP isa c s fun t => Q₁ t ∧ Q₂ t := by
  obtain ⟨t₁, s₁, e₁, q₁⟩ := h₁
  obtain ⟨t₂, s₂, e₂, q₂⟩ := h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ e₂
  exact ⟨_, _, e₁, q₁, q₂⟩

/-- A branch whose condition the runs fix: only one side runs. -/
theorem ite_fixed {P : State → Prop} {c : Cond} {b : Bool} (hb : ∀ x, P x → isa.eval c x = some b)
    {th el : Prog isa} {Q : State → State → Prop}
    (ht : b = true → RelCT isa (Both P) th Q) (he : b = false → RelCT isa (Both P) el Q) :
    RelCT isa (Both P) (.ite c th el) Q := by
  refine VG.RelCT.ite (fun x y h => (hb _ h.1).trans (hb _ h.2).symm) ?_ ?_
  · cases b
    · exact VG.RelCT.of_false fun x y h => by rw [hb _ h.1.1] at h; cases h.2
    · exact (ht rfl).mono (fun _ _ h => h.1) fun _ _ h => h
  · cases b
    · exact (he rfl).mono (fun _ _ h => h.1) fun _ _ h => h
    · exact VG.RelCT.of_false fun x y h => by rw [hb _ h.1.1] at h; cases h.2

/-- A relation that holds for some value of a parameter. -/
theorem relCT_exists {α : Sort _} {P : α → State → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : ∀ a, RelCT isa (P a) c Q) : RelCT isa (fun x y => ∃ a, P a x y) c Q :=
  fun _ _ _ _ _ _ ⟨a, hp⟩ e₁ e₂ => h a _ _ _ _ _ _ hp e₁ e₂

/-- A fact every pair of related runs gives. -/
theorem relCT_of_imp {A : Prop} {P Q : State → State → Prop} {c : Prog isa} (h : A → RelCT isa P c Q)
    (hA : ∀ x y, P x y → A) : RelCT isa P c Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h (hA _ _ hp) _ _ _ _ _ _ hp e₁ e₂

end VG.Proof.Ffdh.X86.Cand
