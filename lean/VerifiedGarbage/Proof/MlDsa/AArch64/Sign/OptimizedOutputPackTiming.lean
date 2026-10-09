import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedOutputPack
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseOCT

namespace VG.Proof.MlDsa.AArch64.Sign.Output
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc seqR)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- Before the signature: an iteration passed, with `c̃`, `z` and `h`. -/
def IOi (p : Params) (D : Nat) (σ s : State) : Prop :=
  ∃ κ, St p D σ s ∧ bytesAt s.mem (pa s (sc oCT)) (cLen p) = CTv p σ κ ∧ Fam s (yBase p) p.ℓ (Zv p σ κ) ∧
    HFam s 5 p.k (Hv p σ κ) ∧ PassV p σ κ ∧ s.gpr .x24 = 1

/-- `c̃` and the first `r` polynomials of `z` in `sig`, of an iteration that passed. -/
def IOr (p : Params) (D : Nat) (r : Nat) (σ s : State) : Prop := ∃ κ, OS p D σ κ r s ∧ PassV p σ κ

/-- Two runs agree on their hints. -/
abbrev HJ (p : Params) (x y : State) : Prop := ∃ f, HFam x 5 p.k f ∧ HFam y 5 p.k f

section
variable {p : Params} {D : Nat}

theorem IOr.zr {r' : Nat} {σ s : State} (h : IOr p D r' σ s) {r : Nat} (hr : r < p.ℓ) :
    Reduced s.mem (pa s (yP p r)) ∧ InRange s.mem (pa s (yP p r)) (p.γ₁ - 1) p.γ₁ := by
  obtain ⟨κ, h, hpass⟩ := h
  have hzr := h.z r hr
  exact ⟨hzr.1, inRange_of_norm hzr (hpass.1 r hr) (Nat.sub_le _ _)⟩

theorem output_tr {P : Prims} (hP : PrimsOk P D) (hc : oChk p = true) {E : State → State → Prop} :
    RelCT isa (fun x y => RS p D E (IOi p D) x y ∧ HJ p x y) (output P p) fun _ _ => True := by
  have hc' := hc
  simp only [oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨cc, -⟩, cz⟩, ch⟩, hhp⟩, hbp⟩, hzl⟩, -⟩, -⟩, -⟩ := hc'
  unfold output
  refine RelCT.seq (R := fun x y => RS p D E (IOr p D 0) x y ∧ HJ p x y) (liftQ
    (F := fun s s' => ∀ f, HFam s 5 p.k f → HFam s' 5 p.k f)
    (fun σ s _ ⟨κ, hk, hct, hz, hh, hpass, h15⟩ =>
      WP.mono (outCopy_ok hc hk hct hz hh h15) fun _ h => ⟨⟨κ, h.1, hpass⟩, h.2⟩)
    (copy_tr (.inr rfl) rfl fun x y h => h.1.lrel fun σ s ⟨_, hk, _⟩ => hk)
    fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ ⟨f, hx, hy⟩ j₁ j₂ g₁ g₂ _ =>
      ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, f, g₁ f hx, g₂ f hy⟩) ?_
  refine RelCT.seq (R := fun x y => RS p D E (IOr p D p.ℓ) x y ∧ HJ p x y) (RelCT.mono (seqR_tr
    (Q := fun r x y => RS p D E (IOr p D r) x y ∧ HJ p x y) p.ℓ 0 fun r _ hr => liftQ
      (F := fun s s' => ∀ f, HFam s 5 p.k f → HFam s' 5 p.k f)
      (fun σ s _ ⟨κ, h, hpass⟩ => WP.mono (packZ_ok hP hc (by omega) h hpass) fun _ h => ⟨⟨κ, h.1, hpass⟩, h.2⟩)
      (RelCT.mono (bpAt_tr hP hbp hzl (cz r (by omega)).1.1) (fun x y ⟨h, _⟩ =>
        ⟨h.lrel fun σ s ⟨_, h, _⟩ => h.k, by
          obtain ⟨_, _, _, _, _, _, i₁, i₂⟩ := h
          exact ⟨i₁.zr (by omega), i₂.zr (by omega)⟩⟩) fun _ _ h => h)
      fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ ⟨f, hx, hy⟩ j₁ j₂ g₁ g₂ _ =>
        ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, f, g₁ f hx, g₂ f hy⟩)
    (fun _ _ h => h) fun x y h => by rwa [Nat.zero_add] at h) ?_
  refine RelCT.mono (hbpAt_tr hP hhp ch) (fun x y ⟨h, f, hx, hy⟩ => ⟨h.lrel fun σ s ⟨_, h, _⟩ => h.k, ?_⟩)
    fun _ _ _ => trivial
  obtain ⟨_, _, _, _, _, _, ⟨_, o₁, a₁⟩, ⟨_, o₂, a₂⟩⟩ := h
  exact ⟨hones_ok o₁ a₁, hones_ok o₂ a₂, hint_coeffs hx hy⟩

end
end VG.Proof.MlDsa.AArch64.Sign.Output
