import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedOutputPack
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseOCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedOutputCorrect

/-! ## From `OptimizedOutputPackTiming.lean` -/

section

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

end

/-! ## From `OptimizedOutputTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (seqR)
open VG.Proof.MlDsa.AArch64.Optimized

def ConversionI (p : Params) (S : Nat) (lo hi : Int) (r : Nat) (σ s : State) : Prop :=
  ∃κ,AcceptedConversion p S σ κ lo hi r s ∧ PassV p σ κ

theorem conversionReady {p : Params} {S : Nat} {σ s : State} {κ r : Nat} {lo hi : Int}
    (hp : Ok3 p) (hr : r<p.ℓ) (hl : -(q:Int)<lo) (hh : hi<(q:Int))
    (h : AcceptedConversion p S σ κ lo hi r s) : Response.CanonicalizeCallReady (yP p r) s := by
  have hc := canonicalizeZChk_ok hp r hr
  simp only [canonicalizeZChk,Bool.and_eq_true] at hc
  exact ⟨h.z.rooted.1.lay.nwp hc.1.1,centered_of_signed (h.z.pending r (by omega) hr) hl hh,
    h.z.rooted.1.lay.cR hc.1.1,h.z.rooted.1.lay.cW hc.1.2⟩

theorem conversionStep_tr {p : Params} {S r : Nat} {lo hi : Int} {E : State → State → Prop}
    (hp : Ok3 p) (hr : r<p.ℓ) (hl : -(q:Int)<lo) (hh : hi<(q:Int)) :
    RelCT isa (fun x y => RS p S E (ConversionI p S lo hi r) x y ∧ HJ p x y)
      (Impl.MlDsa.AArch64.Sign.Optimized.canonicalizeZ p r)
      (fun x y => RS p S E (ConversionI p S lo hi (r+1)) x y ∧ HJ p x y) := by
  refine liftQ (J := ConversionI p S lo hi (r+1)) (Q₀ := fun _ _ => True) (F := fun s t => ∀f,HFam s 5 p.k f → HFam t 5 p.k f) ?_ ?_ ?_
  · intro σ s _ ⟨κ,h,hpass⟩
    have hc := conversionOutputChk_ok hp
    simp only [conversionOutputChk,List.all_eq_true,List.mem_range,Bool.and_eq_true] at hc
    refine WP.mono (canonicalizeZ_step_post hr (canonicalizeZChk_ok hp r hr)
      (canonicalizeZKeepChk_ok hp) hl hh h.z) fun t ⟨hz,hpost⟩ => ?_
    have keepHints : ∀f,HFam s 5 p.k f → HFam t 5 p.k f :=
      fun _ hf => HFam.keep h.z.rooted.1.lay hpost (hc r hr).2 hf
    exact ⟨⟨κ,⟨hz,(h.z.rooted.1.lay.keepBytes hpost (hc r hr).1).trans h.ct,
      keepHints _ h.hints⟩,hpass⟩,fun _ hf => keepHints _ hf⟩
  · apply Response.canonicalizeAt_tr (S := S) (ptr_ok (by change Reg.x28∈keptRegs; decide))
    intro x y hxy
    have L := hxy.1.lrel (fun _ _ ⟨_,h,_⟩ => h.z.rooted.1)
    obtain ⟨_,_,_,_,_,_,⟨_,hx,_⟩,⟨_,hy,_⟩⟩ := hxy.1
    exact ⟨conversionReady hp hr hl hh hx,conversionReady hp hr hl hh hy,
      L.pa (by change Reg.x28∈bases; decide),L.sp⟩
  · intro σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ hHints j₁ j₂ g₁ g₂ _
    obtain ⟨f,hx,hy⟩ := hHints
    exact ⟨⟨σ₁,σ₂,p₁,p₂,hpub,he,j₁,j₂⟩,f,g₁ f hx,g₂ f hy⟩

theorem optimizedOutput_tr {P : Prims} {p : Params} {S : Nat} {lo hi : Int}
    {E : State → State → Prop} (hP : PrimsOk P S) (hp : Ok3 p)
    (hl : -(q:Int)<lo) (hh : hi<(q:Int)) :
    RelCT isa (fun x y => RS p S E (ConversionI p S lo hi 0) x y ∧ HJ p x y)
      (Impl.MlDsa.AArch64.Sign.Optimized.output P p) fun _ _ => True := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.output
  refine RelCT.seq (R := fun x y => RS p S E (ConversionI p S lo hi p.ℓ) x y ∧ HJ p x y) ?_ ?_
  · simpa only [Nat.zero_add] using seqR_tr
      (Q := fun r x y => RS p S E (ConversionI p S lo hi r) x y ∧ HJ p x y)
      p.ℓ 0 (fun r _ hr => conversionStep_tr hp (by omega) hl hh)
  · refine RelCT.mono (Output.output_tr hP (Output.oChk_ok hp) (E := E)) ?_ (fun _ _ h => h)
    intro x y ⟨h,hj⟩
    refine ⟨h.mono (fun _ _ he => he) ?_,hj⟩
    intro σ s ⟨κ,hs,hpass⟩
    exact ⟨κ,hs.z.rooted.1,hs.ct,hs.z.converted,hs.hints,hpass,hs.z.flag⟩

end VG.Proof.MlDsa.AArch64.Sign

end
