module

public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.LayoutAll
public import VerifiedGarbage.Proof.MlKem.AArch64.KgCommon
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Offsets

/-! # Paired noise preserves key-generation inputs and caller state -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
variable {P : KemLay}

theorem noise_far {s₀ : State} (hp : Pre P s₀) (hr : Noise.Room P) {b o l : Nat}
    (hb : b<4) (hf : o+l≤kL P b)
    (hs : b≠3 ∨ ((o+l≤SS ∨ SS+2048≤o) ∧ (o+l≤NS ∨ NS+1024≤o) ∧
      (o+l≤SH P ∨ EP P≤o) ∧ o+l≤P.scl-1024*P.k)) :
    ∀r∈Noise.allWrites P true (kA s₀ 3), (R (kA s₀) b o l).Disjoint r := by
  have hw := hp.wf
  apply Noise.allWrites_apart
  · change (R (kA s₀) b o l).Disjoint (R (kA s₀) 3 SS 2048)
    exact hp.args.rdisj hb (by decide) hf (by kl) (by rcases hs with hs | hs <;> omega)
  · change (R (kA s₀) b o l).Disjoint (R (kA s₀) 3 NS 1024)
    exact hp.args.rdisj hb (by decide) hf (by kl) (by rcases hs with hs | hs <;> omega)
  · intro j hj
    have fits := Noise.outOff_fits hw hr true hj
    apply hp.args.rdisj hb (by decide) hf fits
    rcases hs with hs | ⟨hs,hn,hp',ht⟩
    · exact .inl hs
    · unfold Noise.outOff
      split
      · simp only [ite_true]
        lom
      · have := Noise.noise_past_kg hr (j-P.k)
        unfold Impl.MlKem.AArch64.Noise.noiseOff
        omega

theorem noise_kb {s₀ s t : State} (hp : Pre P s₀) (hr : Noise.Room P) (h : KB P s₀ s)
    (ht : Kept (Noise.allWrites P true (kA s₀ 3)) s t) : KB P s₀ t := by
  have hw := hp.wf
  have hroom := hr.kg
  have h1 := noise_far hp hr (b := 3) (o := SV P) (l := 48) (by decide) hp.sv (.inr (by lom))
  have h2 := noise_far hp hr (b := 0) (o := 0) (l := 64) (by decide) (by kl) (.inl (by decide))
  exact h.call ht fun r hh => ⟨h1 r hh,h2 r hh⟩

end VG.Proof.MlKem.AArch64.KeyGen
