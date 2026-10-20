module

public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.LayoutAll
public import VerifiedGarbage.Proof.MlKem.AArch64.KemOps
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Offsets

/-! # Paired encryption noise preserves read inputs and caller state -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
variable {P : KemLay} {L : Layout}

theorem noise_far {s₀ : State} (hp : Pre P L s₀) (hr : Noise.Room P) {b o l : Nat}
    (hb : b<L.nb) (hf : o+l≤L.len b)
    (hs : b≠L.sc ∨ ((o+l≤SS ∨ SS+2048≤o) ∧ (o+l≤NS ∨ NS+1024≤o) ∧
      (o+l≤YH P ∨ EP P≤o) ∧ o+l≤P.scl-1024*P.k)) :
    ∀r∈Noise.allWrites P false (kA s₀ L.sc), (R (kA s₀) b o l).Disjoint r := by
  have hw := hp.wf
  have hd : b=L.sc ∨ L.nrd≤b ∨ L.nrd≤L.sc := .inr (.inr hp.scw)
  apply Noise.allWrites_apart
  · change (R (kA s₀) b o l).Disjoint (R (kA s₀) L.sc SS 2048)
    exact hp.args.rdisj hb hp.scb hf (hp.fs (by lom)) hd (by rcases hs with hs | hs <;> omega)
  · change (R (kA s₀) b o l).Disjoint (R (kA s₀) L.sc NS 1024)
    exact hp.args.rdisj hb hp.scb hf (hp.fs (by lom)) hd (by rcases hs with hs | hs <;> omega)
  · intro j hj
    have fits : Noise.outOff P false j+1024≤L.len L.sc := by
      rw [hp.scl]; exact Noise.outOff_fits hw hr false hj
    apply hp.args.rdisj hb hp.scb hf fits hd
    rcases hs with hs | ⟨hs,hn,hp',ht⟩
    · exact .inl hs
    · unfold Noise.outOff
      split
      · simp only [Bool.false_eq_true,ite_false]
        lom
      · unfold Impl.MlKem.AArch64.Noise.noiseOff
        omega

theorem noise_kb {s₀ s t : State} (hp : Pre P L s₀) (hr : Noise.Room P) (h : KB P L s₀ s)
    (ht : Kept (Noise.allWrites P false (kA s₀ L.sc)) s t) : KB P L s₀ t := by
  have hw := hp.wf
  have hroom := hr.kem
  refine h.call ht fun r hh => ⟨?_,?_⟩
  · exact noise_far hp hr hp.scb hp.sv (.inr (by lom)) r hh
  · intro b hb
    have hbn : b<L.nb := by have := hp.scw; have := hp.scb; omega
    simpa only [R,ptr_zero] using noise_far hp hr hbn (o := 0) (l := L.len b) (by omega)
      (.inl (by have := hp.scw; omega)) r hh

def Errors (P : KemLay) (L : Layout) (s₀ : State) (rv : List Byte) (s : State) : Prop :=
  ∀j<P.k, PolyIs s.mem (sA L s₀ (Impl.MlKem.AArch64.Noise.noiseOff P j)) (cbd rv (P.k+j))

end VG.Proof.MlKem.AArch64.Kem
