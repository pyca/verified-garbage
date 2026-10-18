module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemURow
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.LayoutAll

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

theorem noise_einv {s₀ s : State} (hp : Pre P L s₀) (hr : Noise.Room P)
    {kC co : Nat} {mE mB : Mem} {v : BitVec 64} {rv mv : List Byte}
    (h : EInv P L s₀ kC co mE mB v rv mv 0 0 s) :
    WP isa (Impl.MlKem.AArch64.Noise.noiseAll P false) s fun t =>
      Kept (Noise.allWrites P false (kA s₀ L.sc)) s t ∧
      EInv P L s₀ kC co t.mem mB v rv mv P.k 0 t ∧ Errors P L s₀ rv t := by
  have hw := hp.wf
  have hroom := hr.kem
  have hc : Covers [⟨kA s₀ L.sc,P.scl⟩] s.wr := by
    have hh := cov_w hp h.kb ⟨hp.scw,hp.scb⟩ (o := 0) (l := P.scl) (by rw [hp.scl]; omega)
    simpa only [R,ptr_zero] using hh
  refine WP.mono (Noise.noiseAll_layout hw hr false h.kb.x28 hc) fun t ⟨kt,pt⟩ => ?_
  have keepB : ∀o l, o+l≤SS → o+l≤P.scl-1024*P.k →
      (Spec.Sha3.bytesAt t.mem (sA L s₀ o) l=Spec.Sha3.bytesAt s.mem (sA L s₀ o) l) := by
    intro o l ho ht
    exact bytesAt_frame kt.frame (noise_far hp hr hp.scb (hp.fs (by lom)) (.inr (by lom))) (by lom)
  refine ⟨kt,⟨noise_kb hp hr h.kb kt,(kt.cs .x24 (by decide) (by decide)).trans h.x24,
    (keepB RB 32 (by decide) (by lom)).trans h.r,
    (keepB MB 32 (by decide) (by lom)).trans h.m,?_,?_,fun _ hj => by omega,Frame.refl _ _⟩,?_⟩
  · intro i hi j hj
    have hij := ij_lt hi hj
    have far := noise_far hp hr hp.scb (hp.fs (by lom : aOff P i j+1024≤SV P+48))
      (.inr (by lom))
    exact ⟨reduced_frame kt.frame far (h.a i hi j hj).1,
      (polyAt_frame kt.frame far).trans (h.a i hi j hj).2⟩
  · intro j hj
    have p := pt j (by omega)
    show PolyIs t.mem (sA L s₀ (yOff P j)) _
    simpa only [Noise.outOff,ite_eq_left hj,Bool.false_eq_true,ite_false,Noise.sampled,Noise.seedOff,
      Noise.transformed,decide_eq_true_eq.mpr hj,Bool.false_or,ite_true,h.r,encY,cbd] using p
  · intro j hj
    have p := pt (P.k+j) (by omega)
    have hn : ¬P.k+j<P.k := by omega
    simpa only [Noise.outOff,ite_eq_right hn,Nat.add_sub_cancel_left,Noise.sampled,Noise.seedOff,
      Noise.transformed,decide_eq_false_iff_not.mpr hn,Bool.false_or,Bool.false_eq_true,ite_false,h.r,cbd] using p

end VG.Proof.MlKem.AArch64.Kem
