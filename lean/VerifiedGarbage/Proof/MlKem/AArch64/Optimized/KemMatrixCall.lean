module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixPost

/-! # Instantiate paired matrix calls at encryption scratch addresses -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Spec.MlKem
open VG.Proof.MlKem
variable {P : KemLay} {L : Layout}

structure MatrixTable (P : KemLay) (L : Layout) (s₀ s : State) : Prop where
 artifact : Rej8.TableArtifact s.mem (s.syms "VG_MLKEM_REJ_SHUFFLE")
 readable : Covers [⟨s.syms "VG_MLKEM_REJ_SHUFFLE",4096⟩] (s.rd++s.wr)
 apart : (Region.mk (s.syms "VG_MLKEM_REJ_SHUFFLE") 4096).Disjoint ⟨kA s₀ L.sc,P.scl⟩

theorem MatrixTable.frame {s₀ s t : State} {rs : List Region} (h : MatrixTable P L s₀ s)
    (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hs : t.syms=s.syms) (hf : Frame rs s.mem t.mem)
    (sub : ∀r∈rs,Region.Sub r ⟨kA s₀ L.sc,P.scl⟩) : MatrixTable P L s₀ t := by
  refine ⟨?_,?_,?_⟩
  · rw [hs]; exact h.artifact.frame hf (fun r hh => h.apart.sub_right (sub r hh))
  · rw [hs,hr,hw]; exact h.readable
  · rw [hs]; exact h.apart

theorem scratch_sub {s₀ : State} (hp : Pre P L s₀) {o l : Nat} (hf : o+l≤SV P+48) :
    Region.Sub (R (kA s₀) L.sc o l) ⟨kA s₀ L.sc,P.scl⟩ := by
  have hh := hp.fs hf
  rw [hp.scl] at hh
  exact R.sub hh

theorem pair_scratch {s₀ : State} (hp : Pre P L s₀) {e : Nat} (he : e+1<P.k*P.k) :
    ∀r∈pairWrites L s₀ e,Region.Sub r ⟨kA s₀ L.sc,P.scl⟩ := by
  have hw := hp.wf
  intro r hr; simp only [pairWrites,Paired.stepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact scratch_sub hp (by lom)

theorem last_scratch {s₀ : State} (hp : Pre P L s₀) {e : Nat} (he : e<P.k*P.k) :
    ∀r∈lastWrites L s₀ e,Region.Sub r ⟨kA s₀ L.sc,P.scl⟩ := by
  have hw := hp.wf
  intro r hr; simp only [lastWrites,Paired.fullWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl <;> exact scratch_sub hp (by lom)

theorem pair_context {s₀ s : State} (hp : Pre P L s₀) {e : Nat} (he : e+1<P.k*P.k)
    (h : KB P L s₀ s) (tb : MatrixTable P L s₀ s) :
    Paired.Context (sA L s₀ SS) (aP L s₀ e) (aP L s₀ (e+1)) (s.syms "VG_MLKEM_REJ_SHUFFLE") s := by
  have hw := hp.wf
  refine ⟨cov_s hp h (by lom),cov_s hp h (by lom),cov_s hp h (by lom),
    sdisj hp (by lom) (by lom) (by lom),sdisj hp (by lom) (by lom) (by lom),
    sdisj hp (by lom) (by lom) (by lom),tb.artifact,tb.readable,?_,?_,?_⟩ <;>
    exact tb.apart.sub_right (scratch_sub hp (by lom))

theorem singleton_context {s₀ s : State} (hp : Pre P L s₀) {e : Nat} (he : e<P.k*P.k)
    (h : KB P L s₀ s) (tb : MatrixTable P L s₀ s) :
    Paired.SingleContext (sA L s₀ SS) (aP L s₀ e) (s.syms "VG_MLKEM_REJ_SHUFFLE") s := by
  have hw := hp.wf
  refine ⟨cov_s hp h (by lom),cov_s hp h (by lom),sdisj hp (by lom) (by lom) (by lom),
    tb.artifact,tb.readable,?_,?_⟩ <;> exact tb.apart.sub_right (scratch_sub hp (by lom))

theorem paired_step {w16 : Bool} {s₀ s : State} (hp : Pre P L s₀) {mA : Mem} {ρ : List Byte} {e : Nat}
    (he : e+1<P.k*P.k) (h : BInvW w16 P L s₀ mA ρ e s) (tb : MatrixTable P L s₀ s) :
    WP isa (Impl.MlKem.AArch64.Paired.pair P false e w16) s fun t =>
      BInvW w16 P L s₀ mA ρ (e+2) t ∧ MatrixTable P L s₀ t := by
  have hw := hp.wf
  rw [Paired.pair_iff]
  refine WP.mono_syms (Paired.pairCode_ok (by decide) (by decide) (by decide)
    (by change AH+1024*e<65536; lom) (by change AH+1024*(e+1)<65536; lom) (e28 h.kb SS) (e28 h.kb SB) (e28 h.kb (AH+1024*e)) (e28 h.kb (AH+1024*(e+1)))
    (fun j hj => ?_) (sdisj hp (by lom) (by lom) (by decide)) (pair_context hp he h.kb tb) rfl
    (by
      rw [h.acc]
      by_cases hh : okR P ρ e
      · rw [ite_eq_left hh]; exact Or.inr rfl
      · rw [ite_eq_right hh]; exact Or.inl rfl)) fun t ht sy => ?_
  · rw [ptr_add]
    exact in_R (cov_sr hp h.kb (o := SB) (l := 32) (by lom)) (k := 8*j) (by omega) (by omega)
  · have post := ht.outcome (by lom) (by lom)
    have seed {i : Nat} : Paired.seedBytes s.mem (sA L s₀ SB) i P.k=matSeed ρ (i/P.k) (i%P.k) := by
      simp only [Paired.seedBytes,h.rho,matSeed]
    rw [seed,seed] at post
    exact ⟨h.paired hp he post,tb.frame post.keep.rd post.keep.wr sy post.frame (pair_scratch hp he)⟩

theorem singleton_step {w16 : Bool} {s₀ s : State} (hp : Pre P L s₀) {mA : Mem} {ρ : List Byte} {e : Nat}
    (he : e<P.k*P.k) (h : BInvW w16 P L s₀ mA ρ e s) (tb : MatrixTable P L s₀ s) :
    WP isa (Paired.lastCode SB SS e P.k (AH+1024*e) w16) s fun t =>
      BInvW w16 P L s₀ mA ρ (e+1) t ∧ MatrixTable P L s₀ t := by
  have hw := hp.wf
  refine WP.mono_syms (Paired.lastCode_ok (by decide) (by decide) (by decide) (by lom) (by lom) (by lom)
    (e28 h.kb SS) (e28 h.kb SB) (e28 h.kb (AH+1024*e)) (fun j hj => ?_)
    (sdisj hp (by lom) (by lom) (by decide)) (sdisj hp (by lom) (by lom) (by lom))
    (singleton_context hp he h.kb tb) rfl (by
      rw [h.acc]
      by_cases hh : okR P ρ e
      · rw [ite_eq_left hh]; exact Or.inr rfl
      · rw [ite_eq_right hh]; exact Or.inl rfl)) fun t ht sy => ?_
  · rw [ptr_add]
    exact in_R (cov_sr hp h.kb (o := SB) (l := 32) (by lom)) (k := 8*j) (by omega) (by omega)
  · have post := ht.outcome
    have seed : Paired.seedBytes s.mem (sA L s₀ SB) e P.k=matSeed ρ (e/P.k) (e%P.k) := by
      simp only [Paired.seedBytes,h.rho,matSeed]
    rw [seed] at post
    exact ⟨h.singleton hp he post,tb.frame post.keep.rd post.keep.wr sy post.frame (last_scratch hp he)⟩

end VG.Proof.MlKem.AArch64.Kem
