module
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixFrame


/-! # Preserve the immutable rejection table across key-generation matrix entries -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Spec.MlKem
variable {P : KemLay}

structure MatrixTable (P : KemLay) (s₀ s : State) : Prop where
 artifact : Rej8.TableArtifact s.mem (s.syms "VG_MLKEM_REJ_SHUFFLE")
 readable : Covers [⟨s.syms "VG_MLKEM_REJ_SHUFFLE",4096⟩] (s.rd++s.wr)
 apart : (Region.mk (s.syms "VG_MLKEM_REJ_SHUFFLE") 4096).Disjoint ⟨kA s₀ 3,P.scl⟩

theorem MatrixTable.frame {s₀ s t : State} {rs : List Region} (h : MatrixTable P s₀ s)
    (hr : t.rd=s.rd) (hw : t.wr=s.wr) (hs : t.syms=s.syms) (hf : Frame rs s.mem t.mem)
    (sub : ∀r∈rs,Region.Sub r ⟨kA s₀ 3,P.scl⟩) : MatrixTable P s₀ t := by
  refine ⟨?_,?_,?_⟩
  · rw [hs]; exact h.artifact.frame hf (fun r hh => h.apart.sub_right (sub r hh))
  · rw [hs,hr,hw]; exact h.readable
  · rw [hs]; exact h.apart

theorem scratch_sub {s₀ : State} (hp : Pre P s₀) {o l : Nat} (hf : o+l≤SV P+48) :
    Region.Sub (R (kA s₀) 3 o l) ⟨kA s₀ 3,P.scl⟩ := by
  have hw := hp.wf
  exact R.sub (by lom)

theorem pair_scratch {s₀ : State} (hp : Pre P s₀) {e : Nat} (he : e+1<P.k*P.k) :
    ∀r∈pairWrites s₀ e,Region.Sub r ⟨kA s₀ 3,P.scl⟩ := by
  have hw := hp.wf
  intro r hr; simp only [pairWrites,Paired.stepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact scratch_sub hp (by lom)

theorem last_scratch {s₀ : State} (hp : Pre P s₀) {e : Nat} (he : e<P.k*P.k) :
    ∀r∈lastWrites s₀ e,Region.Sub r ⟨kA s₀ 3,P.scl⟩ := by
  have hw := hp.wf
  intro r hr; simp only [lastWrites,Paired.fullWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl <;> exact scratch_sub hp (by lom)

end VG.Proof.MlKem.AArch64.KeyGen
