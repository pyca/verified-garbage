module

public import VerifiedGarbage.Proof.MlKem.AArch64.KemB
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullSample
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Context
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Restore

/-! # Paired matrix writes preserve the encryption caller and prior entries -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Spec.MlKem
variable {P : KemLay} {L : Layout}

def pairWrites (L : Layout) (s₀ : State) (e : Nat) : List Region :=
  Paired.stepWrites (sA L s₀ SS) (aP L s₀ e) (aP L s₀ (e+1))

def lastWrites (L : Layout) (s₀ : State) (e : Nat) : List Region :=
  Paired.fullWrites (sA L s₀ SS) (aP L s₀ e)

theorem pair_far {s₀ : State} (hp : Pre P L s₀) {e : Nat} (he : e+1<P.k*P.k)
    {o l : Nat} (hf : o+l≤SV P+48)
    (hs : (o+l≤SS ∨ SS+2048≤o) ∧ (o+l≤AH+1024*e ∨ AH+1024*(e+2)≤o)) :
    ∀r∈pairWrites L s₀ e,(R (kA s₀) L.sc o l).Disjoint r := by
  have hw := hp.wf
  intro r hr
  simp only [pairWrites,Paired.stepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact sdisj hp hf (by lom) hs.1
  · exact sdisj hp hf (by lom) (by rcases hs.2 with h|h <;> omega)
  · exact sdisj hp hf (by lom) (by rcases hs.2 with h|h <;> omega)

theorem pair_kb {s₀ s t : State} (hp : Pre P L s₀) {e : Nat} (he : e+1<P.k*P.k)
    (h : KB P L s₀ s) (hk : Keep Paired.pairRegs s t) (hf : Frame (pairWrites L s₀ e) s.mem t.mem) :
    KB P L s₀ t := by
  have hw := hp.wf
  refine h.frame hk hf (by decide) ?_
  intro r hr
  simp only [pairWrites,Paired.stepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl <;> exact safe_scr hp (by lom)

theorem pair_sub {s₀ : State} {e : Nat} (he : e+1<P.k*P.k) :
    ∀r∈pairWrites L s₀ e,∃r'∈bW P L s₀,Region.Sub r r' := by
  intro r hr
  simp only [pairWrites,Paired.stepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact ⟨_,by simp,fun _ h => h⟩
  · exact ⟨R (kA s₀) L.sc AH (1024*(P.k*P.k)),by simp,R.sub2 (by omega) (by omega)⟩
  · exact ⟨R (kA s₀) L.sc AH (1024*(P.k*P.k)),by simp,R.sub2 (by omega) (by omega)⟩

theorem last_far {s₀ : State} (hp : Pre P L s₀) {e : Nat} (he : e<P.k*P.k)
    {o l : Nat} (hf : o+l≤SV P+48)
    (hs : (o+l≤SS ∨ SS+2048≤o) ∧ (o+l≤AH+1024*e ∨ AH+1024*(e+1)≤o)) :
    ∀r∈lastWrites L s₀ e,(R (kA s₀) L.sc o l).Disjoint r := by
  have hw := hp.wf
  intro r hr
  simp only [lastWrites,Paired.fullWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact sdisj hp hf (by lom) hs.1
  · exact sdisj hp hf (by lom) (by rcases hs.2 with h|h <;> omega)

theorem last_kb {s₀ s t : State} (hp : Pre P L s₀) {e : Nat} (he : e<P.k*P.k)
    (h : KB P L s₀ s) (hk : Keep Paired.pairRegs s t) (hf : Frame (lastWrites L s₀ e) s.mem t.mem) :
    KB P L s₀ t := by
  have hw := hp.wf
  refine h.frame hk hf (by decide) ?_
  intro r hr
  simp only [lastWrites,Paired.fullWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl <;> exact safe_scr hp (by lom)

theorem last_sub {s₀ : State} {e : Nat} (he : e<P.k*P.k) :
    ∀r∈lastWrites L s₀ e,∃r'∈bW P L s₀,Region.Sub r r' := by
  intro r hr
  simp only [lastWrites,Paired.fullWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact ⟨_,by simp,fun _ h => h⟩
  · exact ⟨R (kA s₀) L.sc AH (1024*(P.k*P.k)),by simp,R.sub2 (by omega) (by omega)⟩

end VG.Proof.MlKem.AArch64.Kem
