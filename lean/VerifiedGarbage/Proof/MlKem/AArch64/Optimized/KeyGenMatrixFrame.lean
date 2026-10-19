module
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullSample
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Context
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Restore
public import VerifiedGarbage.Proof.MlKem.AArch64.KgCommon


/-! # Memory and caller invariants for two matrix entries at a time -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Spec.MlKem
variable {P : KemLay}

def pairWrites (s₀ : State) (e : Nat) : List Region :=
  Paired.stepWrites (kA s₀ 3+BitVec.ofNat 64 SS)
    (kA s₀ 3+BitVec.ofNat 64 (AH+1024*e))
    (kA s₀ 3+BitVec.ofNat 64 (AH+1024*(e+1)))

theorem pair_far {s₀ : State} (hp : Pre P s₀) {e : Nat} (he : e+1<P.k*P.k)
    {b o l : Nat} (hb : b<4) (hf : o+l≤kL P b)
    (hs : b≠3 ∨ ((o+l≤SS ∨ SS+2048≤o) ∧
      (o+l≤AH+1024*e ∨ AH+1024*(e+2)≤o))) :
    ∀r∈pairWrites s₀ e,(R (kA s₀) b o l).Disjoint r := by
  have hw := hp.wf
  intro r hr
  simp only [pairWrites,Paired.stepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact hp.args.rdisj hb (by decide) hf (by kl) (by rcases hs with hs|hs <;> omega)
  · exact hp.args.rdisj hb (by decide) hf (by simp only [kL]; lom)
      (by rcases hs with hs|hs <;> omega)
  · exact hp.args.rdisj hb (by decide) hf (by simp only [kL]; lom)
      (by rcases hs with hs|hs <;> omega)

theorem pair_kb {s₀ s t : State} (hp : Pre P s₀) {e : Nat} (he : e+1<P.k*P.k)
    (h : KB P s₀ s) (hk : Keep Paired.pairRegs s t) (hf : Frame (pairWrites s₀ e) s.mem t.mem) :
    KB P s₀ t := by
  have hw := hp.wf
  have h1 := pair_far hp he (b:=3) (o:=SV P) (l:=48) (by decide) hp.sv (.inr (by lom))
  have h2 := pair_far hp he (b:=0) (o:=0) (l:=64) (by decide) (by kl) (.inl (by decide))
  exact h.frame hk hf (by decide) fun r hr=>⟨h1 r hr,h2 r hr⟩

def lastWrites (s₀ : State) (e : Nat) : List Region :=
  Paired.fullWrites (kA s₀ 3+BitVec.ofNat 64 SS)
    (kA s₀ 3+BitVec.ofNat 64 (AH+1024*e))

theorem last_far {s₀ : State} (hp : Pre P s₀) {e : Nat} (he : e<P.k*P.k)
    {b o l : Nat} (hb : b<4) (hf : o+l≤kL P b)
    (hs : b≠3 ∨ ((o+l≤SS ∨ SS+2048≤o) ∧
      (o+l≤AH+1024*e ∨ AH+1024*(e+1)≤o))) :
    ∀r∈lastWrites s₀ e,(R (kA s₀) b o l).Disjoint r := by
  have hw := hp.wf
  intro r hr
  simp only [lastWrites,Paired.fullWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact hp.args.rdisj hb (by decide) hf (by kl) (by rcases hs with hs|hs <;> omega)
  · exact hp.args.rdisj hb (by decide) hf (by simp only [kL]; lom)
      (by rcases hs with hs|hs <;> omega)

theorem last_kb {s₀ s t : State} (hp : Pre P s₀) {e : Nat} (he : e<P.k*P.k)
    (h : KB P s₀ s) (hk : Keep Paired.pairRegs s t) (hf : Frame (lastWrites s₀ e) s.mem t.mem) :
    KB P s₀ t := by
  have hw := hp.wf
  have h1 := last_far hp he (b:=3) (o:=SV P) (l:=48) (by decide) hp.sv (.inr (by lom))
  have h2 := last_far hp he (b:=0) (o:=0) (l:=64) (by decide) (by kl) (.inl (by decide))
  exact h.frame hk hf (by decide) fun r hr=>⟨h1 r hr,h2 r hr⟩

end VG.Proof.MlKem.AArch64.KeyGen
