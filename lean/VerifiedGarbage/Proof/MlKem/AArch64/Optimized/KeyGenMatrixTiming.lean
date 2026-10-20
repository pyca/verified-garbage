module
public import VerifiedGarbage.Proof.MlKem.AArch64.KgB
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixTable
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullPrefix
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Last
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.BeginTiming

import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixLast
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixPair
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! # Public-seed timing of the optimized encryption matrix -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Spec.MlKem
open VG.Proof.MlKem
variable {P : KemLay}

theorem pair_input {s₀ s : State} (hp : Pre P s₀) {e : Nat} (he : e+1<P.k*P.k)
    (h : KB P s₀ s) (tb : MatrixTable P s₀ s) :
    Paired.BeginInput SB SS (AH+1024*e) (AH+1024*(e+1))
      ((kA s₀ 3+BitVec.ofNat 64 SS)) ((kA s₀ 3+BitVec.ofNat 64 SB)) ((kA s₀ 3+BitVec.ofNat 64 (AH+1024*e))) ((kA s₀ 3+BitVec.ofNat 64 (AH+1024*(e+1))))
      (s.syms "VG_MLKEM_REJ_SHUFFLE") s := by
  have hw := hp.wf
  refine ⟨(by rw [h.x28]),(by rw [h.x28]),(by rw [h.x28]),(by rw [h.x28]),?_,
    hp.args.rdisj (b₁:=3) (b₂:=3) (o₁:=SB) (l₁:=32) (o₂:=SS) (l₂:=2048) (by decide) (by decide) (by kl) (by kl) (by decide),pair_context hp he h tb,rfl⟩
  intro j hj
  rw [ptr_add]
  exact in_R (cov_r hp h (b:=3) (o:=SB) (l:=32) (by decide) (by kl)) (k:=8*j) (by omega) (by omega)

theorem last_input {s₀ s : State} (hp : Pre P s₀) {e : Nat} (he : e<P.k*P.k)
    (h : KB P s₀ s) (tb : MatrixTable P s₀ s) :
    Paired.LastInput SB SS (AH+1024*e) ((kA s₀ 3+BitVec.ofNat 64 SS)) ((kA s₀ 3+BitVec.ofNat 64 SB)) ((kA s₀ 3+BitVec.ofNat 64 (AH+1024*e)))
      (s.syms "VG_MLKEM_REJ_SHUFFLE") s := by
  have hw := hp.wf
  refine ⟨(by rw [h.x28]),(by rw [h.x28]),(by rw [h.x28]),?_,
    hp.args.rdisj (b₁:=3) (b₂:=3) (o₁:=SB) (l₁:=32) (o₂:=SS) (l₂:=2048) (by decide) (by decide) (by kl) (by kl) (by decide),singleton_context hp he h tb,rfl⟩
  intro j hj
  rw [ptr_add]
  exact in_R (cov_r hp h (b:=3) (o:=SB) (l:=32) (by decide) (by kl)) (k:=8*j) (by omega) (by omega)

def MatrixRel (w16 : Bool) (P : KemLay) (σ τ : State) (e : Nat)
    (s u : State) : Prop :=
  BInvW w16 P σ e s ∧ BInvW w16 P τ e u ∧
  MatrixTable P σ s ∧ MatrixTable P τ u ∧
  s.syms "VG_MLKEM_REJ_SHUFFLE"=u.syms "VG_MLKEM_REJ_SHUFFLE"

theorem pair_matrix_relCT {w16 : Bool} {σ τ : State} (hp : Pre P σ) (hq : Pre P τ)
    (base : kA σ 3=kA τ 3) (sp : σ.sp=τ.sp) (rho : rhoK P σ=rhoK P τ) {e : Nat}
    (he : e+1<P.k*P.k) :
    RelCT isa (MatrixRel w16 P σ τ e) (Impl.MlKem.AArch64.Paired.pair P true e w16)
      (MatrixRel w16 P σ τ (e+2)) := by
  intro s u tr ur t v h et eu
  have hw := hp.wf
  have ps := pair_input hp he h.1.kb h.2.2.1
  have pu := pair_input hq he h.2.1.kb h.2.2.2.1
  have ba : ∀o,(kA σ 3+BitVec.ofNat 64 o)=(kA τ 3+BitVec.ofNat 64 o) := fun o=>congrArg (fun b=>b+BitVec.ofNat 64 o) base
  have aa : ∀i,(kA σ 3+BitVec.ofNat 64 (AH+1024*i))=(kA τ 3+BitVec.ofNat 64 (AH+1024*i)) := fun i=>ba _
  rw [←ba SS,←ba SB,←aa e,←aa (e+1),←h.2.2.2.2] at pu
  have seeds : ∀i,Paired.seedState s.mem ((kA σ 3+BitVec.ofNat 64 SB)) i P.k=Paired.seedState u.mem ((kA σ 3+BitVec.ofNat 64 SB)) i P.k := by
    intro i
    rw [Paired.seedState_eq _ _ (by lom) (by lom),Paired.seedState_eq _ _ (by lom) (by lom)]
    unfold Paired.seedBytes
    rw [h.1.rho,ba SB,h.2.1.rho,rho]
  have ct := Paired.pair_relCT (w16:=w16) (L:=P) (kg:=true) (a:=e) (by decide) (by decide) (by decide)
    (by change AH+1024*e<65536; lom) (by change AH+1024*(e+1)<65536; lom) ps pu
    (by rw [h.1.kb.sp,h.2.1.kb.sp,sp]) (by rw [h.1.kb.x28,h.2.1.kb.x28,base]) (seeds e) (seeds (e+1))
  have ht := Paired.exec_post (matrix_pair hp he h.1 h.2.2.1) et
  have hv := Paired.exec_post (matrix_pair hq he h.2.1 h.2.2.2.1) eu
  exact ⟨(ct _ _ _ _ _ _ ⟨rfl,rfl⟩ et eu).1,ht.1,hv.1,ht.2,hv.2,
    by rw [Exec.syms et,Exec.syms eu]; exact h.2.2.2.2⟩


theorem last_matrix_relCT {w16 : Bool} {σ τ : State} (hp : Pre P σ) (hq : Pre P τ)
    (base : kA σ 3=kA τ 3) (sp : σ.sp=τ.sp) (rho : rhoK P σ=rhoK P τ) {e : Nat}
    (he : e<P.k*P.k) :
    RelCT isa (MatrixRel w16 P σ τ e) (Paired.lastCode SB SS e P.k (AH+1024*e) w16)
      (MatrixRel w16 P σ τ (e+1)) := by
  intro s u tr ur t v h et eu
  have hw := hp.wf
  have ps := last_input hp he h.1.kb h.2.2.1
  have pu := last_input hq he h.2.1.kb h.2.2.2.1
  have ba : ∀o,(kA σ 3+BitVec.ofNat 64 o)=(kA τ 3+BitVec.ofNat 64 o) := fun o=>congrArg (fun b=>b+BitVec.ofNat 64 o) base
  have aa : ∀i,(kA σ 3+BitVec.ofNat 64 (AH+1024*i))=(kA τ 3+BitVec.ofNat 64 (AH+1024*i)) := fun i=>ba _
  rw [←ba SS,←ba SB,←aa e,←h.2.2.2.2] at pu
  have seed : Paired.seedBytes s.mem ((kA σ 3+BitVec.ofNat 64 SB)) e P.k=Paired.seedBytes u.mem ((kA σ 3+BitVec.ofNat 64 SB)) e P.k := by
    unfold Paired.seedBytes
    rw [h.1.rho,ba SB,h.2.1.rho,rho]
  have ct := Paired.lastCode_relCT (w16 := w16) (by decide) (by decide) (by decide) (by lom) (by lom) (by lom)
    ps pu (hp.args.rdisj (b₁:=3) (b₂:=3) (o₁:=SB) (l₁:=32) (o₂:=AH+1024*e) (l₂:=1024) (by decide) (by decide) (by kl) (matrixEntry_fit hw he) (by lom))
    (by rw [h.1.kb.sp,h.2.1.kb.sp,sp]) (by rw [h.1.kb.x28,h.2.1.kb.x28,base]) seed
  have ht := Paired.exec_post (matrix_singleton hp he h.1 h.2.2.1) et
  have hv := Paired.exec_post (matrix_singleton hq he h.2.1 h.2.2.2.1) eu
  exact ⟨(ct _ _ _ _ _ _ ⟨rfl,rfl⟩ et eu).1,ht.1,hv.1,ht.2,hv.2,
    by rw [Exec.syms et,Exec.syms eu]; exact h.2.2.2.2⟩


theorem paired_matrix_relCT {w16 : Bool} {σ τ : State} (hp : Pre P σ) (hq : Pre P τ)
    (base : kA σ 3=kA τ 3) (sp : σ.sp=τ.sp) (rho : rhoK P σ=rhoK P τ) :
    RelCT isa (MatrixRel w16 P σ τ 0) (Impl.MlKem.AArch64.Paired.matrix P true w16)
      (MatrixRel w16 P σ τ (P.k*P.k)) := by
  have hk : 0<P.k := hp.wf.facts.1
  have hn : 0<P.k*P.k := Nat.mul_pos hk hk
  apply RelCTs.seqs
  · intro hh
    have parts := List.append_eq_nil_iff.mp hh
    by_cases ho : P.k*P.k%2=1
    · simpa only [ite_eq_left ho,List.cons_ne_nil] using parts.2
    · have np : 0<P.k*P.k/2 := by omega
      exact map_range_ne_nil np _ parts.1
  · refine RelCTs.append (RelCTs.range (I:=fun i=>MatrixRel w16 P σ τ (2*i))
      (fun i hi=>?_)) ?_
    · simpa only [Nat.mul_add,Nat.mul_one] using
        pair_matrix_relCT hp hq base sp rho (by omega : 2*i+1<P.k*P.k)
    · by_cases ho : P.k*P.k%2=1
      · rw [ite_eq_left ho]
        have idx : 2*(P.k*P.k/2)=P.k*P.k-1 := by omega
        rw [idx]
        refine ⟨MatrixRel w16 P σ τ (P.k*P.k-1+1),?_,?_⟩
        · rw [Paired.lastSample_eq]
          exact last_matrix_relCT hp hq base sp rho (by omega : P.k*P.k-1<P.k*P.k)
        · intro s u h
          simpa only [Nat.sub_add_cancel hn] using h
      · rw [ite_eq_right ho]
        have idx : 2*(P.k*P.k/2)=P.k*P.k := by omega
        intro s u h
        simpa only [idx] using h

end VG.Proof.MlKem.AArch64.KeyGen
