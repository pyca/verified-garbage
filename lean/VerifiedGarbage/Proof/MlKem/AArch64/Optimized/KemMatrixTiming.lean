module
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixCall
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullPrefix
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.BeginTiming

import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! # Public-seed timing of the optimized encryption matrix -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Spec.MlKem
open VG.Proof.MlKem
variable {P : KemLay} {L : Layout}

theorem pair_input {s₀ s : State} (hp : Pre P L s₀) {e : Nat} (he : e+1<P.k*P.k)
    (h : KB P L s₀ s) (tb : MatrixTable P L s₀ s) :
    Paired.BeginInput SB SS (AH+1024*e) (AH+1024*(e+1))
      (sA L s₀ SS) (sA L s₀ SB) (aP L s₀ e) (aP L s₀ (e+1))
      (s.syms "VG_MLKEM_REJ_SHUFFLE") s := by
  have hw := hp.wf
  refine ⟨e28 h SS,e28 h SB,e28 h _,e28 h _,?_,
    sdisj hp (by lom) (by lom) (by decide),pair_context hp he h tb,rfl⟩
  intro j hj
  rw [ptr_add]
  exact in_R (cov_sr hp h (o:=SB) (l:=32) (by lom)) (k:=8*j) (by omega) (by omega)

theorem last_input {s₀ s : State} (hp : Pre P L s₀) {e : Nat} (he : e<P.k*P.k)
    (h : KB P L s₀ s) (tb : MatrixTable P L s₀ s) :
    Paired.LastInput SB SS (AH+1024*e) (sA L s₀ SS) (sA L s₀ SB) (aP L s₀ e)
      (s.syms "VG_MLKEM_REJ_SHUFFLE") s := by
  have hw := hp.wf
  refine ⟨e28 h SS,e28 h SB,e28 h _,?_,
    sdisj hp (by lom) (by lom) (by decide),singleton_context hp he h tb,rfl⟩
  intro j hj
  rw [ptr_add]
  exact in_R (cov_sr hp h (o:=SB) (l:=32) (by lom)) (k:=8*j) (by omega) (by omega)

def MatrixRel (w16 : Bool) (P : KemLay) (L : Layout) (σ τ : State) (m n : Mem) (ρ : List Byte) (e : Nat)
    (s u : State) : Prop :=
  BInvW w16 P L σ m ρ e s ∧ BInvW w16 P L τ n ρ e u ∧
  MatrixTable P L σ s ∧ MatrixTable P L τ u ∧
  s.syms "VG_MLKEM_REJ_SHUFFLE"=u.syms "VG_MLKEM_REJ_SHUFFLE"

theorem pair_matrix_relCT {w16 : Bool} {σ τ : State} (hp : Pre P L σ) (hq : Pre P L τ)
    (base : kA σ L.sc=kA τ L.sc) (sp : σ.sp=τ.sp) {m n : Mem} {ρ : List Byte} {e : Nat}
    (he : e+1<P.k*P.k) :
    RelCT isa (MatrixRel w16 P L σ τ m n ρ e) (Impl.MlKem.AArch64.Paired.pair P false e w16)
      (MatrixRel w16 P L σ τ m n ρ (e+2)) := by
  intro s u tr ur t v h et eu
  have hw := hp.wf
  have ps := pair_input hp he h.1.kb h.2.2.1
  have pu := pair_input hq he h.2.1.kb h.2.2.2.1
  have ba : ∀o,sA L σ o=sA L τ o := fun o=>congrArg (fun b=>b+BitVec.ofNat 64 o) base
  have aa : ∀i,aP L σ i=aP L τ i := fun i=>ba _
  rw [←ba SS,←ba SB,←aa e,←aa (e+1),←h.2.2.2.2] at pu
  have seeds : ∀i,Paired.seedState s.mem (sA L σ SB) i P.k=Paired.seedState u.mem (sA L σ SB) i P.k := by
    intro i
    rw [Paired.seedState_eq _ _ (by lom) (by lom),Paired.seedState_eq _ _ (by lom) (by lom)]
    unfold Paired.seedBytes
    rw [h.1.rho,ba SB,h.2.1.rho]
  have ct := Paired.pair_relCT (w16:=w16) (L:=P) (kg:=false) (a:=e) (by decide) (by decide) (by decide)
    (by change AH+1024*e<65536; lom) (by change AH+1024*(e+1)<65536; lom) ps pu
    (by rw [h.1.kb.sp,h.2.1.kb.sp,sp]) (by rw [h.1.kb.x28,h.2.1.kb.x28,base]) (seeds e) (seeds (e+1))
  have ht := Paired.exec_post (paired_step hp he h.1 h.2.2.1) et
  have hv := Paired.exec_post (paired_step hq he h.2.1 h.2.2.2.1) eu
  exact ⟨(ct _ _ _ _ _ _ ⟨rfl,rfl⟩ et eu).1,ht.1,hv.1,ht.2,hv.2,
    by rw [Exec.syms et,Exec.syms eu]; exact h.2.2.2.2⟩


theorem last_matrix_relCT {w16 : Bool} {σ τ : State} (hp : Pre P L σ) (hq : Pre P L τ)
    (base : kA σ L.sc=kA τ L.sc) (sp : σ.sp=τ.sp) {m n : Mem} {ρ : List Byte} {e : Nat}
    (he : e<P.k*P.k) :
    RelCT isa (MatrixRel w16 P L σ τ m n ρ e) (Paired.lastCode SB SS e P.k (AH+1024*e) w16)
      (MatrixRel w16 P L σ τ m n ρ (e+1)) := by
  intro s u tr ur t v h et eu
  have hw := hp.wf
  have ps := last_input hp he h.1.kb h.2.2.1
  have pu := last_input hq he h.2.1.kb h.2.2.2.1
  have ba : ∀o,sA L σ o=sA L τ o := fun o=>congrArg (fun b=>b+BitVec.ofNat 64 o) base
  have aa : ∀i,aP L σ i=aP L τ i := fun i=>ba _
  rw [←ba SS,←ba SB,←aa e,←h.2.2.2.2] at pu
  have seed : Paired.seedBytes s.mem (sA L σ SB) e P.k=Paired.seedBytes u.mem (sA L σ SB) e P.k := by
    unfold Paired.seedBytes
    rw [h.1.rho,ba SB,h.2.1.rho]
  have ct := Paired.lastCode_relCT (w16 := w16) (by decide) (by decide) (by decide) (by lom) (by lom) (by lom)
    ps pu (sdisj hp (by lom) (by lom) (by lom))
    (by rw [h.1.kb.sp,h.2.1.kb.sp,sp]) (by rw [h.1.kb.x28,h.2.1.kb.x28,base]) seed
  have ht := Paired.exec_post (singleton_step hp he h.1 h.2.2.1) et
  have hv := Paired.exec_post (singleton_step hq he h.2.1 h.2.2.2.1) eu
  exact ⟨(ct _ _ _ _ _ _ ⟨rfl,rfl⟩ et eu).1,ht.1,hv.1,ht.2,hv.2,
    by rw [Exec.syms et,Exec.syms eu]; exact h.2.2.2.2⟩


theorem paired_matrix_relCT {w16 : Bool} {σ τ : State} (hp : Pre P L σ) (hq : Pre P L τ)
    (base : kA σ L.sc=kA τ L.sc) (sp : σ.sp=τ.sp) {m n : Mem} {ρ : List Byte} :
    RelCT isa (MatrixRel w16 P L σ τ m n ρ 0) (Impl.MlKem.AArch64.Paired.matrix P false w16)
      (MatrixRel w16 P L σ τ m n ρ (P.k*P.k)) := by
  have hk : 0<P.k := hp.wf.facts.1
  have hn : 0<P.k*P.k := Nat.mul_pos hk hk
  apply RelCTs.seqs
  · intro hh
    have parts := List.append_eq_nil_iff.mp hh
    by_cases ho : P.k*P.k%2=1
    · simpa only [ite_eq_left ho,List.cons_ne_nil] using parts.2
    · have np : 0<P.k*P.k/2 := by omega
      exact map_range_ne_nil np _ parts.1
  · refine RelCTs.append (RelCTs.range (I:=fun i=>MatrixRel w16 P L σ τ m n ρ (2*i))
      (fun i hi=>?_)) ?_
    · simpa only [Nat.mul_add,Nat.mul_one] using
        pair_matrix_relCT hp hq base sp (m:=m) (n:=n) (ρ:=ρ) (by omega : 2*i+1<P.k*P.k)
    · by_cases ho : P.k*P.k%2=1
      · rw [ite_eq_left ho]
        have idx : 2*(P.k*P.k/2)=P.k*P.k-1 := by omega
        rw [idx]
        refine ⟨MatrixRel w16 P L σ τ m n ρ (P.k*P.k-1+1),?_,?_⟩
        · rw [Paired.lastSample_eq]
          exact last_matrix_relCT hp hq base sp (by omega : P.k*P.k-1<P.k*P.k)
        · intro s u h
          simpa only [Nat.sub_add_cancel hn] using h
      · rw [ite_eq_right ho]
        have idx : 2*(P.k*P.k/2)=P.k*P.k := by omega
        intro s u h
        simpa only [idx] using h

end VG.Proof.MlKem.AArch64.Kem
