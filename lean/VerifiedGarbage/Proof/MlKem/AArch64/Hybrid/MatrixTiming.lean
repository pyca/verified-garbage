module

public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.PairTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Matrix

/-!
# The hashing matrix leaks only public pointers and `ρ`

As `Kem.paired_matrix_relCT`, relating two runs from states that agree on
the pointers and `ρ`, with each run's invariant (`HInv`): a hashing pair by
`pair3Code_relCT`, the others by `Paired.pair_relCT` and
`Paired.lastCode_relCT`. The two runs' `ek` may differ; only its pointer is
public.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Encaps (enL ekE)
open VG.Proof.MlKem.AArch64.Paired (exec_post)
open VG.Spec.MlKem

variable {P : KemLay}

/-- Both runs after `e` entries and `j` hashing pairs. -/
def HRel (w16 : Bool) (P : KemLay) (σ τ : State) (m n : Mem) (ρ : List Byte) (e j : Nat) (s u : State) : Prop :=
  HInvW w16 P σ m ρ (ekE P σ) e j s ∧ HInvW w16 P τ n ρ (ekE P τ) e j u ∧
  MT3 P σ s ∧ MT3 P τ u ∧ s.syms "VG_MLKEM_REJ_SHUFFLE" = u.syms "VG_MLKEM_REJ_SHUFFLE"

/-- What both runs agree on. -/
structure Same (P : KemLay) (σ τ : State) : Prop where
  base : kA σ (enL P).sc = kA τ (enL P).sc
  ek : kA σ 0 = kA τ 0
  sp : σ.sp = τ.sp

theorem hashPair_relCT {w16 : Bool} {σ τ : State} (hp : Pre P (enL P) σ) (hq : Pre P (enL P) τ)
    (hk : Stk128 P σ) (hk' : Stk128 P τ) (sm : Same P σ τ) {m n : Mem} {ρ : List Byte} {i : Nat}
    (he : 2*i+1<P.k*P.k) (hb : 136 * (3 * i + 2) < P.ekLen) (h8 : P.ekLen % 8 = 0) (hlim : P.ekLen ≤ 4096)
    (habs : ∀ blk, 136 * blk < P.ekLen → ∃ h, (taint.check (Taint.ofRegs [.x25, .x28])
      (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock P blk)) h).isSome = true) :
    RelCT isa (HRel w16 P σ τ m n ρ (2*i) i) (Impl.MlKem.AArch64.Hybrid.pair3 P (2*i) i w16)
      (HRel w16 P σ τ m n ρ (2*i+2) (i+1)) := by
  intro s u tr ur t v h et eu
  have hw := hp.wf
  have hf := hw.facts
  have hkk : P.k * P.k ≤ 16 := hf.2.2.1
  have hoa : AH+1024*(2*i)<65536 := by simp only [KEM.AH]; omega_using [he, hkk]
  have hob : AH+1024*(2*i+1)<65536 := by simp only [KEM.AH]; omega_using [he, hkk]
  have ps := pair_input hp he h.1.b.kb h.2.2.1.t
  have pu := pair_input hq he h.2.1.b.kb h.2.2.2.1.t
  have hs := hash_input hp hk he h.1.b.kb h.2.2.1
  have hu := hash_input hq hk' he h.2.1.b.kb h.2.2.2.1
  have ba : ∀o,sA (enL P) σ o=sA (enL P) τ o := fun o=>congrArg (fun b=>b+BitVec.ofNat 64 o) sm.base
  have aa : ∀i,aP (enL P) σ i=aP (enL P) τ i := fun i=>ba _
  rw [←ba SS,←ba SB,←aa (2*i),←aa (2*i+1),←h.2.2.2.2] at pu
  rw [←ba SS,←aa (2*i),←aa (2*i+1),←h.2.2.2.2,←sm.ek,←sm.base] at hu
  have seeds : ∀j,Paired.seedState s.mem (sA (enL P) σ SB) j P.k=Paired.seedState u.mem (sA (enL P) σ SB) j P.k := by
    intro j
    rw [Paired.seedState_eq _ _ (by lom) (by lom),Paired.seedState_eq _ _ (by lom) (by lom)]
    unfold Paired.seedBytes
    rw [h.1.b.rho,ba SB,h.2.1.b.rho]
  have hash₂ := h.2.1.hash
  rw [← sm.base] at hash₂
  have ek₂ := ek_kb h.2.1.b.kb
  rw [← sm.ek] at ek₂
  have ct := pair3Code_relCT (w16 := w16) P hoa hob ps hs pu hu hb h8 hlim h.1.hash (ek_kb h.1.b.kb) hash₂ ek₂
    (by rw [h.1.b.kb.sp, h.2.1.b.kb.sp, sm.sp]) (seeds (2*i)) (seeds (2*i+1)) habs
  have ht := exec_post (paired_step3 hp hk he hb h8 hlim h.1 h.2.2.1) et
  have hv := exec_post (paired_step3 hq hk' he hb h8 hlim h.2.1 h.2.2.2.1) eu
  exact ⟨(ct _ _ _ _ _ _ ⟨rfl,rfl⟩ (pair3_exec et) (pair3_exec eu)).1,ht.1,hv.1,ht.2,hv.2,
    by rw [Exec.syms et,Exec.syms eu]; exact h.2.2.2.2⟩

theorem plainPair_relCT {w16 : Bool} {σ τ : State} (hp : Pre P (enL P) σ) (hq : Pre P (enL P) τ)
    (sm : Same P σ τ) {m n : Mem} {ρ : List Byte} {e j : Nat} (he : e+1<P.k*P.k) :
    RelCT isa (HRel w16 P σ τ m n ρ e j) (Impl.MlKem.AArch64.Paired.pair P false e w16)
      (HRel w16 P σ τ m n ρ (e+2) j) := by
  intro s u tr ur t v h et eu
  have hw := hp.wf
  have ps := pair_input hp he h.1.b.kb h.2.2.1.t
  have pu := pair_input hq he h.2.1.b.kb h.2.2.2.1.t
  have ba : ∀o,sA (enL P) σ o=sA (enL P) τ o := fun o=>congrArg (fun b=>b+BitVec.ofNat 64 o) sm.base
  have aa : ∀i,aP (enL P) σ i=aP (enL P) τ i := fun i=>ba _
  rw [←ba SS,←ba SB,←aa e,←aa (e+1),←h.2.2.2.2] at pu
  have seeds : ∀i,Paired.seedState s.mem (sA (enL P) σ SB) i P.k=Paired.seedState u.mem (sA (enL P) σ SB) i P.k := by
    intro i
    rw [Paired.seedState_eq _ _ (by lom) (by lom),Paired.seedState_eq _ _ (by lom) (by lom)]
    unfold Paired.seedBytes
    rw [h.1.b.rho,ba SB,h.2.1.b.rho]
  have ct := Paired.pair_relCT (w16:=w16) (L:=P) (kg:=false) (a:=e) (by decide) (by decide) (by decide)
    (by change AH+1024*e<65536; lom) (by change AH+1024*(e+1)<65536; lom) ps pu
    (by rw [h.1.b.kb.sp,h.2.1.b.kb.sp,sm.sp]) (by rw [h.1.b.kb.x28,h.2.1.b.kb.x28,sm.base]) (seeds e) (seeds (e+1))
  have ht := exec_post (paired_stepH hp he h.1 h.2.2.1) et
  have hv := exec_post (paired_stepH hq he h.2.1 h.2.2.2.1) eu
  exact ⟨(ct _ _ _ _ _ _ ⟨rfl,rfl⟩ et eu).1,ht.1,hv.1,ht.2,hv.2,
    by rw [Exec.syms et,Exec.syms eu]; exact h.2.2.2.2⟩

theorem lastH_relCT {w16 : Bool} {σ τ : State} (hp : Pre P (enL P) σ) (hq : Pre P (enL P) τ)
    (sm : Same P σ τ) {m n : Mem} {ρ : List Byte} {e j : Nat} (he : e<P.k*P.k) :
    RelCT isa (HRel w16 P σ τ m n ρ e j) (Paired.lastCode SB SS e P.k (AH+1024*e) w16)
      (HRel w16 P σ τ m n ρ (e+1) j) := by
  intro s u tr ur t v h et eu
  have hw := hp.wf
  have ps := last_input hp he h.1.b.kb h.2.2.1.t
  have pu := last_input hq he h.2.1.b.kb h.2.2.2.1.t
  have ba : ∀o,sA (enL P) σ o=sA (enL P) τ o := fun o=>congrArg (fun b=>b+BitVec.ofNat 64 o) sm.base
  have aa : ∀i,aP (enL P) σ i=aP (enL P) τ i := fun i=>ba _
  rw [←ba SS,←ba SB,←aa e,←h.2.2.2.2] at pu
  have seed : Paired.seedBytes s.mem (sA (enL P) σ SB) e P.k=Paired.seedBytes u.mem (sA (enL P) σ SB) e P.k := by
    unfold Paired.seedBytes
    rw [h.1.b.rho,ba SB,h.2.1.b.rho]
  have ct := Paired.lastCode_relCT (w16 := w16) (by decide) (by decide) (by decide) (by lom) (by lom) (by lom)
    ps pu (sdisj hp (by lom) (by lom) (by lom))
    (by rw [h.1.b.kb.sp,h.2.1.b.kb.sp,sm.sp]) (by rw [h.1.b.kb.x28,h.2.1.b.kb.x28,sm.base]) seed
  have ht := exec_post (singleton_stepH hp he h.1 h.2.2.1) et
  have hv := exec_post (singleton_stepH hq he h.2.1 h.2.2.2.1) eu
  exact ⟨(ct _ _ _ _ _ _ ⟨rfl,rfl⟩ et eu).1,ht.1,hv.1,ht.2,hv.2,
    by rw [Exec.syms et,Exec.syms eu]; exact h.2.2.2.2⟩

/-- **The hashing matrix** leaks only public pointers and `ρ`. -/
theorem matrixH_relCT {w16 : Bool} {σ τ : State} (hp : Pre P (enL P) σ) (hq : Pre P (enL P) τ)
    (hk : Stk128 P σ) (hk' : Stk128 P τ) (sm : Same P σ τ) (ho : HashOk P) {m n : Mem} {ρ : List Byte}
    (habs : ∀ blk, 136 * blk < P.ekLen → ∃ h, (taint.check (Taint.ofRegs [.x25, .x28])
      (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock P blk)) h).isSome = true) :
    RelCT isa (HRel w16 P σ τ m n ρ 0 0) (Impl.MlKem.AArch64.Hybrid.matrixH P w16)
      (HRel w16 P σ τ m n ρ (P.k*P.k) (Impl.MlKem.AArch64.Hybrid.hashPairs P)) := by
  have hk1 : 0<P.k := hp.wf.facts.1
  have hn : 0<P.k*P.k := Nat.mul_pos hk1 hk1
  have hP := ho.pairs
  apply RelCTs.seqs
  · intro hh
    have parts := List.append_eq_nil_iff.mp hh
    by_cases ho' : P.k*P.k%2=1
    · simpa only [ite_eq_left ho',List.cons_ne_nil] using parts.2
    · have np : 0<P.k*P.k/2 := by omega
      exact map_range_ne_nil np _ parts.1
  · refine RelCTs.append (RelCTs.range (I:=fun i=>HRel w16 P σ τ m n ρ (2*i)
      (min i (Impl.MlKem.AArch64.Hybrid.hashPairs P))) (fun i hi=>?_)) ?_
    · by_cases hh : i < Impl.MlKem.AArch64.Hybrid.hashPairs P
      · rw [ite_eq_left hh, show min i (Impl.MlKem.AArch64.Hybrid.hashPairs P) = i by omega,
          show min (i+1) (Impl.MlKem.AArch64.Hybrid.hashPairs P) = i+1 by omega,
          show 2*(i+1) = 2*i+2 by omega]
        have hb : 136 * (3 * i + 2) < P.ekLen := by
          have := ho.part; have := ho.three
          simp only [Impl.MlKem.AArch64.Hybrid.hashPairs, Impl.MlKem.AArch64.Hybrid.blocks] at hh
          omega
        exact hashPair_relCT hp hq hk hk' sm (by omega) hb ho.h8 ho.lim habs
      · rw [ite_eq_right hh,
          show min i (Impl.MlKem.AArch64.Hybrid.hashPairs P) = Impl.MlKem.AArch64.Hybrid.hashPairs P by omega,
          show min (i+1) (Impl.MlKem.AArch64.Hybrid.hashPairs P) = Impl.MlKem.AArch64.Hybrid.hashPairs P by omega,
          show 2*(i+1) = 2*i+2 by omega]
        exact plainPair_relCT hp hq sm (by omega)
    · rw [show min (P.k*P.k/2) (Impl.MlKem.AArch64.Hybrid.hashPairs P) = Impl.MlKem.AArch64.Hybrid.hashPairs P by omega]
      by_cases ho' : P.k*P.k%2=1
      · rw [ite_eq_left ho']
        have idx : 2*(P.k*P.k/2)=P.k*P.k-1 := by omega
        rw [idx]
        refine ⟨HRel w16 P σ τ m n ρ (P.k*P.k-1+1) (Impl.MlKem.AArch64.Hybrid.hashPairs P),?_,?_⟩
        · rw [Paired.lastSample_eq]
          exact lastH_relCT hp hq sm (by omega : P.k*P.k-1<P.k*P.k)
        · intro s u h
          simpa only [Nat.sub_add_cancel hn] using h
      · rw [ite_eq_right ho']
        have idx : 2*(P.k*P.k/2)=P.k*P.k := by omega
        intro s u h
        simpa only [idx] using h

end VG.Proof.MlKem.AArch64.Hybrid
