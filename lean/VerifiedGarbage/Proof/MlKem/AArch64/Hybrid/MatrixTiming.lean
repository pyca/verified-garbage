module

import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.PairTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Matrix
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-!
# A hashing pair leaks only public pointers and `ρ`

`hashPair_relCT`, as `Kem.paired_matrix_relCT`'s pairs, relating two runs from
states that agree on the pointers and `ρ`, with each run's invariant (`HRel`),
by `pairMCode_relCT`. The two runs' messages may differ; only their pointer
is public.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Paired (exec_post)
open VG.Spec.MlKem

variable {P : KemLay} {L : Layout}

/-- Both runs after `e` entries and `j` hashing pairs. -/
def HRel (w16 : Bool) (P : KemLay) (L : Layout) (M : Msg) (σ τ : State) (m n : Mem) (ρ Eσ Eτ : List Byte)
    (e j : Nat) (s u : State) : Prop :=
  HInvW w16 P L M σ m ρ Eσ e j s ∧ HInvW w16 P L M τ n ρ Eτ e j u ∧
  MT3 P L σ s ∧ MT3 P L τ u ∧ s.syms "VG_MLKEM_REJ_SHUFFLE" = u.syms "VG_MLKEM_REJ_SHUFFLE"

/-- What both runs agree on. -/
structure Same (L : Layout) (M : Msg) (σ τ : State) : Prop where
  base : kA σ L.sc = kA τ L.sc
  ek : (M.reg σ).base = (M.reg τ).base
  sp : σ.sp = τ.sp

theorem hashPair_relCT {w16 : Bool} {M : Msg} {σ τ : State} (hp : Pre P L σ) (hq : Pre P L τ)
    (hk : Stk128 P L σ) (hk' : Stk128 P L τ) (hM : MsgOk P L M σ) (hM' : MsgOk P L M τ) (sm : Same L M σ τ)
    {m n : Mem} {ρ Eσ Eτ : List Byte} {i : Nat}
    (he : 2*i+1<P.k*P.k) (hb : 136 * (3 * i + 2) < M.S.len)
    (habs : ∀ blk, 136 * blk < M.S.len → ∃ h, (taint.check (Taint.ofRegs [M.S.r, .x28])
      (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock M.S blk)) h).isSome = true) :
    RelCT isa (HRel w16 P L M σ τ m n ρ Eσ Eτ (2*i) i) (Impl.MlKem.AArch64.Hybrid.pair3 P M.S (2*i) i w16)
      (HRel w16 P L M σ τ m n ρ Eσ Eτ (2*i+2) (i+1)) := by
  intro s u tr ur t v h et eu
  have hw := hp.wf
  have hf := hw.facts
  have hkk : P.k * P.k ≤ 16 := hf.2.2.1
  have hoa : AH+1024*(2*i)<65536 := by simp only [KEM.AH]; omega_using [he, hkk]
  have hob : AH+1024*(2*i+1)<65536 := by simp only [KEM.AH]; omega_using [he, hkk]
  have ps := pair_input hp he h.1.b.kb h.2.2.1.t
  have pu := pair_input hq he h.2.1.b.kb h.2.2.2.1.t
  have hs := hash_input hp hk hM he h.1.b.kb h.2.2.1
  have hu := hash_input hq hk' hM' he h.2.1.b.kb h.2.2.2.1
  have ba : ∀o,sA L σ o=sA L τ o := fun o=>congrArg (fun b=>b+BitVec.ofNat 64 o) sm.base
  have aa : ∀i,aP L σ i=aP L τ i := fun i=>ba _
  rw [←ba SS,←ba SB,←aa (2*i),←aa (2*i+1),←h.2.2.2.2] at pu
  rw [←ba SS,←aa (2*i),←aa (2*i+1),←h.2.2.2.2,←sm.ek,←sm.base] at hu
  have seeds : ∀j,Paired.seedState s.mem (sA L σ SB) j P.k=Paired.seedState u.mem (sA L σ SB) j P.k := by
    intro j
    rw [Paired.seedState_eq _ _ (by lom) (by lom),Paired.seedState_eq _ _ (by lom) (by lom)]
    unfold Paired.seedBytes
    rw [h.1.b.rho,ba SB,h.2.1.b.rho]
  have hash₂ := h.2.1.hash
  rw [← sm.base] at hash₂
  have ek₂ := h.2.1.ek
  rw [← sm.ek] at ek₂
  have ct := pairMCode_relCT (w16 := w16) (j := 3*i) (m := 3) P M.S hM.src (by decide) (by decide) (by decide)
    hoa hob ps hs pu hu (fun k hk _ => by omega) h.1.hash h.1.ek hash₂ ek₂
    (by rw [h.1.b.kb.sp, h.2.1.b.kb.sp, sm.sp]) (seeds (2*i)) (seeds (2*i+1)) habs
  have ht := exec_post (paired_step3 hp hk hM he hb h.1 h.2.2.1) et
  have hv := exec_post (paired_step3 hq hk' hM' he hb h.2.1 h.2.2.2.1) eu
  exact ⟨(ct _ _ _ _ _ _ ⟨rfl,rfl⟩ (pairM_exec et) (pairM_exec eu)).1,ht.1,hv.1,ht.2,hv.2,
    by rw [Exec.syms et,Exec.syms eu]; exact h.2.2.2.2⟩

end VG.Proof.MlKem.AArch64.Hybrid
