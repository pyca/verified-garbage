module
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixCall
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbols

import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixTiming

/-! # Compositional timing endpoints for optimized public operations -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Impl.MlKem.AArch64

abbrev restSymbols : List String :=
 ["VG_MLKEM_GAMMA","VG_MLKEM_NTT16_ZETAS","VG_MLKEM_INTT16_ZETAS","VG_MLKEM16_NTT_ZETAS"]

theorem symbol_taint {c : Prog isa} {s u : State} (rs : List Reg)
    (sp : s.sp=u.sp) (regs : ∀r∈rs,s.gpr r=u.gpr r)
    (symbols : ∀name∈restSymbols,s.syms name=u.syms name)
    (hc : ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs rs) c h).isSome=true)
    {tr ur : List Leak} {t v : State} (et : Exec isa c s tr t) (eu : Exec isa c u ur v) : tr=ur := by
  exact (RelCT.taint (A:=VectorSymbols.analysis restSymbols) (VectorTaint.ofRegs rs)
    (P:=fun a b=>a=s ∧ b=u) (fun a b ⟨ha,hb⟩=>by
      subst a; subst b
      exact ⟨VectorTaint.agree_initial (agree_of sp regs),symbols⟩)
    hc.choose_spec _ _ _ _ _ _ ⟨rfl,rfl⟩ et eu).1

theorem kem_relCT {w16 : Bool} {P : KemLay} {L : Kem.Layout} {σ τ : State} {ρ : List Byte}
    {start rest : Prog isa} (hp : Kem.Pre P L σ) (hq : Kem.Pre P L τ)
    (ptr : ∀i<4,Kem.kA σ (L.slot i)=Kem.kA τ (L.slot i)) (sp : σ.sp=τ.sp)
    (shuffle : σ.syms "VG_MLKEM_REJ_SHUFFLE"=τ.syms "VG_MLKEM_REJ_SHUFFLE")
    (symbols : ∀name∈restSymbols,σ.syms name=τ.syms name)
    (as : WP isa start σ (fun s=>Kem.BInvW w16 P L σ s.mem ρ 0 s ∧ Kem.MatrixTable P L σ s))
    (au : WP isa start τ (fun s=>Kem.BInvW w16 P L τ s.mem ρ 0 s ∧ Kem.MatrixTable P L τ s))
    (ac : RelCT isa (fun s u=>s=σ ∧ u=τ) start (fun _ _=>True))
    (hc : ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28]) rest h).isSome=true) :
    RelCT isa (fun s u=>s=σ ∧ u=τ) (.seq start (.seq (Impl.MlKem.AArch64.Paired.matrix P false w16) rest))
      (fun _ _=>True) := by
  intro s u tr ur t v h et eu
  rcases h with ⟨hs,hu⟩; subst s; subst u
  obtain ⟨sA,ta,tb,rfl,ea,eb⟩ := Paired.seq_parts et
  obtain ⟨uA,ua,ub,rfl,fa,fb⟩ := Paired.seq_parts eu
  have aeq := (ac _ _ _ _ _ _ ⟨rfl,rfl⟩ ea fa).1
  have hs := Paired.exec_post as ea
  have hu := Paired.exec_post au fa
  obtain ⟨sB,tc,td,rfl,ec,ed⟩ := Paired.seq_parts eb
  obtain ⟨uB,uc,ud,rfl,fc,fd⟩ := Paired.seq_parts fb
  have bm := Kem.paired_matrix_relCT hp hq (ptr 3 (by decide)) sp _ _ _ _ _ _
    ⟨hs.1,hu.1,hs.2,hu.2,by rw [Exec.syms ea,Exec.syms fa]; exact shuffle⟩ ec fc
  have beq := bm.1
  have bs := bm.2.1
  have bu := bm.2.2.1
  have ceq := symbol_taint [.x25,.x26,.x27,.x28]
    (by rw [bs.kb.sp,bu.kb.sp,sp]) (fun r hr=>by
      rcases mem4 hr with rfl|rfl|rfl|rfl
      · rw [bs.kb.x25,bu.kb.x25,ptr 0 (by decide)]
      · rw [bs.kb.x26,bu.kb.x26,ptr 1 (by decide)]
      · rw [bs.kb.x27,bu.kb.x27,ptr 2 (by decide)]
      · rw [bs.kb.x28,bu.kb.x28,ptr 3 (by decide)])
    (fun name hn=>by rw [Exec.syms ec,Exec.syms fc,Exec.syms ea,Exec.syms fa]; exact symbols name hn) hc ed fd
  exact ⟨by rw [aeq,beq,ceq],trivial⟩

end VG.Proof.MlKem.AArch64.Optimized
