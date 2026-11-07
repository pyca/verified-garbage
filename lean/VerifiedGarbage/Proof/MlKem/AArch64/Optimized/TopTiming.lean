module
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixCall
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbols

import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KemMatrixTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-! # Compositional timing endpoints for optimized public operations -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Impl.MlKem.AArch64

abbrev restSymbols : List String :=
 ["VG_MLKEM_GAMMA","VG_MLKEM_NTT16_ZETAS","VG_MLKEM16_INTT_ZETAS","VG_MLKEM16_NTT_ZETAS"]

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

end VG.Proof.MlKem.AArch64.Optimized
