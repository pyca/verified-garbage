module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Pre
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.FwdU

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Ntt16.Readonly
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Ntt16

theorem fwd_ok (s₀ : State) (hi : Input s₀ "VG_MLKEM_NTT16_ZETAS" tableHalves) :
    WP isa Impl.MlKem.AArch64.Ntt16.Readonly.fwd s₀ fun s' =>
      s'.sp=s₀.sp ∧ PolyIs s'.mem (fP s₀) (Spec.MlKem.ntt (P₀ s₀)) := by
  exact NttR.fwd_run s₀ ⟨hi.wr, hi.disj, hi.red, hi.table, hi.readable, hi.apartOutput, hi.apartScratch⟩

end VG.Proof.MlKem.AArch64.Ntt16.Readonly
