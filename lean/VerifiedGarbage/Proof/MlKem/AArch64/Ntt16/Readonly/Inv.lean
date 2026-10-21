module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Pre
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Inv

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Ntt16.Readonly
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Ntt16

theorem inv_ok (s₀ : State) (hi : Input s₀ "VG_MLKEM_INTT16_ZETAS" invTableHalves) :
    WP isa Impl.MlKem.AArch64.Ntt16.Readonly.inv s₀ fun s' =>
      s'.sp=s₀.sp ∧ PolyIs s'.mem (fP s₀) (Spec.MlKem.nttInv (P₀ s₀)) := by
  exact NttR.inv_run s₀ ⟨hi.wr, hi.disj, hi.red, hi.table, hi.readable, hi.apartOutput, hi.apartScratch⟩

end VG.Proof.MlKem.AArch64.Ntt16.Readonly
