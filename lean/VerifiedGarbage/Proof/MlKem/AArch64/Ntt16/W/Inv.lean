module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Fwd
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Inv

/-!
# ML-KEM's 16-bit inverse NTT on AArch64, of a polynomial stored with 16 bits

`Impl.MlKem.AArch64.Ntt16.Readonly.invW` computes the inverse of the
polynomial at `x0`, stored with 16-bit coefficients, in place, with 512
bytes of working space at `x1` and the table `VG_MLKEM_INTT16_ZETAS`
(`invW_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16.W

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Ntt16

theorem invW_ok (s₀ : State) (hi : Input s₀ "VG_MLKEM_INTT16_ZETAS" invTableHalves) :
    WP isa Impl.MlKem.AArch64.Ntt16.Readonly.invW s₀ fun s' =>
      s'.sp = s₀.sp ∧ PolyIsW 16 s'.mem (fP s₀) (Spec.MlKem.nttInv (P₀ s₀)) := by
  exact NttR.invW_run s₀ ⟨hi.wr, hi.disj, hi.red, hi.table, hi.readable, hi.apartOutput, hi.apartScratch⟩

end VG.Proof.MlKem.AArch64.Ntt16.W
