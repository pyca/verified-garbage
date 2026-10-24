module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Ntt16.Readonly
open VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.Ntt16
open VG.Impl.MlKem.AArch64.Ntt16.Readonly

theorem forward_length : (words 16 tableHalves).length = 64 := by lit_decide
theorem gamma_length : (words 32 gammaTable).length = 64 := by lit_decide

theorem forward_words : ∀ i < 64, (words 16 tableHalves).getD i 0 = hw4 tableHalves i := by lit_decide

theorem gamma_low : ∀ i < 64,
    ((words 32 gammaTable).getD i 0).extractLsb' 0 32 = BitVec.ofNat 32 (gammaTable.getD (2*i) 0) := by lit_decide

theorem gamma_high : ∀ i < 64,
    ((words 32 gammaTable).getD i 0).extractLsb' 32 32 = BitVec.ofNat 32 (gammaTable.getD (2*i+1) 0) := by lit_decide

end VG.Proof.MlKem.AArch64.Ntt16.Readonly
