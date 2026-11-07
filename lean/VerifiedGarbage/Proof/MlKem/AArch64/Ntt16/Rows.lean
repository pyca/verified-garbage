module

public import VerifiedGarbage.Proof.MlKem.NttLayer
import VerifiedGarbage.Proof.MlKem.AArch64.Barrett
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint

/-!
# ML-KEM's 16-bit NTT on AArch64: its zetas

The zetas of the 16-bit NTT's table are those of the standard
(`ofNat_zeta`), each less than `q` (`zeta_lt`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open Impl.MlKem.AArch64.Ntt16

/-! ## Zetas -/

theorem ofNat_zeta {k : Nat} (hk : k < 128) : ofNat (Impl.MlKem.AArch64.Ntt16.zeta k) = VG.Proof.MlKem.zeta k := by
  rw [VG.Proof.MlKem.zeta_eq hk, Impl.MlKem.AArch64.Ntt16.zeta, zetaTable_eq]

theorem zeta_lt {k : Nat} (hk : k < 128) : Impl.MlKem.AArch64.Ntt16.zeta k < 3329 := by
  have := zetaTable_lt k hk
  exact this

end VG.Proof.MlKem.AArch64.Ntt16
