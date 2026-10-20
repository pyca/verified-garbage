module

public import VerifiedGarbage.Proof.MlKem.AArch64.Width
public import VerifiedGarbage.Impl.MlKem1024.AArch64.Compress
import VerifiedGarbage.Proof.MlKem.Compress1024

/-! # ML-KEM-1024 on AArch64: the widths of the vector codecs -/

@[expose] public section

namespace VG.Proof.MlKem1024.AArch64

open VG.Impl.MlKem1024.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64

theorem width5_ok : WOk width5 := ⟨compress1024_eq (d := 5) (by decide), by decide, by decide, rfl, rfl, rfl,
  by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem width11_ok : WOk width11 := ⟨compress1024_eq (d := 11) (by decide), by decide, by decide, rfl, rfl,
  rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

end VG.Proof.MlKem1024.AArch64
