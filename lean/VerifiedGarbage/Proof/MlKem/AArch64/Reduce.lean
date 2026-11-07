module

public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.MlKem.Arith

/-!
# ML-KEM on AArch64: reductions modulo `q`

The conditional subtraction `csub` (`Impl/MlKem/AArch64/Basic.lean`), for any
registers.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.MlKem (q)
open VG.Proof.MlKem (condSub q_eq)

theorem not_mem_one {a b : Reg} (h : a ≠ b) : a ∉ [b] := by simpa using h

end VG.Proof.MlKem.AArch64
