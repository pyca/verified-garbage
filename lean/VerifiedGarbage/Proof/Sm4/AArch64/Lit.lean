import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Sm4.AArch64.Ecb
import VerifiedGarbage.Impl.Sm4.AArch64.ExpandKey
import VerifiedGarbage.Proof.Sm4.Planes

/-!
# SM4 on AArch64: the code as literals

The code of the key expansion and of ECB in both directions as literals
(`materialize_code`, `Proof/Framework/Lit.lean`), which the checks of the
whole functions (`taint_decide`, `lit_decide`) read rather than build the
code again.

The table of `CK`'s planes has a literal of its own, `ckEntries.lit`, which the
key expansion's reads: its `planeOf`s, which the kernel builds bit by bit,
are checked through `planeMasks` (`planeOf_eq_masks`) instead.
-/

namespace VG.Proof.Sm4.AArch64

materialize_value ckPlanes := (List.range 32).flatMap fun i => (List.range 8).map fun j =>
  (Impl.Sm4.AArch64.tableSlot + 8 * i + j, planeMasks (Spec.Sm4.ck i) j)

end VG.Proof.Sm4.AArch64

namespace VG.Impl.Sm4.AArch64

/-- `ckEntries` as a literal (`Proof.Sm4.AArch64.ckPlanes`). -/
noncomputable abbrev ckEntries.lit := VG.Proof.Sm4.AArch64.ckPlanes.lit

theorem ckEntries.lit_eq : ckEntries = ckEntries.lit := by
  rw [ckEntries.lit, ← VG.Proof.Sm4.AArch64.ckPlanes.lit_eq]
  simp only [ckEntries, VG.Proof.Sm4.planeOf_eq_masks]

end VG.Impl.Sm4.AArch64

namespace VG.Proof.Sm4.AArch64

materialize_code expandKeyCode := Impl.Sm4.AArch64.expandKey
materialize_code ecbEncrypt := Impl.Sm4.AArch64.ecb .encrypt
materialize_code ecbDecrypt := Impl.Sm4.AArch64.ecb .decrypt

end VG.Proof.Sm4.AArch64
