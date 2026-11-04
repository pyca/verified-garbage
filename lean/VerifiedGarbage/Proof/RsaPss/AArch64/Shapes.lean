module

public import VerifiedGarbage.Proof.RsaPss.AArch64.Checks
public import VerifiedGarbage.Proof.RsaPss.AArch64.TabCall
public import VerifiedGarbage.Impl.RsaPss.AArch64.Encoding
import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.RsaPss.AArch64.Checks
meta import VerifiedGarbage.Proof.RsaPss.AArch64.TabCall
meta import VerifiedGarbage.Impl.RsaPss.AArch64.Encoding
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# RSASSA-PSS on AArch64: the facts of each hash function's shape

`encode` and `checkEncoding` are emitted once for each index of `idxs`, with
the streaming code's parameters and the digest length `shapeOf` gives it
(`ofIdx`): the taint check of their piece that depends on these
(`pss_shape`), and what their calls of the digest need of it (`dig_shape`),
for each, as on x86-64 (`Proof/RsaPss/X86_64/Shapes.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.AArch64 (Params)

/-- The checks, for the shape of each index. -/
theorem pss_shape : ∀ i ∈ idxs, PssChecks (shapeOf i).1 (shapeOf i).2 := by
  intro i hi
  simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨⟨_, by taint_decide⟩⟩

/-! ## The digest -/

/-- What the calls of the digest need of it, for the parameters `P`. -/
theorem dig_of (P : Params) (hv : (Impl.MdHashTable.AArch64.digest P).allInstrs keepsV = true)
    (hct : ∃ hc, (taint.check (VG.AArch64.Taint.ofRegs [.x0, .x1]) (Impl.MdHashTable.AArch64.digest P) hc).isSome =
      true) : DigOK P :=
  ⟨hv, fun _ => VG.Taint.constantTime_of_exists (A := taint) (VG.AArch64.Taint.ofRegs [.x0, .x1])
    (fun _ _ _ _ hp => ⟨hp.2.2, fun r hr => by
      simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.1
      · exact hp.2.1⟩) hct⟩

theorem dig_md5 : DigOK (shapeOf 0).1 := dig_of _ (by decide) ⟨_, by taint_decide⟩
theorem dig_sha1 : DigOK (shapeOf 1).1 := dig_of _ (by decide) ⟨_, by taint_decide⟩
theorem dig_sha256 : DigOK (shapeOf 3).1 := dig_of _ (by decide) ⟨_, by taint_decide⟩
theorem dig_sha512 : DigOK (shapeOf 5).1 := dig_of _ (by decide) ⟨_, by taint_decide⟩

/-- What the calls of the digest need of it, for the shape of each index. -/
theorem dig_shape : ∀ i ∈ idxs, DigOK (shapeOf i).1 := by
  intro i hi
  simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact dig_md5
  · exact dig_sha1
  · exact dig_sha256
  · exact dig_sha256
  · exact dig_sha512
  · exact dig_sha512
  · exact dig_sha512
  · exact dig_sha512

end VG.Proof.RsaPss.AArch64
