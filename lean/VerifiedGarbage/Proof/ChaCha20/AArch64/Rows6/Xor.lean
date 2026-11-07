module
public import VerifiedGarbage.Impl.ChaCha20.AArch64.Rows6
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor

import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Save
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Lit
import VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.ChaCha20.AArch64.Rows6
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Save
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Lit
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Spec.ChaCha20
public import VerifiedGarbage.TCB.Artifact

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Rows6
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6
open VG.Proof.ChaCha20 (xorAArch64)
open VG.Proof.ChaCha20.AArch64.Xor (st dp L bp stR dR bR)
open VG.Spec.ChaCha20 (stateAt bytesAt)

/-- The six other callee-saved vectors are never destinations. -/
def keepsOtherV (i : Instr) : Bool :=
  match vdstOf i with
  | some .v10 | some .v11 | some .v12 | some .v13 | some .v14 | some .v15 => false
  | _ => true

theorem keepsOtherV_ne {i : Instr} (hi : keepsOtherV i = true) {r : VReg}
    (hr : r ∈ preservedV) (h8 : r ≠ .v8) (h9 : r ≠ .v9) : vdstOf i ≠ some r := by
  intro he
  unfold keepsOtherV at hi
  rw [he] at hi
  cases r <;> simp_all [preservedV]

end VG.Proof.ChaCha20.AArch64.Rows6
