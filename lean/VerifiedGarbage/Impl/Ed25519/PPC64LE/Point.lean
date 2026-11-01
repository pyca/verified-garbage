module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.FieldMemory
public import VerifiedGarbage.Spec.Ed25519

/-!
# `vg_ed25519_r32_point_add` on PPC64LE, and doubling

`vg_ed25519_r32_point_add(ws)` (`Proof/Ed25519/Point32Contract.lean`; `ws` in `r3`)
moves `ws` to `r6` and runs the complete addition formula inline
(`pointAdd`). A double is the same call after the point is copied to the
second operand's slots (`doubleCall`), which computes `p + p` with the
same nine products as the addition formula specialized to equal inputs.
-/

@[expose] public section

namespace VG.Impl.Ed25519.PPC64LE

open VG.PPC64LE

/-- `vg_ed25519_r32_point_add`. -/
def addFn : Prog isa := .seq (.block [.addi .r6 .r3 0]) pointAdd

/-- A call of `vg_ed25519_r32_point_add`, the working space in `r6` before
and after (the callee keeps it in `r3`). -/
def addCall : Prog isa :=
  .seq (.block [.addi .r3 .r6 0])
    (.seq (.call "vg_ed25519_r32_point_add" addFn) (.block [.addi .r6 .r3 0]))

/-- The point in slots 0–3 doubled: copied to slots 4–7, and added. -/
def doubleCall : Prog isa := .seq copyPointToQ addCall

end VG.Impl.Ed25519.PPC64LE
