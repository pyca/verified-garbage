module

public import VerifiedGarbage.Impl.Ed25519.RISCV64.FieldMemory
public import VerifiedGarbage.Spec.Ed25519

/-!
# `vg_ed25519_r32_point_add` on RISC-V, and doubling

`vg_ed25519_r32_point_add(ws)` (`Proof/Ed25519/Point32Contract.lean`; `ws` in `a0`)
moves `ws` to `a3` and runs the complete addition formula inline
(`pointAdd`). A double is the same call after the point is copied to the
second operand's slots (`doubleCall`), which computes `p + p` with the
same nine products as the addition formula specialized to equal inputs.
-/

@[expose] public section

namespace VG.Impl.Ed25519.RISCV64

open VG.RISCV64

/-- `vg_ed25519_r32_point_add`. -/
def addFn : Prog isa := .seq (.block [.addi .a3 .a0 0]) pointAdd

/-- A call of `vg_ed25519_r32_point_add`, the working space in `a3` before
and after (the callee keeps it in `a0`). -/
def addCall : Prog isa :=
  .seq (.block [.addi .a0 .a3 0])
    (.seq (.call "vg_ed25519_r32_point_add" addFn) (.block [.addi .a3 .a0 0]))

/-- The point in slots 0–3 doubled: copied to slots 4–7, and added. -/
def doubleCall : Prog isa := .seq copyPointToQ addCall

end VG.Impl.Ed25519.RISCV64
