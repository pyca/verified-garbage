module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ed25519.Point32Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Ed25519.RISCV64.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldProg
public import VerifiedGarbage.Impl.Ed25519.RISCV64.FieldMemory
public import VerifiedGarbage.Spec.Ed25519

/-!
# Ed25519 on RISC-V: a working space aligned to 8 bytes

`Ctx8`: the working space of 8192 bytes aligned to 8, as calls of the field
and point functions take it, which code that keeps `Keep` keeps; the slots
that a point addition keeps (`Kept`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64

/-- The point addition's working space: `ws` in `a3`, a multiple of 8, its 8192 bytes writable. -/
structure Ctx8 (b : Addr) (s : State) : Prop where
  a3 : s.gpr .a3 = b
  al : b.toNat % 8 = 0
  wr : (⟨b, 8192⟩ : Region) ∈ s.wr

theorem Ctx8.ctx {b : Addr} {s : State} (h : Ctx8 b s) : Ctx b s :=
  ⟨h.a3, h.al, fun d n hd => in_base h.wr (by omega) (by omega)⟩

theorem Ctx8.ws {b : Addr} {s : State} (h : Ctx8 b s) : WS b s :=
  Covers.of_sub fun r hr => ⟨_, h.wr, 0, by rw [List.mem_singleton.mp hr]; simp, by
    rw [List.mem_singleton.mp hr]; simp⟩

theorem Ctx8.of_keep {b : Addr} {s t : State} (h : Ctx8 b s) (k : Keep b s t) : Ctx8 b t :=
  ⟨by rw [k.rest.gpr _ (by decide), h.a3], h.al, by rw [k.rest.wr]; exact h.wr⟩

/-- The slots the point addition keeps: all but the sum's and the temporaries'. -/
def Kept (i : Slot) : Prop := 4 ≤ i.val ∧ i.val < 8 ∨ 16 ≤ i.val

instance (i : Slot) : Decidable (Kept i) := by unfold Kept; infer_instance

end VG.Proof.Ed25519.RISCV64
