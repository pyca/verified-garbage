module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Native controller accesses include both halves of the packed attempt counter. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Ffdh.Arm.KeySearch (Controller)

theorem controllerAddr {base : BitVec 32} {s : State} (h : Controller base s)
    (d : Nat) (bound : d + 4 ≤ 128) :
    State.addr (s.gpr .r4 + BitVec.ofNat 32 d) = off (State.addr base) d := by
  rw [h.ptr]
  exact VG.Arm.addr_add (by have := h.space.nowrap; omega)

end VG.Proof.Ffdh.Arm.ParameterSearch
