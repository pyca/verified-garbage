module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Initialization changes only bytes in the caller's scratch buffer -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt

theorem crt_regions_frame {s : State} {base : BitVec 32} {size w : Nat} {m m' : Mem}
    (ws : Workspace s base size) (fit : totalBytes w ≤ size)
    (frame : Frame (crtRegions base (workspaceWords w) w) m m') :
    Frame [⟨State.addr base, size⟩] m m' := by
  have cover : Covers (crtRegions base (workspaceWords w) w) [⟨State.addr base, size⟩] := by
    have fake : Workspace (s.withRegions s.rd [⟨State.addr base, size⟩]) base size :=
      ⟨ws.nowrap, by simp [State.withRegions]⟩
    exact crt_regions_covered fake fit
  intro x hx
  apply frame x
  intro r hr inside
  obtain ⟨r', member, inside'⟩ := cover x 1 ⟨r, hr, inside⟩
  exact hx r' member inside'

end VG.Proof.Bignum.Arm
