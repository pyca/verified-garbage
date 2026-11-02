module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtCallStack
public import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceState
import VerifiedGarbage.Proof.Framework.Offset

/-! # Shared state retained across private CRT validation and arithmetic -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure CrtShared (g : CrtGeometry) (bs : Fin 7 → List Byte) (s : State) : Prop where
  buffers : CrtBuffers g bs s
  stack : CrtCallStack g s
  main : CrtMainState g.base (workspaceWords g.words) g.words s.mem
  p : CrtLayoutState (crtP g.base g.words) (workspaceWords g.words) g.words s.mem
  q : CrtLayoutState (crtQ g.base g.words) (workspaceWords g.words) g.words s.mem
  modulus : numAt s.mem (State.addr g.base) g.words 0 = Spec.Rsa.os2ip (bs 0)
  valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (bs 0)) g.length = true
  savedMain : s.mem.readW (off (State.addr s.sp) 8) 32 = g.base

theorem CrtBuffers.after_mutable {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {rs : List Reg}
    (h : CrtBuffers g bs s) (frame : Frame (crtMutable g s.sp) s.mem t.mem) (rest : Rest rs s t) :
    CrtBuffers g bs t := by
  apply h.after_frame frame rest
  intro i r hr
  simp only [crtMutable, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.sourceSeparate i
  · exact (h.sourceStack i).sub_right (Region.sub_prefix (by decide))
  · exact (h.sourceStack i).sub_right (Offset.sub_base _ (by decide))
  · exact (h.sourceStack i).sub_right (Offset.sub_base _ (by decide))

end VG.Proof.Bignum.Arm
