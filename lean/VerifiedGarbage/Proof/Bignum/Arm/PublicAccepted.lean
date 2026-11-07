module

import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst

/-! # Preserve the secret acceptance bit across workspace-only arithmetic -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem PublicStack.keep_acceptance {s t : State} {base dst np ep xp : BitVec 32} {len k eLen : Nat} {rs : List Reg}
    (h : PublicStack base dst np ep xp len k eLen s)
    (frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem) (rest : Rest rs s t) :
    t.mem.readW (off (State.addr t.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 := by
  have eq : WorkspaceEq (State.addr s.sp) 80 s.mem t.mem := WorkspaceEq.of_frame (by decide) frame
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.separate)
  rw [rest.sp]
  exact eq.word (d := 48) (bits := 32) (by decide)

end VG.Proof.Bignum.Arm
