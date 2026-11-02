module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicArithmetic
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

theorem PublicAccepted.after_arrays {s t : State} {base dst np ep xp : BitVec 32} {len k eLen : Nat}
    {nb eb xb : List Byte} {rs : List Reg}
    (h : PublicAccepted base dst np ep xp len k eLen nb eb xb s)
    (ready : ArithmeticReady base len (Spec.Rsa.modulusWords k) t)
    (arrays : ∀ q < 8, numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) q =
      numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) q)
    (frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem) (rest : Rest rs s t) :
    PublicAccepted base dst np ep xp len k eLen nb eb xb t :=
  ⟨⟨⟨h.buffers.after_workspace frame rest, h.stack.after_workspace frame rest, ready,
      (arrays 0 (by decide)).trans h.modulus, h.modulusLength, h.odd, (arrays 4 (by decide)).trans h.r2⟩,
      (arrays 1 (by decide)).trans h.input⟩, (h.stack.keep_acceptance frame rest).trans h.flag⟩

theorem PublicAccepted.of_mem {s t : State} {base dst np ep xp : BitVec 32} {len k eLen : Nat}
    {nb eb xb : List Byte} {rs : List Reg}
    (h : PublicAccepted base dst np ep xp len k eLen nb eb xb s)
    (mem : t.mem = s.mem) (rest : Rest rs s t) (ptr : t.gpr .r0 = base) :
    PublicAccepted base dst np ep xp len k eLen nb eb xb t :=
  h.after_arrays (h.ready.of_mem mem rest ptr) (by intros; rw [mem])
    (by rw [mem]; exact Frame.refl _ _) rest

end VG.Proof.Bignum.Arm
