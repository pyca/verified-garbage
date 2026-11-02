module

public import VerifiedGarbage.Proof.Bignum.Arm.PdArithmetic
import VerifiedGarbage.Proof.Bignum.Arm.PublicAccepted
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst

/-! # Preserve the secret acceptance bit across workspace-only arithmetic -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem PdAccepted.after_arrays {s t : State} {base dst np ep xp : BitVec 32} {len k eLen N R : Nat}
    {eb xb : List Byte} {rs : List Reg}
    (h : PdAccepted base dst np ep xp len k eLen N R eb xb s)
    (ready : ArithmeticReady base len (Spec.Rsa.modulusWords k) t)
    (arrays : ∀ q < 8, numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) q =
      numAt s.mem (State.addr base) (Spec.Rsa.modulusWords k) q)
    (frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem) (rest : Rest rs s t) :
    PdAccepted base dst np ep xp len k eLen N R eb xb t :=
  ⟨⟨⟨h.buffers.after_workspace frame rest, h.stack.after_workspace frame rest, ready,
      (arrays 0 (by decide)).trans h.modulus, h.odd, (arrays 4 (by decide)).trans h.r2, h.r2bound⟩,
      (arrays 1 (by decide)).trans h.input⟩, (h.stack.keep_acceptance frame rest).trans h.flag⟩

theorem PdAccepted.of_mem {s t : State} {base dst np ep xp : BitVec 32} {len k eLen N R : Nat}
    {eb xb : List Byte} {rs : List Reg}
    (h : PdAccepted base dst np ep xp len k eLen N R eb xb s)
    (mem : t.mem = s.mem) (rest : Rest rs s t) (ptr : t.gpr .r0 = base) :
    PdAccepted base dst np ep xp len k eLen N R eb xb t :=
  h.after_arrays (h.ready.of_mem mem rest ptr) (by intros; rw [mem])
    (by rw [mem]; exact Frame.refl _ _) rest

end VG.Proof.Bignum.Arm
