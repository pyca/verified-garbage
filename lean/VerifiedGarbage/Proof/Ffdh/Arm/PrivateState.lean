module

public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Ffdh.Arm.SubgroupCT
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack

/-! Shared arithmetic and input-buffer invariants of native private-key validation. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)

structure PrivateReady (p : Inputs) (slots : List Nat) (yb xb : List Byte) (s : State) : Prop where
  context : Context p slots s
  ready : ArithmeticReady p.base p.len p.w s
  modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P
  r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P
  value : Octets p.base p.publicValue p.len yb s
  scalar : Octets p.base p.privateValue p.len xb s

theorem PrivateReady.after_mem {p : Inputs} {slots : List Nat} {yb xb : List Byte} {s t : State} {rs : List Reg}
    (h : PrivateReady p slots yb xb s) (mem : t.mem = s.mem) (rest : VG.Proof.X25519.Arm.Rest rs s t)
    (ptr : t.gpr .r0 = p.base) : PrivateReady p slots yb xb t := by
  have frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact ⟨h.context.of_mem mem rest ptr, h.ready.of_mem mem rest ptr, by rw [mem]; exact h.modulus,
    by rw [mem]; exact h.r2, h.value.after_workspace frame rest, h.scalar.after_workspace frame rest⟩

theorem PrivateReady.after_workspace {p : Inputs} {slots : List Nat} {yb xb : List Byte} {s t : State} {rs : List Reg}
    (h : PrivateReady p slots yb xb s) (stable : stableSlots slots = true)
    (frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem) (rest : VG.Proof.X25519.Arm.Rest rs s t)
    (ready : ArithmeticReady p.base p.len p.w t) (modulus : numAt t.mem (State.addr p.base) p.w 0 = p.P)
    (r2 : numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P) : PrivateReady p slots yb xb t :=
  ⟨h.context.after_workspace frame rest ready.ptr (fun d hd => (stableSlots_at (d := d) stable hd).1),
    ready, modulus, r2, h.value.after_workspace frame rest, h.scalar.after_workspace frame rest⟩

end VG.Proof.Ffdh.Arm
