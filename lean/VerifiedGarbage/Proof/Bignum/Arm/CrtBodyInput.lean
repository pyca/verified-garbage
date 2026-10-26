module
import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Bignum.Arm.CrtCallStack
public import VerifiedGarbage.Proof.Bignum.Words


/-! # Private RSA body state before validating the public modulus -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure CrtBodyInput (g : CrtGeometry) (bs : Fin 7 → List Byte) (s : State) : Prop where
  buffers : CrtBuffers g bs s
  stack : CrtCallStack g s
  ptr : s.gpr .r0 = g.base
  source : s.gpr .r4 = g.modulus
  count : s.gpr .r6 = BitVec.ofNat 32 g.length
  saved : s.mem.readW (State.addr s.sp) 32 = g.base
  modulusPtr : s.mem.readW (off (State.addr s.sp) 8) 32 = g.modulus

theorem CrtBodyInput.of_mem {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {rs : List Reg}
    (h : CrtBodyInput g bs s) (mem : t.mem = s.mem) (rest : Rest rs s t)
    (ptr : t.gpr .r0 = g.base) (source : t.gpr .r4 = g.modulus) (count : t.gpr .r6 = BitVec.ofNat 32 g.length) :
    CrtBodyInput g bs t := by
  have frame : Frame [] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact ⟨h.buffers.after_frame frame rest (by simp), h.stack.after_frame (frame.mono (by simp)) rest,
    ptr, source, count, by rw [mem, rest.sp]; exact h.saved, by rw [mem, rest.sp]; exact h.modulusPtr⟩

end VG.Proof.Bignum.Arm
