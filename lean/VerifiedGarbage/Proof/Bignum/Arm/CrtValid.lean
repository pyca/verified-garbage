module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtCallStack
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState

import VerifiedGarbage.Proof.Bignum.Arm.CrtBegin
import VerifiedGarbage.Proof.Bignum.Arm.CrtComputeResult
import VerifiedGarbage.Proof.Framework.Block

/-! # The complete private RSA path for a valid public modulus -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem crt_valid_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (buffers : CrtBuffers g bs s) (stack : CrtCallStack g s)
    (ptr : s.gpr .r0 = g.base) (count : s.gpr .r6 = BitVec.ofNat 32 g.length)
    (saved : s.mem.readW (State.addr s.sp) 32 = g.base)
    (modulusPtr : s.mem.readW (off (State.addr s.sp) 8) 32 = g.modulus)
    (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (bs 0)) g.length = true) :
    WP isa CrtFn.valid s fun t =>
      Spec.Rsa.written t.mem (State.addr g.output) g.length (t.gpr .r0)
        (Spec.Rsa.privateCrt (bs 0) (bs 1) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6)) ∧
      Frame (crtMutable g s.sp ++ [⟨State.addr g.output, g.length⟩]) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [CrtFn.valid, WP.seq_iff]
  refine WP.mono (crt_begin_ok s buffers stack ptr count saved modulusPtr valid) ?_
  rintro u ⟨sharedU, readyU, frameU, restU⟩
  refine WP.mono (crt_validatedCompute_ok u sharedU readyU) ?_
  rintro t ⟨written, frameT, restT⟩
  rw [restU.sp] at frameT
  refine ⟨written, (frameU.mono (fun _ hr => List.mem_append_left _ hr)).trans (frameT.mono ?_), restU.trans restT⟩
  intro r hr
  simp only [crtLiveMutable, crtMutable, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with (rfl | rfl | rfl) | rfl <;> simp

end VG.Proof.Bignum.Arm
