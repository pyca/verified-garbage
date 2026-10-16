module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtFail
public import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Complete private RSA body including public modulus rejection -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem crt_body_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtBodyInput g bs s) :
    WP isa CrtFn.body s fun t =>
      Spec.Rsa.written t.mem (State.addr g.output) g.length (t.gpr .r0)
        (Spec.Rsa.privateCrt (bs 0) (bs 1) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6)) ∧
      Frame (crtMutable g s.sp ++ [⟨State.addr g.output, g.length⟩]) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [CrtFn.body, WP.seq_iff]
  refine WP.mono (modulusCheck_ok s h.buffers.lengthValid.1 h.buffers.lengthValid.2
    (h.buffers.source 0).fits (h.buffers.source 0).read h.source h.count) ?_
  rintro u ⟨flag, mem, rest⟩
  have nb : Spec.Rsa.bytesAt s.mem (State.addr g.modulus) g.length = bs 0 := (h.buffers.source 0).bytes
  change u.z = Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr g.modulus) g.length)) g.length at flag
  rw [nb] at flag
  have hu := h.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ptr)
    ((rest.gpr .r4 (by simp)).trans h.source) ((rest.gpr .r6 (by simp)).trans h.count)
  refine WP.ite (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (bs 0)) g.length) (by change some u.z = _; rw [flag]) ?_ ?_
  · intro valid
    refine WP.mono (crt_valid_ok u hu.buffers hu.stack hu.ptr hu.count hu.saved hu.modulusPtr valid) ?_
    rintro t ⟨written, frame, restT⟩
    rw [mem, rest.sp] at frame
    exact ⟨written, frame, (rest.mono (by simp [roundClobbers])).trans restT⟩
  · intro invalid
    refine WP.mono (crt_fail_ok u hu) ?_
    rintro t ⟨status, bytes, frame, restT⟩
    have failed : Spec.Rsa.privateCrt (bs 0) (bs 1) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6) = none := by
      have nLength : (bs 0).length = g.length := (h.buffers.source 0).length
      simp only [Spec.Rsa.privateCrt, nLength, invalid, Bool.false_eq_true, ite_false]
    rw [failed]
    rw [mem] at frame
    exact ⟨⟨status, bytes⟩, frame.mono (by simp), (rest.mono (by simp [roundClobbers])).trans restT⟩

end VG.Proof.Bignum.Arm
