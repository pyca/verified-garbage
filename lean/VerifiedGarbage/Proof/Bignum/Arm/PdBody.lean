module

public import VerifiedGarbage.Proof.Bignum.Arm.PdImported
public import VerifiedGarbage.Proof.Bignum.Arm.PublicArgs
public import VerifiedGarbage.Proof.Bignum.Arm.ExponentCheck
public import VerifiedGarbage.Proof.Bignum.Arm.ExponentFlag
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Complete ARMv7 checked public RSA body, including invalid-key failures -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem pdBody_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen N R : Nat} {eb xb : List Byte}
    (h : PdBodyInput base dst np ep xp len k eLen N R eb xb s) :
    WP isa PdFn.body s fun t =>
      (if Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb) then PdOutput dst k N R eb xb t
       else t.gpr .r0 = 0 ∧ Spec.Rsa.bytesAt t.mem (State.addr dst) k = List.replicate k 0) ∧
      Frame [⟨State.addr base, 8 * len⟩, ⟨off (State.addr s.sp) 48, 4⟩, ⟨State.addr dst, k⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  rw [PdFn.body, WP.seq_iff]
  refine WP.mono (publicExponentArgs_ok s h.stack) ?_
  rintro u ⟨pointer, count, memU, restU⟩
  have hu := h.of_mem memU restU ((restU.gpr .r0 (by simp)).trans h.ptr)
  have length := hu.buffers.exponent.length
  rw [WP.seq_iff]
  refine WP.mono (exponentCheck_ok u
    (by rw [length]; exact hu.buffers.exponentPositive)
    (by rw [length]; have := hu.buffers.exponentFits; have := hu.buffers.maxLength; omega)
    (by rw [length]; exact hu.buffers.exponent.fits)
    (by rw [length]; exact hu.buffers.exponent.read) hu.buffers.exponent.byte pointer
    (by rw [length]; exact count)) ?_
  rintro v ⟨status, memV, restV⟩
  have hv := hu.of_mem memV restV ((restV.gpr .r0 (by simp [exponentClobbers])).trans hu.ptr)
  rw [WP.seq_iff]
  refine WP.mono (exponentFlag_ok v status) ?_
  rintro z ⟨zero, memZ, restZ⟩
  have hz := hv.of_mem memZ restZ ((restZ.gpr .r0 (by simp)).trans hv.ptr)
  have rest : Rest roundClobbers s z := (restU.mono (by simp [roundClobbers])).trans
    ((restV.mono (by simp [roundClobbers, exponentClobbers])).trans (restZ.mono (by simp [roundClobbers])))
  have mem : z.mem = s.mem := memZ.trans (memV.trans memU)
  refine WP.ite (!Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb)) (by change some z.z = _; rw [zero]) ?_ ?_
  · intro invalid
    have invalidE : Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb) = false := by simpa using invalid
    refine WP.mono (pdFail_ok z hz) ?_
    rintro t ⟨status, bytes, frame, restT⟩
    simp only [invalidE, Bool.false_eq_true, ite_false]
    rw [mem] at frame
    exact ⟨⟨status, bytes⟩, frame.mono (by simp), rest.trans restT⟩
  · intro valid
    have validE : Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb) = true := by simpa using valid
    refine WP.mono (pdImported_ok z hz) ?_
    rintro t ⟨result, frame, restT⟩
    rw [mem, rest.sp] at frame
    simp only [validE, ite_true]
    exact ⟨result, frame, rest.trans restT⟩

end VG.Proof.Bignum.Arm
