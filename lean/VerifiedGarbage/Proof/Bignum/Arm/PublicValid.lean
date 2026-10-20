module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicPrepare
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Bignum.Arm.PublicApply
import VerifiedGarbage.Proof.Bignum.PublicWritten
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.PublicWritten

/-! # The public RSA path for a validated public key satisfies the shared result contract -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem publicValid_ok (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb : List Byte}
    (h : PublicValidInput base dst np ep xp len k eLen nb eb xb s)
    (exponent : Spec.Rsa.exponentValid (Spec.Rsa.os2ip eb) = true) :
    WP isa PublicFn.valid s fun t =>
      Spec.Rsa.written t.mem (State.addr dst) k (t.gpr .r0) (Spec.Rsa.publicOpChecked nb eb xb) ∧
      Frame [⟨State.addr base, 8 * len⟩, ⟨off (State.addr s.sp) 48, 4⟩, ⟨State.addr dst, k⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  rw [PublicFn.valid, WP.seq_iff]
  refine WP.mono (publicPrepare_ok s h) ?_
  rintro u ⟨prepared, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (publicPrecompute_ok u prepared) ?_
  rintro v ⟨arithmetic, frameV, restV⟩
  refine WP.mono (publicApply_ok v arithmetic) ?_
  rintro t ⟨bytes, status, frameT, restT⟩
  rw [restV.sp, restU.sp] at frameT
  exact ⟨publicOutput_written h.buffers.modulus.length h.valid exponent bytes status,
    (frameU.mono (by simp)).trans ((frameV.mono (by simp)).trans frameT), restU.trans (restV.trans restT)⟩

end VG.Proof.Bignum.Arm
