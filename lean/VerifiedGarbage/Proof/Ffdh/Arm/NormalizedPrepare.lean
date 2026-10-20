module

public import VerifiedGarbage.Impl.Ffdh.Arm.NormalizedPrepare
public import VerifiedGarbage.Proof.Ffdh.Arm.Prepare
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
import VerifiedGarbage.Proof.Bignum.Arm.NormalizedPrecompute
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.Block

/-! # FFDH preparation for a modulus with a nonzero highest word -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Spec.Rsa.Mont (numAt)

theorem normalizedPrepare_ok (s : State) {base src : BitVec 32} {len k : Nat}
    {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len (Spec.Rsa.modulusWords k) P regions)
    (h : PrepareInput base src len k s) (hp : P s)
    (normalized : 2 ^ (64 * (Spec.Rsa.modulusWords k - 1)) ≤
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) :
    WP isa (VG.Impl.Ffdh.Arm.NormalizedPrepare.code K.op) s fun t =>
      ArithmeticReady base len (Spec.Rsa.modulusWords k) t ∧
      numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 0 =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 4 =
        2 ^ (128 * Spec.Rsa.modulusWords k) % Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.NormalizedPrepare.code, WP.seq_iff]
  refine WP.mono (prepare_input s h) ?_
  rintro u ⟨ready, frameU, restU⟩
  have pu := K.stable frameU restU hp
  have countFit := (pc_dimensions h.minLength h.maxLength h.space).2.2.2.2
  have bytes := rsa_bytes_frame (src := State.addr src) (k := k) frameU
    (by have := h.maxLength; omega) (by simpa using h.separate)
  refine WP.mono (normalizedPrecompute_ok K u pu ready.workspace ready.layout ready.width ready.positive ready.fits
    ready.sourceFits ready.readable ready.separate ready.ptr ready.source ready.count ready.stackRead
    ready.stackSep ready.saved ready.large ready.odd countFit (by rw [bytes]; exact normalized)) ?_
  rintro t ⟨done, modulus, r2, pt, frameT, restT⟩
  rw [bytes] at modulus r2
  exact ⟨⟨done.workspace, done.layout, done.width, done.ptr, done.inverse,
      by rw [modulus]; exact h.large, done.stackRead, done.stackSep, done.saved⟩,
    modulus, r2, pt, (frameU.mono (by simpa using K.workspace)).trans frameT, restU.trans restT⟩

end VG.Proof.Ffdh.Arm
