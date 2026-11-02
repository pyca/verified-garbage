module

public import VerifiedGarbage.Impl.Ffdh.Arm.Arithmetic
public import VerifiedGarbage.Proof.Bignum.Arm.PcStack
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
public import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
import VerifiedGarbage.Proof.Bignum.Arm.PcHead
import VerifiedGarbage.Proof.Bignum.Arm.SetupFrame
import VerifiedGarbage.Proof.Bignum.Arm.Precompute
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.MontContract

/-! Reuse RSA's native modulus preparation without imposing public-RSA
exponent restrictions on FFDH scalars. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Rsa.Mont (numAt)

structure PrepareInput (base src : BitVec 32) (len k : Nat) (s : State) : Prop where
  workspace : Workspace s base (8 * len)
  stack : PcStack base (s.mem.readW (VG.Proof.Mont.off (State.addr s.sp) 4) 32) src len k s
  ptr : s.gpr .r0 = base
  count : s.gpr .r6 = BitVec.ofNat 32 k
  minLength : 64 ≤ k
  maxLength : k ≤ 1024
  space : Spec.Rsa.publicScratchWords k ≤ len
  sourceFits : src.toNat + k ≤ 2 ^ 32
  readable : InRegions (s.rd ++ s.wr) (State.addr src) k
  separate : Region.Disjoint ⟨State.addr src, k⟩ ⟨State.addr base, 8 * len⟩
  large : 1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)
  odd : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) % 2 = 1

theorem prepare_input (s : State) {base src : BitVec 32} {len k : Nat}
    (h : PrepareInput base src len k s) :
    WP isa VG.Impl.Bignum.Arm.PublicFn.prepare s fun t =>
      PrecomputeInput base src len (Spec.Rsa.modulusWords k) k t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧
      Rest VG.Proof.Bignum.Arm.roundClobbers s t := by
  obtain ⟨hw, hw', fits, bytesFit, _⟩ := pc_dimensions h.minLength h.maxLength h.space
  rw [VG.Impl.Bignum.Arm.PublicFn.prepare, WP.seq_iff]
  refine WP.mono (pcHead_ok s h.maxLength h.count) ?_
  rintro u ⟨limbs, zero, memU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (setup_frame_ok u (h.workspace.congr restU.wr) hw hw' fits
    ((restU.gpr .r0 (by simp)).trans h.ptr) limbs zero) ?_
  rintro v ⟨layout, width, ptr, frameV, restV⟩
  rw [memU] at frameV
  have restUV : Rest VG.Proof.Bignum.Arm.roundClobbers s v :=
    (restU.mono (by simp [VG.Proof.Bignum.Arm.roundClobbers])).trans restV
  have stackV := h.stack.after_workspace frameV restUV
  refine WP.mono (pcInputs_ok v stackV) ?_
  rintro t ⟨source, count, memT, restT⟩
  have rest := restUV.trans (restT.mono (by simp [VG.Proof.Bignum.Arm.roundClobbers]))
  have frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem := by rw [memT]; exact frameV
  have stack := h.stack.after_workspace frame rest
  have bytes := rsa_bytes_frame (src := State.addr src) (k := k) frame (by have := h.maxLength; omega) (by simpa using h.separate)
  refine ⟨⟨⟨h.workspace.congr rest.wr, by rw [memT]; exact layout,
    by rw [memT]; exact width, (restT.gpr .r0 (by simp)).trans ptr,
    by simpa only [VG.Proof.Mont.off, BitVec.add_zero] using stack.read (d := 0) (by decide),
    stack.separate.sub_left (Region.sub_prefix (by decide)), stack.savedBase⟩,
    by have := h.minLength; omega, bytesFit, h.sourceFits,
    by rw [rest.rd, rest.wr]; exact h.readable, h.separate, source, count,
    by rw [bytes]; exact h.large, by rw [bytes]; exact h.odd⟩, frame, rest⟩

theorem prepare_ok (s : State) {base src : BitVec 32} {len k : Nat}
    (h : PrepareInput base src len k s) :
    WP isa VG.Impl.Ffdh.Arm.prepare s fun t =>
      ArithmeticReady base len (Spec.Rsa.modulusWords k) t ∧
      numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 0 =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 4 =
        2 ^ (128 * Spec.Rsa.modulusWords k) % Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧
      Rest VG.Proof.Bignum.Arm.roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.prepare, WP.seq_iff]
  refine WP.mono (prepare_input s h) ?_
  rintro u ⟨ready, frameU, restU⟩
  have countFit := (pc_dimensions h.minLength h.maxLength h.space).2.2.2.2
  refine WP.mono (precompute_ok u ready.workspace ready.layout ready.width ready.positive ready.fits
    ready.sourceFits ready.readable ready.separate ready.ptr ready.source ready.count ready.stackRead
    ready.stackSep ready.saved ready.large ready.odd countFit) ?_
  rintro t ⟨done, modulus, r2, frameT, restT⟩
  have bytes := rsa_bytes_frame (src := State.addr src) (k := k) frameU (by have := h.maxLength; omega) (by simpa using h.separate)
  rw [bytes] at modulus r2
  exact ⟨⟨done.workspace, done.layout, done.width, done.ptr, done.inverse,
      by rw [modulus]; exact h.large, done.stackRead, done.stackSep, done.saved⟩,
    modulus, r2, frameU.trans frameT, restU.trans restT⟩

end VG.Proof.Ffdh.Arm
