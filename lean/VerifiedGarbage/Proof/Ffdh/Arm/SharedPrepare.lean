module

public import VerifiedGarbage.Impl.Ffdh.Arm.SharedPrepare
public import VerifiedGarbage.Proof.Ffdh.Arm.Prepare
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery

import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Bignum.Arm.SharedPrecompute
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopState
import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.Arm.ImportModulus
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeInverse
import VerifiedGarbage.Proof.Bignum.Arm.SharedR2
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
/-! # FFDH preparation retains the shared RSA arithmetic contract -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/SharedPrecompute.lean`, which only this module imported.
section

/-! # Modulus import and inverse followed by shared R-squared preparation -/

section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt wOf Layout)
open VG.Proof.X25519.Arm (Rest)

theorem sharedPrecompute_ok {base src : BitVec 32} {len w k : Nat}
    {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (s : State) (hp : P s)
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (width : wOf s.mem (State.addr base) = w)
    (hk : 0 < k) (fit : k ≤ 8 * w) (srcFit : src.toNat + k ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr src) k)
    (sep : Region.Disjoint ⟨State.addr src, k⟩ ⟨State.addr base, 8 * len⟩)
    (ptr : s.gpr .r0 = base) (source : s.gpr .r4 = src) (count : s.gpr .r6 = BitVec.ofNat 32 k)
    (stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩)
    (saved : s.mem.readW (State.addr s.sp) 32 = base)
    (large : 1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k))
    (odd : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) % 2 = 1)
    (countFits : 128 * w < 2 ^ 32) :
    WP isa (SharedPrecompute.precompute K.op) s fun t => DoubleLoopReady base len w 0 t ∧
      numAt t.mem (State.addr base) w 0 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      numAt t.mem (State.addr base) w 4 =
        2 ^ (128 * w) % Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [SharedPrecompute.precompute, WP.seq_iff]
  refine WP.mono (importModulus_ok s ws layout width hk fit srcFit read sep ptr source count
    stackRead stackSep saved) ?_
  rintro u ⟨layoutU, widthU, ptrU, modulus, frameU, restU⟩
  have pu := K.stable frameU restU hp
  rw [WP.seq_iff]
  refine WP.mono (precomputeInverse_ok u (ws.congr restU.wr) layoutU widthU ptrU
    (by rw [modulus]; exact odd) (by rw [modulus]; exact large)
    (by rw [restU.rd, restU.wr, restU.sp]; exact stackRead)
    (by rw [restU.sp]; exact stackSep) (saved_base_kept frameU stackSep saved restU.sp)) ?_
  rintro v ⟨ready, modV, frameV, restV⟩
  have pv := K.stable frameV restV pu
  refine WP.mono (sharedR2_ok K v ready pv countFits) ?_
  rintro t ⟨done, value, modT, pt, frameT, restT⟩
  rw [modV, modulus] at value
  exact ⟨done, modT.trans (modV.trans modulus), value, pt,
    (frameU.trans frameV).mono (by simpa using K.workspace) |>.trans frameT,
    restU.trans (restV.trans restT)⟩

end VG.Proof.Bignum.Arm
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Rsa.Mont (numAt)

theorem sharedPrepare_ok (s : State) {base src : BitVec 32} {len k : Nat}
    {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len (Spec.Rsa.modulusWords k) P regions)
    (h : PrepareInput base src len k s) (hp : P s) :
    WP isa (VG.Impl.Ffdh.Arm.SharedPrepare.code K.op) s fun t =>
      ArithmeticReady base len (Spec.Rsa.modulusWords k) t ∧
      numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 0 =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      numAt t.mem (State.addr base) (Spec.Rsa.modulusWords k) 4 =
        2 ^ (128 * Spec.Rsa.modulusWords k) % Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k) ∧
      P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.SharedPrepare.code, WP.seq_iff]
  refine WP.mono (prepare_input s h) ?_
  rintro u ⟨ready, frameU, restU⟩
  have pu := K.stable frameU restU hp
  have countFit := (pc_dimensions h.minLength h.maxLength h.space).2.2.2.2
  refine WP.mono (sharedPrecompute_ok K u pu ready.workspace ready.layout ready.width ready.positive ready.fits
    ready.sourceFits ready.readable ready.separate ready.ptr ready.source ready.count ready.stackRead
    ready.stackSep ready.saved ready.large ready.odd countFit) ?_
  rintro t ⟨done, modulus, r2, pt, frameT, restT⟩
  have bytes := rsa_bytes_frame (src := State.addr src) (k := k) frameU
    (by have := h.maxLength; omega) (by simpa using h.separate)
  rw [bytes] at modulus r2
  exact ⟨⟨done.workspace, done.layout, done.width, done.ptr, done.inverse,
      by rw [modulus]; exact h.large, done.stackRead, done.stackSep, done.saved⟩,
    modulus, r2, pt, (frameU.mono (by simpa using K.workspace)).trans frameT, restU.trans restT⟩

end VG.Proof.Ffdh.Arm
