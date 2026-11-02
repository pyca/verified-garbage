module

public import VerifiedGarbage.Impl.Bignum.Arm.PreparePrime
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopState
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeInverse
import VerifiedGarbage.Proof.Bignum.Arm.R2
import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulus
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Framework.Block

/-! # Invalid secret factors still enter well-defined Montgomery arithmetic -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

/-- This value is used only in proofs; selection is implemented in ARM code. -/
def safePrime (bit M : Nat) : Nat := if bit = 0 then 3 else M

theorem safePrime_valid {bit M : Nat} (good : bit ≠ 0 → 1 < M ∧ M % 2 = 1) :
    1 < safePrime bit M ∧ safePrime bit M % 2 = 1 := by
  unfold safePrime
  split
  · decide
  · rename_i h; exact good h

structure PrimeInput (base : BitVec 32) (len w : Nat) (s : State) : Prop
    extends LayoutFrameReady base len w s where
  bit : (s.mem.readW (off (State.addr base) 212) 32).toNat ≤ 1
  valid : (s.mem.readW (off (State.addr base) 212) 32).toNat ≠ 0 →
    1 < numAt s.mem (State.addr base) w 0 ∧ numAt s.mem (State.addr base) w 0 % 2 = 1

theorem preparePrime_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : PrimeInput base len w s) (countFits : 128 * w < 2 ^ 32) :
    WP isa preparePrime s fun t =>
      let M := safePrime (s.mem.readW (off (State.addr base) 212) 32).toNat (numAt s.mem (State.addr base) w 0)
      DoubleLoopReady base len w 0 t ∧ numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % M ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have valid := safePrime_valid h.valid
  rw [preparePrime, WP.seq_iff]
  refine WP.mono (sanitizeModulus_ok s h.workspace h.layout h.width h.ptr h.bit h.stackRead h.stackSep h.saved) ?_
  rintro u ⟨layoutU, widthU, modulus, _, frameU, restU, ptrU⟩
  change numAt u.mem (State.addr base) w 0 = safePrime _ _ at modulus
  rw [WP.seq_iff]
  refine WP.mono (precomputeInverse_ok u (h.workspace.congr restU.wr) layoutU widthU ptrU
    (by rw [modulus]; exact valid.2) (by rw [modulus]; exact valid.1)
    (by rw [restU.rd, restU.wr, restU.sp]; exact h.stackRead)
    (by rw [restU.sp]; exact h.stackSep) (saved_base_kept frameU h.stackSep h.saved restU.sp)) ?_
  rintro v ⟨ready, modV, frameV, restV⟩
  refine WP.mono (r2_ok v ready countFits) ?_
  rintro t ⟨done, value, modT, frameT, restT⟩
  rw [modV, modulus] at value
  exact ⟨done, modT.trans (modV.trans modulus), value,
    frameU.trans (frameV.trans frameT), restU.trans (restV.trans restT)⟩

end VG.Proof.Bignum.Arm
