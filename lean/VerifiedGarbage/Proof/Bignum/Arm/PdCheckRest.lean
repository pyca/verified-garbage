module

public import VerifiedGarbage.Proof.Bignum.Arm.PdCheckState
public import VerifiedGarbage.Proof.Bignum.Arm.PdOdd
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Check the supplied R² range and modulus parity, retaining the public conjunction -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

def pdAccepted (N R : Nat) : Bool := decide (1 < N) && decide (R < N) && decide (N % 2 = 1)

theorem pdCheckRest_ok (s : State) {base : BitVec 32} {len w N R : Nat}
    (h : PdCheckState base len w N R s)
    (first : s.gpr .r11 = BitVec.ofNat 32 (decide (1 < N)).toNat) :
    WP isa (.seq (.block saveAcceptance)
      (.seq (arrayCompare 4 0) (.seq (.block mergeAcceptance) pdOdd))) s fun t =>
      PdCheckState base len w N R t ∧ t.gpr .r11 = BitVec.ofNat 32 (pdAccepted N R).toNat ∧
      t.z = !(pdAccepted N R) ∧
      Frame [⟨State.addr base, 8 * len⟩, ⟨off (State.addr s.sp) 48, 4⟩] s.mem t.mem ∧
      Rest roundClobbers s t := by
  rw [WP.seq_iff]
  refine WP.mono (saveAcceptanceLayout_ready s h.ready h.stackFit h.write h.separate) ?_
  rintro u ⟨readyU, savedU, eqU, frameU, restU, _⟩
  rw [first] at savedU
  have hu := h.after_flag readyU restU eqU
  rw [WP.seq_iff]
  refine WP.mono (arrayCompare_ok u hu.ready (by decide : 4 < 8) (by decide : 0 < 8)
    (by decide) (by decide)) ?_
  rintro v ⟨readyV, compared, keepsV, frameV, restV⟩
  rw [hu.r2, hu.modulus] at compared
  have hv := hu.after_array readyV restV keepsV (by decide) (by decide)
  have savedV := (hu.keep_flag frameV restV).trans savedU
  rw [WP.seq_iff]
  refine WP.mono (mergeAcceptanceLayout_ready v hv.ready hv.stackFit hv.write hv.separate) ?_
  rintro z ⟨readyZ, savedZ, eqZ, frameZ, restZ, _⟩
  have hz := hv.after_flag readyZ restZ eqZ
  rw [compared, savedV] at savedZ
  have bit : (if R < N then (1 : BitVec 32) else 0) &&& BitVec.ofNat 32 (decide (1 < N)).toNat =
      BitVec.ofNat 32 (decide (1 < N) && decide (R < N)).toNat := by
    by_cases hn : 1 < N <;> by_cases hr : R < N <;> simp [hn, hr]
  rw [bit] at savedZ
  refine WP.mono (pdOdd_ok z hz.ready hz.stackFit hz.read savedZ) ?_
  rintro t ⟨accepted, zero, memT, restT⟩
  rw [hz.modulus] at accepted zero
  have readyT := hz.ready.of_mem memT restT ((restT.gpr .r0 (by simp)).trans hz.ready.ptr)
  have ht := hz.after readyT restT (by rw [memT]; exact hz.modulus) (by rw [memT]; exact hz.r2)
  have rest : Rest roundClobbers s t := (restU.mono (by simp [roundClobbers])).trans
    (restV.trans ((restZ.mono (by simp [roundClobbers])).trans (restT.mono (by simp [roundClobbers]))))
  rw [restV.sp, restU.sp] at frameZ
  refine ⟨ht, accepted, zero, ?_, rest⟩
  rw [memT]
  exact (frameU.mono (by simp)).trans ((frameV.mono (by simp)).trans (frameZ.mono (by simp)))

end VG.Proof.Bignum.Arm
