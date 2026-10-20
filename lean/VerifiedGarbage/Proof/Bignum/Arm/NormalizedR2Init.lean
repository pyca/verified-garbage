module

import VerifiedGarbage.Proof.Bignum.Arm.NormalizedR2Seed
public import VerifiedGarbage.Impl.Bignum.Arm.NormalizedR2
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Spec.Rsa.Mont
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopState
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.NormalizedR2Memory
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.R2
import VerifiedGarbage.Proof.Bignum.Arm.DoubleCountMemory
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block

/-! Initialize a reduced high-word seed and its shortened doubling loop. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem normalizedR2Constants_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) :
    WP isa NormalizedR2.constants s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 4 = 0 ∧ w32 t.mem (State.addr base) (arrAt w 7) = 2 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [NormalizedR2.constants, WP.seq_iff]
  refine WP.mono (smallConst_ok s (o := 4) 0 h (by decide) (by decide) (by decide) (by decide)) ?_
  rintro u ⟨ready, zero, _, keeps1, frame1, rest1⟩
  refine WP.mono (smallConst_ok u (o := 7) 2 ready (by decide) (by decide) (by decide) (by decide)) ?_
  rintro t ⟨next, _, two, keeps2, frame2, rest2⟩
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have op0 : Operand 0 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  exact ⟨next, (keeps_array_num keeps2 fits op4 (by decide)).trans zero, two,
    (keeps_array_num keeps2 fits op0 (by decide)).trans (keeps_array_num keeps1 fits op0 (by decide)),
    frame1.trans frame2, rest1.trans rest2⟩

theorem normalizedSeed_lt {m w : Nat} (hw : 2 ≤ w) (odd : m % 2 = 1)
    (normalized : 2 ^ (64 * (w - 1)) ≤ m) : 2 ^ (64 * (w - 1)) < m := by
  have even : 2 ^ (64 * (w - 1)) % 2 = 0 := by
    rw [show 64 * (w - 1) = (64 * (w - 1) - 1) + 1 by omega, Nat.pow_succ, Nat.mul_mod]
    simp
  omega

theorem normalizedR2Init_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s)
    (normalized : 2 ^ (64 * (w - 1)) ≤ numAt s.mem (State.addr base) w 0) :
    WP isa NormalizedR2.init s fun t => DoubleLoopReady base len w (w + 64) t ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (64 * (w - 1)) ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have fit4 := Nat.le_trans (array_end_le (w := w) (j := 4) (k := 8) (by decide)) fits
  have fit4 : arrAt w 4 + 8 * w ≤ 8 * len := by omega
  have size : 256 ≤ 8 * len := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at fits; omega
  have odd := numAt_odd_of_inverse s.mem (State.addr base) (by omega : 0 < w) h.inverse
  have strict := normalizedSeed_lt hw odd normalized
  rw [NormalizedR2.init, WP.seq_iff]
  refine WP.mono (normalizedR2Constants_ok s h) ?_
  rintro u ⟨ready, zero, two, modulus, frame, rest⟩
  rw [NormalizedR2.seed, WP.block_append_iff]
  have header := nativeHeader_of_layout u.mem base ready.workspace.nowrap (Nat.le_refl _) ready.layout
  rw [ready.width] at header
  refine WP.mono (normalizedR2Top_ok u ready.workspace hw fit4 ready.ptr header.count) ?_
  rintro v ⟨memV, restV⟩
  have outside := writeW32_outside u.mem (State.addr base) (d := arrAt w 4 + 8 * (w - 1)) (1#32)
    (by have := ready.workspace.nowrap; omega)
  rw [← memV] at outside
  have outside4 := outside.mono (o' := arrAt w 4) (n' := 8 * w) (by omega) (by omega)
  have frameV := outside_workspace outside4 fit4
  have keeps := outside_array_keeps outside4 (len := len) (by have := ready.workspace.nowrap; omega)
  have keepV : Rest roundClobbers u v := restV.mono (by simp [roundClobbers])
  obtain ⟨readyV, modV⟩ := ready.after_array (by decide : 4 ≠ 0) keeps frameV keepV
    ((restV.gpr .r0 (by simp)).trans ready.ptr)
  have value : numAt v.mem (State.addr base) w 4 = 2 ^ (64 * (w - 1)) := by
    rw [memV]; exact normalizedSeed_value u.mem (State.addr base) hw (by have hn := ready.workspace.nowrap; simp only [State.addr, BitVec.toNat_setWidth] ; omega) zero
  have twoV := keeps_array_word (d := 0) (bits := 32) keeps fits
    (show Operand 7 by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]) (by decide) (by omega)
  have twoV := congrArg BitVec.toNat twoV
  simp only [Nat.add_zero] at twoV
  let c := (v.mem.readW (off (State.addr base) 208) 32).toNat
  have loop : DoubleLoopReady base len w c v := by
    refine ⟨readyV.workspace, readyV.layout, readyV.width, readyV.ptr, readyV.inverse, ?_,
      twoV.trans two, ?_, readyV.stackRead, readyV.stackSep, readyV.saved⟩
    · rw [value, modV, modulus]; exact strict
    · simp only [c, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have headerV := nativeHeader_of_layout v.mem base readyV.workspace.nowrap (Nat.le_refl _) readyV.layout
  rw [readyV.width] at headerV
  refine WP.mono (normalizedR2Count_ok v readyV.workspace (by omega) readyV.ptr headerV.count) ?_
  rintro t ⟨memT, restT⟩
  obtain ⟨loopT, frameT, numberT, modT⟩ := loop.after_count memT restT
  exact ⟨loopT, numberT.trans value, modT.trans (modV.trans modulus),
    frame.trans (frameV.trans frameT), rest.trans (keepV.trans (restT.mono (by simp [roundClobbers])))⟩

end VG.Proof.Bignum.Arm
