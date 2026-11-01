module

public import VerifiedGarbage.Impl.Bignum.Arm.SharedWindow
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Proof.Bignum.Arm.WindowBytes

import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowApplyCT
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowBit
public import VerifiedGarbage.Proof.Bignum.Arm.WindowBitCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Bignum.Arm.ExpControl
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Shared-window bit and byte controls hide scalar bits -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.SharedWindow
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.Bignum.Arm.TwoExp (Montgomery MontgomeryTiming OpInput)

section
variable {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
variable (K : Montgomery base len w P regions) (ct : MontgomeryTiming K)
include ct

theorem bit_ct {M1 M2 x1 x2 A1 A2 p1 p2 q V1 V2 : Nat} (fits : arrAt w 16 ≤ 8 * len) :
    RelCT isa (fun s t => (WinByte base len w M1 x1 A1 p1 q V1 s ∧ P s) ∧
      (WinByte base len w M2 x2 A2 p2 q V2 t ∧ P t) ∧ s.sp = t.sp)
      (VG.Impl.Bignum.Arm.SharedWindow.bit K.op) (fun _ _ => True) := by
  let J := fun (M x A p V : Nat) (v : State) => v.z = decide (q + 1 = 3) ∧
    ScanPre base len w M x (2 * A) (2 * p + V / 128 % 2) v ∧ P v
  have joined (s : State) {M x A p V : Nat} (h : WinByte base len w M x (2 * A) p q V s ∧ P s) :
      WP isa (.block windowBitValue) s (J M x A p V) := by
    refine WP.mono (windowJoin_ok s h.1.1 h.1.2.1 h.1.2.2) ?_
    rintro v ⟨power, table, bound, digit, _, zV, _, frame, rest⟩
    have short := h.1.1.short
    have : 2 ^ (q + 1) ≤ 2 ^ 3 := Nat.pow_le_pow_right (n := 2) (by decide) (by omega)
    exact ⟨zV, ⟨power, table, by omega, digit⟩, K.stable frame rest h.2⟩
  have squared (s : State) {M x A p V : Nat} (h : WinByte base len w M x A p q V s ∧ P s) :
      WP isa (K.op 6 6 6) s fun u => WinByte base len w M x (2 * A) p q V u ∧ P u := by
    refine WP.mono (sharedWindowSquare_ok K s h.1.1 h.2 h.1.2.2) ?_
    rintro u ⟨state, byte, _, pu, _, _⟩
    exact ⟨⟨state, h.1.2.1, byte⟩, pu⟩
  have op6 : Operand 6 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  unfold VG.Impl.Bignum.Arm.SharedWindow.bit
  refine relCT_chain ((ct.op_ct 6 6 6 op6 op6 op6).mono
    (fun _ _ h => ⟨⟨h.1.1.1.power.ready, h.1.2, by rw [h.1.1.1.power.modulus]; exact h.1.1.1.power.powerBound⟩,
      ⟨h.2.1.1.1.power.ready, h.2.1.2, by rw [h.2.1.1.1.power.modulus]; exact h.2.1.1.1.power.powerBound⟩, h.2.2⟩)
    (fun _ _ h => h)) (fun s h => squared s h) (fun s h => squared s h) ?_
  refine relCT_chain (Q₁ := J M1 x1 A1 p1 V1) (Q₂ := J M2 x2 A2 p2 V2)
    (windowBitValue_ct.mono (fun _ _ h => h.1.1.1.power.ready.ptr.trans h.2.1.1.1.power.ready.ptr.symm)
      (fun _ _ h => h)) (fun s h => joined s h) (fun s h => joined s h) ?_
  refine RelCT.ite (fun s t h => ?_) ?_ ?_
  · change some s.z = some t.z
    rw [h.1.1, h.2.1.1]
  · exact (apply_ct K ct fits).mono (fun _ _ h => ⟨h.1.1.2, h.1.2.1.2, h.1.2.2⟩) (fun _ _ h => h)
  · exact RelCT.block_nil (fun _ _ _ => trivial)

theorem round_ct {M1 M2 x1 x2 A1 A2 p1 p2 q V1 V2 : Nat} (fits : arrAt w 16 ≤ 8 * len) :
    RelCT isa (fun s t => (WinByte base len w M1 x1 A1 p1 q V1 s ∧ P s) ∧
      (WinByte base len w M2 x2 A2 p2 q V2 t ∧ P t) ∧ s.sp = t.sp)
      (VG.Impl.Bignum.Arm.SharedWindow.round K.op) (fun _ _ => True) := by
  have ready (s : State) {M x A p V : Nat} (h : WinByte base len w M x A p q V s ∧ P s) :
      WP isa (VG.Impl.Bignum.Arm.SharedWindow.bit K.op) s (ArithmeticReady base len w) :=
    WP.mono (sharedWindowBit_ok K s h.1.1 h.2 h.1.2.1 h.1.2.2) fun _ ⟨⟨_, _, k, _⟩, _⟩ => k.power.ready
  have shifted (s : State) (h : ArithmeticReady base len w s) :
      WP isa (.block expShift) s fun t => t.gpr .r0 = base := by
    have size : 204 ≤ 8 * len := by
      have := h.layout.2.2.1
      simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at this
      omega
    exact WP.mono (expShift_ok s h.workspace size h.ptr (V := (s.mem.readW
      (VG.Proof.Mont.off (State.addr base) 200) 32).toNat) (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]))
      fun _ k => (k.2.gpr .r0 (by simp)).trans h.ptr
  unfold VG.Impl.Bignum.Arm.SharedWindow.round
  refine relCT_chain (bit_ct K ct fits) (fun s h => ready s h) (fun s h => ready s h) ?_
  exact relCT_chain (Q₁ := fun s => s.gpr .r0 = base) (Q₂ := fun s => s.gpr .r0 = base)
    (expShift_ct.mono (fun _ _ h => h.1.ptr.trans h.2.1.ptr.symm) (fun _ _ h => h))
    (fun s h => shifted s h) (fun s h => shifted s h)
    (expDecrement_ct.mono (fun _ _ h => h.1.trans h.2.1.symm) (fun _ _ h => h))

theorem bits_ct {M1 M2 x1 x2 E1 E2 v1 v2 n : Nat}
    (fits : arrAt w 16 ≤ 8 * len) (hv1 : v1 < 256) (hv2 : v2 < 256) :
    RelCT isa (fun s t => (WinBitState base len w M1 x1 E1 v1 n 0 s ∧ P s) ∧ (WinBitState base len w M2 x2 E2 v2 n 0 t ∧ P t) ∧
      s.sp = t.sp) (VG.Impl.Bignum.Arm.SharedWindow.bits K.op) (fun _ _ => True) := by
  let I := fun k (s t : State) => ∃ j, j + k = 8 ∧ 0 < k ∧
    (WinBitState base len w M1 x1 E1 v1 n j s ∧ P s) ∧ (WinBitState base len w M2 x2 E2 v2 n j t ∧ P t) ∧ s.sp = t.sp
  have step : ∀ k, RelCT isa (I k) (VG.Impl.Bignum.Arm.SharedWindow.round K.op) fun s t =>
      isa.eval .ne s = isa.eval .ne t ∧ (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ m, m < k ∧ I m s t) := by
    intro k s t tr1 tr2 u z h e1 e2
    obtain ⟨j, jk, hk, hs, ht, sp⟩ := h
    obtain ⟨⟨A1, p1, state1, sum1⟩, byte1, count1⟩ := hs.1
    obtain ⟨⟨A2, p2, state2, sum2⟩, byte2, count2⟩ := ht.1
    have hp : 2 ^ j ≤ 128 := Nat.pow_le_pow_right (by decide) (by omega : j ≤ 7)
    have fit1 : v1 * 2 ^ j < 2 ^ 32 := by have := Nat.mul_le_mul_left v1 hp; omega
    have fit2 : v2 * 2 ^ j < 2 ^ 32 := by have := Nat.mul_le_mul_left v2 hp; omega
    have ct := relCT_keep_sp (round_ct K ct (base := base) (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2)
      (A1 := A1) (A2 := A2) (p1 := p1) (p2 := p2) (q := (n + j) % 3) (V1 := v1 * 2 ^ j) (V2 := v2 * 2 ^ j)
      fits) (fun _ _ h => h.2.2)
    obtain ⟨trace, sp'⟩ := ct s t tr1 tr2 u z ⟨⟨⟨state1, fit1, byte1⟩, hs.2⟩, ⟨⟨state2, fit2, byte2⟩, ht.2⟩, sp⟩ e1 e2
    obtain ⟨_, _, run1, ⟨⟨A1', p1', next1, sumN1⟩, byteN1, countN1, zero1, _, pn1, _, _⟩⟩ :=
      sharedWindowRound_ok K s state1 hs.2 fit1 (c := 8 - j) (by omega) (by omega) byte1 count1
    obtain ⟨_, _, run2, ⟨⟨A2', p2', next2, sumN2⟩, byteN2, countN2, zero2, _, pn2, _, _⟩⟩ :=
      sharedWindowRound_ok K t state2 ht.2 fit2 (c := 8 - j) (by omega) (by omega) byte2 count2
    obtain ⟨-, rfl⟩ := Exec.det e1 run1
    obtain ⟨-, rfl⟩ := Exec.det e2 run2
    refine ⟨trace, ?_, fun _ => trivial, ?_⟩
    · change some (!_) = some (!_)
      rw [zero1, zero2]
    · intro again
      have notLast : j + 1 ≠ 8 := by
        intro last
        change some (!_) = some true at again
        simp only [zero1, show 8 - j = 1 by omega, decide_true, Bool.not_true, Option.some.injEq,
          Bool.false_eq_true] at again
      have expEq (E v : Nat) : 2 * (E * 2 ^ j + v / 2 ^ (8 - j)) + v * 2 ^ j / 128 % 2 =
          E * 2 ^ (j + 1) + v / 2 ^ (8 - (j + 1)) := by
        rw [Nat.mul_add, Nat.add_assoc, bit_step (by omega), show 7 - j = 8 - (j + 1) by omega,
          Nat.pow_succ, Nat.mul_comm 2 (E * 2 ^ j), Nat.mul_assoc]
      rw [sum1, expEq] at sumN1
      rw [sum2, expEq] at sumN2
      rw [Nat.mod_add_mod] at next1 next2
      refine ⟨k - 1, by omega, j + 1, by omega, by omega, ⟨⟨⟨A1', p1', next1, sumN1⟩, ?_, ?_⟩, pn1⟩,
        ⟨⟨⟨A2', p2', next2, sumN2⟩, ?_, ?_⟩, pn2⟩, sp'⟩
      · rw [byteN1, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]
      · rw [countN1]; congr 1
      · rw [byteN2, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]
      · rw [countN2]; congr 1
  unfold VG.Impl.Bignum.Arm.SharedWindow.bits
  exact (RelCT.loop I step 8).mono (fun _ _ h => ⟨0, rfl, by decide, h.1, h.2.1, h.2.2⟩) (fun _ _ h => h)

end
end VG.Proof.Bignum.Arm.SharedWindow
