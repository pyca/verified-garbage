module
public import VerifiedGarbage.Proof.Bignum.Arm.WindowBytes
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.Arm.WindowScanCT
import VerifiedGarbage.Proof.Bignum.Arm.SquareOpCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Bignum.Arm.ExpControl
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Layout

/-! # An exponent bit's trace depends only on the count of pending bits

The count of pending bits is the bit's position modulo 3, the same in any
two runs; the bit and the digit are only data. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest)

/-- A window state with the byte at 200. -/
def WinByte (base : BitVec 32) (len w M x A p q V : Nat) (s : State) : Prop :=
  WinState base len w M x A p q s ∧ V < 2 ^ 32 ∧
    s.mem.readW (VG.Proof.Mont.off (State.addr base) 200) 32 = BitVec.ofNat 32 V

theorem windowBit_ct {base : BitVec 32} {len w M1 M2 x1 x2 A1 A2 p1 p2 q V1 V2 : Nat}
    (fit : arrAt w 3 + 32 ≤ 8 * len) (fits : arrAt w 16 ≤ 8 * len) :
    RelCT isa (fun s t => WinByte base len w M1 x1 A1 p1 q V1 s ∧ WinByte base len w M2 x2 A2 p2 q V2 t ∧
      s.sp = t.sp) windowBit (fun _ _ => True) := by
  -- after the square and the join: the branch condition, and `windowApply`'s precondition
  let J := fun (M x A p V : Nat) (v : State) => v.z = decide (q + 1 = 3) ∧
    ScanPre base len w M x (2 * A) (2 * p + V / 128 % 2) v
  have joined (s : State) {M x A p V : Nat} (h : WinState base len w M x (2 * A) p q s ∧ V < 2 ^ 32 ∧
      s.mem.readW (VG.Proof.Mont.off (State.addr base) 200) 32 = BitVec.ofNat 32 V) :
      WP isa (.block windowBitValue) s (J M x A p V) := by
    refine WP.mono (windowJoin_ok s h.1 h.2.1 h.2.2) ?_
    rintro v ⟨power, table, bound, digit, _, zV, _, _, _⟩
    have short := h.1.short
    have : 2 ^ (q + 1) ≤ 2 ^ 3 := Nat.pow_le_pow_right (n := 2) (by decide) (by omega)
    exact ⟨zV, power, table, by omega, digit⟩
  have squared (s : State) {M x A p V : Nat} (h : WinByte base len w M x A p q V s) :
      WP isa (squareOp 6 6) s fun u => WinState base len w M x (2 * A) p q u ∧ V < 2 ^ 32 ∧
        u.mem.readW (VG.Proof.Mont.off (State.addr base) 200) 32 = BitVec.ofNat 32 V :=
    WP.mono (windowSquare_ok s h.1 h.2.2) fun _ k => ⟨k.1, h.2.1, k.2.1⟩
  unfold windowBit
  refine relCT_chain (squareOp_ct (base := base) (len := len) (w := w) (o := 6) (a := 6)
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) |>.mono
      (fun _ _ h => ⟨⟨h.1.1.power.ready, by rw [h.1.1.power.modulus]; exact h.1.1.power.powerBound⟩,
        ⟨h.2.1.1.power.ready, by rw [h.2.1.1.power.modulus]; exact h.2.1.1.power.powerBound⟩, h.2.2⟩)
      (fun _ _ h => h)) (fun s h => squared s h) (fun s h => squared s h) ?_
  refine relCT_chain (Q₁ := J M1 x1 A1 p1 V1) (Q₂ := J M2 x2 A2 p2 V2)
    (windowBitValue_ct.mono (fun _ _ h => h.1.1.power.ready.ptr.trans h.2.1.1.power.ready.ptr.symm)
      (fun _ _ h => h)) (fun s h => joined s h) (fun s h => joined s h) ?_
  refine RelCT.ite (fun s t h => ?_) ?_ ?_
  · change some s.z = some t.z
    rw [h.1.1, h.2.1.1]
  · exact (windowApply_ct fit fits).mono (fun _ _ h => ⟨h.1.1.2, h.1.2.1.2, h.1.2.2⟩) (fun _ _ h => h)
  · exact RelCT.block_nil (fun _ _ _ => trivial)

theorem windowRound_ct {base : BitVec 32} {len w M1 M2 x1 x2 A1 A2 p1 p2 q V1 V2 : Nat}
    (fit : arrAt w 3 + 32 ≤ 8 * len) (fits : arrAt w 16 ≤ 8 * len) :
    RelCT isa (fun s t => WinByte base len w M1 x1 A1 p1 q V1 s ∧ WinByte base len w M2 x2 A2 p2 q V2 t ∧
      s.sp = t.sp) windowRound (fun _ _ => True) := by
  have ready (s : State) {M x A p V : Nat} (h : WinByte base len w M x A p q V s) :
      WP isa windowBit s (ArithmeticReady base len w) :=
    WP.mono (windowBit_ok s h.1 h.2.1 h.2.2) fun _ ⟨⟨_, _, k, _⟩, _⟩ => k.power.ready
  have shifted (s : State) (h : ArithmeticReady base len w s) :
      WP isa (.block expShift) s fun t => t.gpr .r0 = base := by
    have size : 204 ≤ 8 * len := by
      have := h.layout.2.2.1
      simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at this
      omega
    exact WP.mono (expShift_ok s h.workspace size h.ptr (V := (s.mem.readW
      (VG.Proof.Mont.off (State.addr base) 200) 32).toNat) (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]))
      fun _ k => (k.2.gpr .r0 (by simp)).trans h.ptr
  unfold windowRound
  refine relCT_chain (windowBit_ct fit fits) (fun s h => ready s h) (fun s h => ready s h) ?_
  exact relCT_chain (Q₁ := fun s => s.gpr .r0 = base) (Q₂ := fun s => s.gpr .r0 = base)
    (expShift_ct.mono (fun _ _ h => h.1.ptr.trans h.2.1.ptr.symm) (fun _ _ h => h))
    (fun s h => shifted s h) (fun s h => shifted s h)
    (expDecrement_ct.mono (fun _ _ h => h.1.trans h.2.1.symm) (fun _ _ h => h))

theorem windowBits_ct {base : BitVec 32} {len w M1 M2 x1 x2 E1 E2 v1 v2 n : Nat}
    (fit : arrAt w 3 + 32 ≤ 8 * len) (fits : arrAt w 16 ≤ 8 * len) (hv1 : v1 < 256) (hv2 : v2 < 256) :
    RelCT isa (fun s t => WinBitState base len w M1 x1 E1 v1 n 0 s ∧ WinBitState base len w M2 x2 E2 v2 n 0 t ∧
      s.sp = t.sp) windowBits (fun _ _ => True) := by
  let I := fun k (s t : State) => ∃ j, j + k = 8 ∧ 0 < k ∧
    WinBitState base len w M1 x1 E1 v1 n j s ∧ WinBitState base len w M2 x2 E2 v2 n j t ∧ s.sp = t.sp
  have step : ∀ k, RelCT isa (I k) windowRound fun s t =>
      isa.eval .ne s = isa.eval .ne t ∧ (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ m, m < k ∧ I m s t) := by
    intro k s t tr1 tr2 u z h e1 e2
    obtain ⟨j, jk, hk, hs, ht, sp⟩ := h
    obtain ⟨⟨A1, p1, state1, sum1⟩, byte1, count1⟩ := hs
    obtain ⟨⟨A2, p2, state2, sum2⟩, byte2, count2⟩ := ht
    have hp : 2 ^ j ≤ 128 := Nat.pow_le_pow_right (by decide) (by omega : j ≤ 7)
    have fit1 : v1 * 2 ^ j < 2 ^ 32 := by have := Nat.mul_le_mul_left v1 hp; omega
    have fit2 : v2 * 2 ^ j < 2 ^ 32 := by have := Nat.mul_le_mul_left v2 hp; omega
    have ct := relCT_keep_sp (windowRound_ct (base := base) (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2)
      (A1 := A1) (A2 := A2) (p1 := p1) (p2 := p2) (q := (n + j) % 3) (V1 := v1 * 2 ^ j) (V2 := v2 * 2 ^ j)
      fit fits) (fun _ _ h => h.2.2)
    obtain ⟨trace, sp'⟩ := ct s t tr1 tr2 u z ⟨⟨state1, fit1, byte1⟩, ⟨state2, fit2, byte2⟩, sp⟩ e1 e2
    obtain ⟨_, _, run1, ⟨⟨A1', p1', next1, sumN1⟩, byteN1, countN1, zero1, _⟩⟩ :=
      windowRound_ok s state1 fit1 (c := 8 - j) (by omega) (by omega) byte1 count1
    obtain ⟨_, _, run2, ⟨⟨A2', p2', next2, sumN2⟩, byteN2, countN2, zero2, _⟩⟩ :=
      windowRound_ok t state2 fit2 (c := 8 - j) (by omega) (by omega) byte2 count2
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
      refine ⟨k - 1, by omega, j + 1, by omega, by omega, ⟨⟨A1', p1', next1, sumN1⟩, ?_, ?_⟩,
        ⟨⟨A2', p2', next2, sumN2⟩, ?_, ?_⟩, sp'⟩
      · rw [byteN1, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]
      · rw [countN1]; congr 1
      · rw [byteN2, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]
      · rw [countN2]; congr 1
  exact (RelCT.loop I step 8).mono (fun _ _ h => ⟨0, rfl, by decide, h.1, h.2.1, h.2.2⟩) (fun _ _ h => h)

end VG.Proof.Bignum.Arm
