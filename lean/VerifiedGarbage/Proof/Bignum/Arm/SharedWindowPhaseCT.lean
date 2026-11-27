module

public import VerifiedGarbage.Impl.Bignum.Arm.SharedWindow
public import VerifiedGarbage.Proof.Bignum.Arm.WindowPhase
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomeryCT
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowApplyCT
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowPhase
public import VerifiedGarbage.Proof.Bignum.Arm.WindowBuild
import VerifiedGarbage.Proof.Bignum.Arm.WindowScanCT
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
public import VerifiedGarbage.Proof.Bignum.Arm.WindowBytes
public import VerifiedGarbage.Proof.Bignum.Arm.WindowBitCT
import VerifiedGarbage.Proof.Bignum.Arm.ExpControl
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay

/-! ### `Bignum.Arm.SharedWindowBuildCT`, which only this module used -/

section

/-! # Shared-window table preparation and multiplication have public traces -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.SharedWindow
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.Bignum.Arm.TwoExp (Montgomery MontgomeryTiming OpInput)

theorem tablePrepare_ct {base : BitVec 32} {len w M1 M2 x1 x2 : Nat}
    (fits : arrAt w 16 ≤ 8 * len) :
    RelCT isa (fun s t => ExpState base len w M1 x1 0 s ∧ ExpState base len w M2 x2 0 t ∧ s.sp = t.sp)
      VG.Impl.Bignum.Arm.SharedWindow.tablePrepare (fun _ _ => True) := by
  have entry (j : Nat) {M x : Nat} (s : State) (h : TablePre base len w M x j s) : EntryReady base len w j s :=
    ⟨h.power.ready, h.entry⟩
  unfold VG.Impl.Bignum.Arm.SharedWindow.tablePrepare
  refine relCT_chain (Q₁ := TablePre base len w M1 x1 0) (Q₂ := TablePre base len w M2 x2 0)
    (tableInit_ct.mono (fun _ _ h => h.1.ready.ptr.trans h.2.1.ready.ptr.symm) (fun _ _ h => h))
    (fun s h => WP.mono (tableStage0_ok s h fits) fun _ k => k.1)
    (fun s h => WP.mono (tableStage0_ok s h fits) fun _ k => k.1) ?_
  refine relCT_chain (Q₁ := TablePre base len w M1 x1 1) (Q₂ := TablePre base len w M2 x2 1)
    ((entryStepCT (a := 6) (j := 0) (by decide) (by decide) fits).mono
      (fun _ _ h => ⟨entry 0 _ h.1, entry 0 _ h.2.1, h.2.2⟩) (fun _ _ h => h))
    (fun s h => WP.mono (tableStageStep_ok s h (a := 6) (by decide) (by decide) h.power.powerBound
      h.power.powerValue) fun _ k => k.1)
    (fun s h => WP.mono (tableStageStep_ok s h (a := 6) (by decide) (by decide) h.power.powerBound
      h.power.powerValue) fun _ k => k.1) ?_
  refine relCT_chain (Q₁ := TablePre base len w M1 x1 2) (Q₂ := TablePre base len w M2 x2 2)
    ((entryStepCT (a := 5) (j := 1) (by decide) (by decide) fits).mono
      (fun _ _ h => ⟨entry 1 _ h.1, entry 1 _ h.2.1, h.2.2⟩) (fun _ _ h => h))
    (fun s h => WP.mono (tableStageStep_ok s h (a := 5) (by decide) (by decide) h.power.inputBound
      (by rw [Nat.pow_one]; exact h.power.inputValue)) fun _ k => k.1)
    (fun s h => WP.mono (tableStageStep_ok s h (a := 5) (by decide) (by decide) h.power.inputBound
      (by rw [Nat.pow_one]; exact h.power.inputValue)) fun _ k => k.1) ?_
  exact prodInit_ct

section
variable {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
variable (A : Montgomery base len w P regions) (ct : MontgomeryTiming A)
include ct

theorem tableBody_ct {M1 M2 x1 x2 j : Nat} (hj : j < 8) (fits : arrAt w 16 ≤ 8 * len) :
    RelCT isa (fun s t => (BuildInv base len w M1 x1 j s ∧ P s) ∧
      (BuildInv base len w M2 x2 j t ∧ P t) ∧ s.sp = t.sp)
      (VG.Impl.Bignum.Arm.SharedWindow.tableBody A.op) (fun _ _ => True) := by
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op5 : Operand 5 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have entryOf (s : State) {M x : Nat} (h : BuildInv base len w M x j s ∧ P s) :
      WP isa (A.op 1 1 5) s (EntryReady base len w j) := by
    have size : 256 ≤ 8 * len := Nat.le_trans (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using []) h.1.fits
    refine WP.mono (A.op_ok s 1 1 5 h.1.power.ready h.2 op1 op1 op5 (by decide)
      (by rw [h.1.power.modulus]; exact h.1.power.inputBound)) ?_
    rintro t ⟨ready, _, _, _, keeps, _, _, _⟩
    exact ⟨ready, (keeps_header_readW keeps size (d := 220) (bits := 32) (by decide)).trans h.1.entry⟩
  unfold VG.Impl.Bignum.Arm.SharedWindow.tableBody
  exact relCT_chain ((ct.op_ct 1 1 5 op1 op1 op5).mono
    (fun _ _ h => ⟨⟨h.1.1.power.ready, h.1.2, by rw [h.1.1.power.modulus]; exact h.1.1.power.inputBound⟩,
      ⟨h.2.1.1.power.ready, h.2.1.2, by rw [h.2.1.1.power.modulus]; exact h.2.1.1.power.inputBound⟩, h.2.2⟩)
    (fun _ _ h => h)) (fun s h => entryOf s h) (fun s h => entryOf s h) (entryStepCT (by decide) hj fits)

theorem tableLoop_ct {M1 M2 x1 x2 : Nat} (fits : arrAt w 16 ≤ 8 * len) :
    RelCT isa (fun s t => (BuildInv base len w M1 x1 2 s ∧ P s) ∧
      (BuildInv base len w M2 x2 2 t ∧ P t) ∧ s.sp = t.sp)
      (.loop (VG.Impl.Bignum.Arm.SharedWindow.tableBody A.op) .ne) (fun _ _ => True) := by
  let I := fun k (s t : State) => ∃ j, j + k = 8 ∧ 0 < k ∧ 2 ≤ j ∧
    (BuildInv base len w M1 x1 j s ∧ P s) ∧ (BuildInv base len w M2 x2 j t ∧ P t) ∧ s.sp = t.sp
  have step : ∀ k, RelCT isa (I k) (VG.Impl.Bignum.Arm.SharedWindow.tableBody A.op) fun s t =>
      isa.eval .ne s = isa.eval .ne t ∧ (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ m, m < k ∧ I m s t) := by
    intro k s t tr1 tr2 u z h e1 e2
    obtain ⟨j, jk, hk, hj, hs, ht, sp⟩ := h
    have c := relCT_keep_sp (tableBody_ct A ct (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2)
      (j := j) (by omega_using [jk, hk]) fits) (fun _ _ h => h.2.2)
    obtain ⟨trace, sp'⟩ := c s t tr1 tr2 u z ⟨hs, ht, sp⟩ e1 e2
    obtain ⟨_, _, run1, next1, zero1, _, p1, _, _⟩ := sharedTableBody_ok A s hs.1 hs.2 hj (by omega_using [jk, hk])
    obtain ⟨_, _, run2, next2, zero2, _, p2, _, _⟩ := sharedTableBody_ok A t ht.1 ht.2 hj (by omega_using [jk, hk])
    obtain ⟨-, rfl⟩ := Exec.det e1 run1
    obtain ⟨-, rfl⟩ := Exec.det e2 run2
    refine ⟨trace, ?_, fun _ => trivial, ?_⟩
    · change some (!_) = some (!_)
      rw [zero1, zero2]
    · intro again
      have notLast : j + 1 ≠ 8 := by
        intro last
        change some (!_) = some true at again
        simp only [zero1, last, decide_true, Bool.not_true, Option.some.injEq, Bool.false_eq_true] at again
      exact ⟨k - 1, by omega_using [hk], j + 1, by omega_using [jk, hk], by omega_using [jk, hk, notLast], by omega_using [hj], ⟨next1, p1⟩, ⟨next2, p2⟩, sp'⟩
  exact (RelCT.loop I step 6).mono (fun _ _ h => ⟨2, by decide, by decide, by decide, h.1, h.2.1, h.2.2⟩) (fun _ _ h => h)

theorem tableBuild_ct {M1 M2 x1 x2 : Nat} (fits : arrAt w 16 ≤ 8 * len) :
    RelCT isa (fun s t => (ExpState base len w M1 x1 0 s ∧ P s) ∧
      (ExpState base len w M2 x2 0 t ∧ P t) ∧ s.sp = t.sp)
      (VG.Impl.Bignum.Arm.SharedWindow.tableBuild A.op) (fun _ _ => True) := by
  have ready (s : State) {M x : Nat} (h : ExpState base len w M x 0 s ∧ P s) :
      WP isa VG.Impl.Bignum.Arm.SharedWindow.tablePrepare s fun t => BuildInv base len w M x 2 t ∧ P t :=
    WP.mono (sharedTablePrepare_ok A s h.1 h.2 fits) fun _ k => ⟨k.1, k.2.2.1⟩
  unfold VG.Impl.Bignum.Arm.SharedWindow.tableBuild
  exact relCT_chain ((tablePrepare_ct fits).mono
    (fun _ _ h => ⟨h.1.1, h.2.1.1, h.2.2⟩) (fun _ _ h => h))
    (fun s h => ready s h) (fun s h => ready s h) (tableLoop_ct A ct fits)

end
end VG.Proof.Bignum.Arm.SharedWindow

end

end

/-! ### `Bignum.Arm.SharedWindowBitCT`, which only this module used -/

section

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
    have : 2 ^ (q + 1) ≤ 2 ^ 3 := Nat.pow_le_pow_right (n := 2) (by decide) (by omega_using [short])
    exact ⟨zV, ⟨power, table, by omega_using [bound, this], digit⟩, K.stable frame rest h.2⟩
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
      omega_using [this]
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
    have hp : 2 ^ j ≤ 128 := Nat.pow_le_pow_right (by decide) (by omega_using [jk, hk] : j ≤ 7)
    have fit1 : v1 * 2 ^ j < 2 ^ 32 := by have := Nat.mul_le_mul_left v1 hp; omega_using [hv1, this]
    have fit2 : v2 * 2 ^ j < 2 ^ 32 := by have := Nat.mul_le_mul_left v2 hp; omega_using [hv2, this]
    have ct := relCT_keep_sp (round_ct K ct (base := base) (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2)
      (A1 := A1) (A2 := A2) (p1 := p1) (p2 := p2) (q := (n + j) % 3) (V1 := v1 * 2 ^ j) (V2 := v2 * 2 ^ j)
      fits) (fun _ _ h => h.2.2)
    obtain ⟨trace, sp'⟩ := ct s t tr1 tr2 u z ⟨⟨⟨state1, fit1, byte1⟩, hs.2⟩, ⟨⟨state2, fit2, byte2⟩, ht.2⟩, sp⟩ e1 e2
    obtain ⟨_, _, run1, ⟨⟨A1', p1', next1, sumN1⟩, byteN1, countN1, zero1, _, pn1, _, _⟩⟩ :=
      sharedWindowRound_ok K s state1 hs.2 fit1 (c := 8 - j) (by omega_using [jk, hk]) (by omega_using []) byte1 count1
    obtain ⟨_, _, run2, ⟨⟨A2', p2', next2, sumN2⟩, byteN2, countN2, zero2, _, pn2, _, _⟩⟩ :=
      sharedWindowRound_ok K t state2 ht.2 fit2 (c := 8 - j) (by omega_using [jk, hk]) (by omega_using []) byte2 count2
    obtain ⟨-, rfl⟩ := Exec.det e1 run1
    obtain ⟨-, rfl⟩ := Exec.det e2 run2
    refine ⟨trace, ?_, fun _ => trivial, ?_⟩
    · change some (!_) = some (!_)
      rw [zero1, zero2]
    · intro again
      have notLast : j + 1 ≠ 8 := by
        intro last
        change some (!_) = some true at again
        simp only [zero1, show 8 - j = 1 by omega_using [last], decide_true, Bool.not_true, Option.some.injEq,
          Bool.false_eq_true] at again
      have expEq (E v : Nat) : 2 * (E * 2 ^ j + v / 2 ^ (8 - j)) + v * 2 ^ j / 128 % 2 =
          E * 2 ^ (j + 1) + v / 2 ^ (8 - (j + 1)) := by
        rw [Nat.mul_add, Nat.add_assoc, bit_step (by omega_using [jk, hk]), show 7 - j = 8 - (j + 1) by omega_using [],
          Nat.pow_succ, Nat.mul_comm 2 (E * 2 ^ j), Nat.mul_assoc]
      rw [sum1, expEq] at sumN1
      rw [sum2, expEq] at sumN2
      rw [Nat.mod_add_mod] at next1 next2
      refine ⟨k - 1, by omega_using [hk], j + 1, by omega_using [jk, hk], by omega_using [jk, hk, notLast], ⟨⟨⟨A1', p1', next1, sumN1⟩, ?_, ?_⟩, pn1⟩,
        ⟨⟨⟨A2', p2', next2, sumN2⟩, ?_, ?_⟩, pn2⟩, sp'⟩
      · rw [byteN1, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]
      · rw [countN1]; congr 1
      · rw [byteN2, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]
      · rw [countN2]; congr 1
  unfold VG.Impl.Bignum.Arm.SharedWindow.bits
  exact (RelCT.loop I step 8).mono (fun _ _ h => ⟨0, rfl, by decide, h.1, h.2.1, h.2.2⟩) (fun _ _ h => h)

end
end VG.Proof.Bignum.Arm.SharedWindow

end

end

/-! # The shared three-bit exponentiation schedule hides scalar values -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/SharedWindowBytesCT.lean`, which only this module imported.
section

/-! # Shared-window byte iteration preserves a fixed public exponent schedule -/

section
namespace VG.Proof.Bignum.Arm.SharedWindow
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.Bignum.Arm.TwoExp (Montgomery MontgomeryTiming)
section
variable {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
variable (K : Montgomery base len w P regions) (ct : MontgomeryTiming K)
include ct

theorem byteBody_ct {ep : BitVec 32} {M1 M2 x1 x2 j : Nat} {eb1 eb2 : List Byte}
    (fits : arrAt w 16 ≤ 8 * len) (hj1 : j < eb1.length)
    (hj2 : j < eb2.length) :
    RelCT isa (fun s t => (WinByteLoop base ep len w M1 x1 eb1 j s ∧ P s) ∧ (WinByteLoop base ep len w M2 x2 eb2 j t ∧ P t) ∧
      s.sp = t.sp) (.seq expByteHead (.seq (VG.Impl.Bignum.Arm.SharedWindow.bits K.op) (.block expByteNext))) (fun _ _ => True) := by
  -- after the head: the bits of the byte
  have head (s : State) {M x : Nat} {eb : List Byte} (h : WinByteLoop base ep len w M x eb j s ∧ P s)
      (hj : j < eb.length) :
      WP isa expByteHead s fun t => WinBitState base len w M x (pre eb j) (eb[j]).toNat (8 * j) 0 t ∧ P t := by
    obtain ⟨⟨A, p, state, sum⟩, ptr, _, _, sourceFit, read, _, bytes⟩ := h.1
    have address : State.addr (ep + BitVec.ofNat 32 j) = State.addr ep + BitVec.ofNat 64 j :=
      addr_add (by omega)
    have current : InRegions (s.rd ++ s.wr) (State.addr (ep + BitVec.ofNat 32 j)) 1 := by
      rw [address]; exact CallLay.inRegions_sub read (by omega) (by omega)
    refine WP.mono (windowByteHead_ok s state ptr current) ?_
    rintro u ⟨stateU, byteU, countU, _, frameU, restU⟩
    rw [address, bytes j hj] at byteU
    have v256 := (eb[j]).isLt
    exact ⟨⟨⟨A, p, stateU, by rw [sum, Nat.pow_zero, Nat.mul_one, Nat.sub_zero, show 2 ^ 8 = 256 from rfl,
      Nat.div_eq_of_lt v256, Nat.add_zero]⟩, by rw [Nat.pow_zero, Nat.mul_one]; exact byteU, countU⟩, K.stable frameU restU h.2⟩
  have bits (u : State) {M x E v n : Nat} (h : WinBitState base len w M x E v n 0 u ∧ P u) (hv : v < 256) :
      WP isa (VG.Impl.Bignum.Arm.SharedWindow.bits K.op) u fun y => y.gpr .r0 = base :=
    WP.mono (sharedWindowBits_ok K u h.1 h.2 hv) fun _ ⟨⟨_, _, k, _⟩, _⟩ => k.power.ready.ptr
  refine relCT_chain (Q₁ := fun s => WinBitState base len w M1 x1 (pre eb1 j) (eb1[j]).toNat (8 * j) 0 s ∧ P s)
    (Q₂ := fun s => WinBitState base len w M2 x2 (pre eb2 j) (eb2[j]).toNat (8 * j) 0 s ∧ P s)
    ((expByteHead_ct (base := base) (ep := ep + BitVec.ofNat 32 j) (len := len) (w := w)).mono
      (fun _ _ h => ⟨⟨(Classical.choose_spec (Classical.choose_spec h.1.1.state)).1.power.ready, h.1.1.pointer⟩,
        ⟨(Classical.choose_spec (Classical.choose_spec h.2.1.1.state)).1.power.ready, h.2.1.1.pointer⟩⟩)
      (fun _ _ h => h))
    (fun s h => head s h hj1) (fun s h => head s h hj2) ?_
  exact relCT_chain (Q₁ := fun s => s.gpr .r0 = base) (Q₂ := fun s => s.gpr .r0 = base)
    (bits_ct K ct fits (eb1[j]).isLt (eb2[j]).isLt)
    (fun s h => bits s h (eb1[j]).isLt) (fun s h => bits s h (eb2[j]).isLt)
    (expByteNext_ct.mono (fun _ _ h => h.1.trans h.2.1.symm) (fun _ _ h => h))

theorem bytes_ct {ep : BitVec 32} {M1 M2 x1 x2 : Nat} {eb1 eb2 : List Byte}
    (fits : arrAt w 16 ≤ 8 * len) (positive : 0 < eb1.length)
    (length : eb1.length = eb2.length)
    (separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb1.length⟩ r) :
    RelCT isa (fun s t => (WinByteLoop base ep len w M1 x1 eb1 0 s ∧ P s) ∧ (WinByteLoop base ep len w M2 x2 eb2 0 t ∧ P t) ∧
      s.sp = t.sp) (VG.Impl.Bignum.Arm.SharedWindow.bytes K.op) (fun _ _ => True) := by
  let I := fun k (s t : State) => ∃ j, j + k = eb1.length ∧ 0 < k ∧
    (WinByteLoop base ep len w M1 x1 eb1 j s ∧ P s) ∧ (WinByteLoop base ep len w M2 x2 eb2 j t ∧ P t) ∧ s.sp = t.sp
  have step : ∀ k, RelCT isa (I k) (.seq expByteHead (.seq (VG.Impl.Bignum.Arm.SharedWindow.bits K.op) (.block expByteNext))) fun s t =>
      isa.eval .ne s = isa.eval .ne t ∧ (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ m, m < k ∧ I m s t) := by
    intro k s t tr1 tr2 u z h e1 e2
    obtain ⟨j, jk, hk, hs, ht, sp⟩ := h
    have ct := relCT_keep_sp (byteBody_ct K ct (base := base) (ep := ep) (M1 := M1) (M2 := M2) (x1 := x1)
      (x2 := x2) (j := j) (eb1 := eb1) (eb2 := eb2) fits (by omega) (by omega)) (fun _ _ h => h.2.2)
    obtain ⟨trace, sp'⟩ := ct s t tr1 tr2 u z ⟨hs, ht, sp⟩ e1 e2
    obtain ⟨_, _, run1, next1, zero1, pn1, _, _⟩ := sharedWindowByteStep_ok K s hs.1 hs.2 (by omega) separate
    obtain ⟨_, _, run2, next2, zero2, pn2, _, _⟩ := sharedWindowByteStep_ok K t ht.1 ht.2 (by omega) (by rw [← length]; exact separate)
    obtain ⟨-, rfl⟩ := Exec.det e1 run1
    obtain ⟨-, rfl⟩ := Exec.det e2 run2
    refine ⟨trace, ?_, fun _ => trivial, ?_⟩
    · change some (!_) = some (!_)
      rw [zero1, zero2, length]
    · intro again
      have notLast : j + 1 ≠ eb1.length := by
        intro last
        change some (!_) = some true at again
        simp only [zero1, last, decide_true, Bool.not_true, Option.some.injEq, Bool.false_eq_true] at again
      exact ⟨k - 1, by omega, j + 1, by omega, by omega, ⟨next1, pn1⟩, ⟨next2, pn2⟩, sp'⟩
  unfold VG.Impl.Bignum.Arm.SharedWindow.bytes
  exact (RelCT.loop I step eb1.length).mono
    (fun _ _ h => ⟨0, by omega, positive, h.1, h.2.1, h.2.2⟩) (fun _ _ h => h)

end
end VG.Proof.Bignum.Arm.SharedWindow
end

end

@[expose] public section
namespace VG.Proof.Bignum.Arm.SharedWindow
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.Bignum.Arm.TwoExp (Montgomery MontgomeryTiming OpInput)

theorem phase_ct {base ep : BitVec 32} {len w M1 M2 x1 x2 : Nat} {eb1 eb2 : List Byte}
    {P : State → Prop} {regions : List Region}
    (K : Montgomery base len w P regions) (ct : MontgomeryTiming K)
    (fits : arrAt w 16 ≤ 8 * len) (positive : 0 < eb1.length)
    (length : eb1.length = eb2.length)
    (separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb1.length⟩ r) :
    RelCT isa (fun s t => (ExpPhaseInput base ep len w M1 x1 eb1 s ∧ P s) ∧
      (ExpPhaseInput base ep len w M2 x2 eb2 t ∧ P t) ∧ s.sp = t.sp)
      (VG.Impl.Bignum.Arm.SharedWindow.phase K.op) (fun _ _ => True) := by
  let F := fun (M x : Nat) (eb : List Byte) (s : State) =>
    ∃ A p, WinState base len w M x A p (8 * eb.length % 3) s ∧ A + p = Spec.Rsa.os2ip eb
  have separate2 : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb2.length⟩ r := by
    rw [← length]; exact separate
  have finishReady (s : State) {M x : Nat} {eb : List Byte} (h : F M x eb s ∧ P s) :
      WP isa (VG.Impl.Bignum.Arm.SharedWindow.apply K.op) s (OpInput base len w P 7) := by
    obtain ⟨⟨A, p, state, _⟩, hp⟩ := h
    refine WP.mono (sharedWindowApply_ok K s state.power hp state.table fits (pending_digit state) state.digit) ?_
    rintro t ⟨power, _, _, _, _, pt, _, _⟩
    exact ⟨power.ready, pt, by rw [power.one]; exact power.ready.modulus⟩
  have applying : RelCT isa (fun s t => (F M1 x1 eb1 s ∧ P s) ∧
      (F M2 x2 eb2 t ∧ P t) ∧ s.sp = t.sp)
      (VG.Impl.Bignum.Arm.SharedWindow.apply K.op) (fun _ _ => True) := by
    intro s t tr1 tr2 u z h e1 e2
    obtain ⟨⟨⟨A1, p1, state1, _⟩, ps⟩, ⟨⟨A2, p2, state2, _⟩, pt⟩, sp⟩ := h
    exact apply_ct K ct fits s t tr1 tr2 u z
      ⟨⟨⟨state1.power, state1.table, pending_digit state1, state1.digit⟩, ps⟩,
        ⟨⟨state2.power, state2.table, pending_digit state2, state2.digit⟩, pt⟩, sp⟩ e1 e2
  have reset (s : State) {M x : Nat} {eb : List Byte} (h : WinReady base ep len w M x eb s ∧ P s) :
      WP isa (.block windowReset) s fun t => WinByteLoop base ep len w M x eb 0 t ∧ P t :=
    WP.mono (phaseReset_ok s h.1) fun _ k => ⟨k.1, K.stable k.2.1 k.2.2 h.2⟩
  unfold VG.Impl.Bignum.Arm.SharedWindow.phase
  refine relCT_chain (Q₁ := fun s => ExpByteState base ep len w M1 x1 eb1 0 s ∧ P s)
    (Q₂ := fun s => ExpByteState base ep len w M2 x2 eb2 0 s ∧ P s)
    ((init_ct K ct).mono
      (fun _ _ h => ⟨⟨⟨h.1.1.ready, by rw [h.1.1.modulus]; exact h.1.1.r2bound⟩, h.1.2⟩,
        ⟨⟨h.2.1.1.ready, by rw [h.2.1.1.modulus]; exact h.2.1.1.r2bound⟩, h.2.1.2⟩, h.2.2⟩)
      (fun _ _ h => h))
    (fun s h => WP.mono (sharedPhaseInit_ready K s h.1 h.2 separate) fun _ k => ⟨k.1, k.2.1⟩)
    (fun s h => WP.mono (sharedPhaseInit_ready K s h.1 h.2 separate2) fun _ k => ⟨k.1, k.2.1⟩) ?_
  refine relCT_chain (Q₁ := fun s => WinReady base ep len w M1 x1 eb1 s ∧ P s)
    (Q₂ := fun s => WinReady base ep len w M2 x2 eb2 s ∧ P s)
    ((tableBuild_ct K ct fits).mono
      (fun _ _ h => ⟨⟨h.1.1.power, h.1.2⟩, ⟨h.2.1.1.power, h.2.1.2⟩, h.2.2⟩) (fun _ _ h => h))
    (fun s h => WP.mono (sharedPhaseTable_ok K s h.1 h.2 fits separate) fun _ k => ⟨k.1, k.2.1⟩)
    (fun s h => WP.mono (sharedPhaseTable_ok K s h.1 h.2 fits separate2) fun _ k => ⟨k.1, k.2.1⟩) ?_
  refine relCT_chain
    (windowReset_ct.mono (fun _ _ h => h.1.1.power.ready.ptr.trans h.2.1.1.power.ready.ptr.symm) (fun _ _ h => h))
    (fun s h => reset s h) (fun s h => reset s h) ?_
  refine relCT_chain (Q₁ := fun s => F M1 x1 eb1 s ∧ P s) (Q₂ := fun s => F M2 x2 eb2 s ∧ P s)
    (bytes_ct K ct fits positive length separate)
    (fun s h => WP.mono (sharedWindowBytes_ok K s h.1 h.2 positive separate) fun _ k => ⟨k.1, k.2.1⟩)
    (fun s h => WP.mono (sharedWindowBytes_ok K s h.1 h.2 (by omega) separate2) fun _ k => ⟨k.1, k.2.1⟩) ?_
  exact relCT_chain applying (fun s h => finishReady s h) (fun s h => finishReady s h)
    (ct.op_ct 6 6 7
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
      (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]))

end VG.Proof.Bignum.Arm.SharedWindow
