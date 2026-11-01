module
public import VerifiedGarbage.Impl.Bignum.Arm.SharedWindow
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Proof.Bignum.Arm.ExpState
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.FoldedPublic
import VerifiedGarbage.Proof.Framework.Block

/-! Reuse the shared Montgomery calls for window initialization and conversion. -/
@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt arrAt Operand Keeps)
open VG.Proof.X25519.Arm (Rest)
theorem sharedWindowInit_ok {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (s : State) {M x : Nat}
    (h : ArithmeticReady base len w s) (hp : P s) (modulus : numAt s.mem (State.addr base) w 0 = M)
    (odd : M % 2 = 1) (input : numAt s.mem (State.addr base) w 1 = x)
    (r2bound : numAt s.mem (State.addr base) w 4 < M)
    (r2value : numAt s.mem (State.addr base) w 4 % M = 2 ^ (64 * w) * 2 ^ (64 * w) % M) :
    WP isa (SharedWindow.init K.op) s fun t => ExpState base len w M x 0 t ∧
      (∀ d, d + 4 ≤ 256 → t.mem.readW (VG.Proof.Mont.off (State.addr base) d) 32 =
        s.mem.readW (VG.Proof.Mont.off (State.addr base) d) 32) ∧
      P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  have op (q : Nat) (hq : q = 1 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7) : Operand q := by
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have coprime := coprime_pow2 odd (64 * w)
  rw [SharedWindow.init, WP.seq_iff]
  refine WP.mono (smallConst_ok s (1 : BitVec 32) h (o := 7) (by decide) (by decide) (by decide) (by decide)) ?_
  rintro u ⟨readyU, oneU, _, keepsU, frameU, restU⟩
  change numAt u.mem (State.addr base) w 7 = 1 at oneU
  have modU := (h.after_array (by decide) keepsU frameU restU readyU.ptr).2.trans modulus
  have inputU := (keeps_array_num keepsU fits (op 1 (by decide)) (by decide)).trans input
  have r2U := keeps_array_num keepsU fits (op 4 (by decide)) (by decide)
  have pU := K.stable frameU restU hp
  rw [WP.seq_iff]
  refine WP.mono (K.op_ok u 6 4 7 readyU pU (op 6 (by decide)) (op 4 (by decide)) (op 7 (by decide)) (by decide)
    (by rw [oneU]; exact readyU.modulus)) ?_
  rintro v ⟨readyV, modV, boundV, valueV, keepsV, pV, frameV, restV⟩
  rw [modU] at modV boundV valueV
  rw [oneU, Nat.mul_one, r2U, r2value] at valueV
  have powerV := mont_cancel coprime valueV
  have oneV := (keeps_array_num keepsV fits (op 7 (by decide)) (by decide)).trans oneU
  have inputV := (keeps_array_num keepsV fits (op 1 (by decide)) (by decide)).trans inputU
  have r2V := (keeps_array_num keepsV fits (op 4 (by decide)) (by decide)).trans r2U
  refine WP.mono (K.op_ok v 5 1 4 readyV pV (op 5 (by decide)) (op 1 (by decide)) (op 4 (by decide)) (by decide)
    (by rw [modV, r2V]; exact r2bound)) ?_
  rintro t ⟨readyT, modT, boundT, valueT, keepsT, pT, frameT, restT⟩
  rw [modV] at modT boundT valueT
  rw [inputV, r2V] at valueT
  have encoded : numAt t.mem (State.addr base) w 5 % M = x * 2 ^ (64 * w) % M := by
    apply mont_cancel coprime
    rw [valueT, Nat.mul_mod, r2value, ← Nat.mul_mod, Nat.mul_assoc]
  have powerT := keeps_array_num keepsT fits (op 6 (by decide)) (by decide)
  have oneT := (keeps_array_num keepsT fits (op 7 (by decide)) (by decide)).trans oneV
  have r2T := (keeps_array_num keepsT fits (op 4 (by decide)) (by decide)).trans r2V
  have r2Exact : numAt s.mem (State.addr base) w 4 = 2 ^ (128 * w) % M := by
    rw [Nat.mod_eq_of_lt r2bound, ← Nat.pow_add,
      show 64 * w + 64 * w = 128 * w by omega] at r2value
    exact r2value
  refine ⟨⟨readyT, modT, coprime, boundT, encoded, ?_, ?_, oneT, r2T.trans r2Exact⟩, ?_,
    pT, (Frame.mono frameU (by intro r hr; have er := List.mem_singleton.mp hr; subst r; exact K.workspace)).trans
      (frameV.trans frameT), restU.trans (restV.trans restT)⟩
  · rw [powerT]; exact boundV
  · rw [powerT, Nat.pow_zero, Nat.one_mul]; exact powerV
  · intro d hd
    rw [keeps_header_readW keepsT size (d := d) (bits := 32) hd,
      keeps_header_readW keepsV size (d := d) (bits := 32) hd,
      keeps_header_readW keepsU size (d := d) (bits := 32) hd]

theorem sharedExpSquare_ok {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (s : State) {M x E : Nat}
    (h : ExpState base len w M x E s) (hp : P s) :
    WP isa (K.op 6 6 6) s fun t => ExpState base len w M x (2 * E) t ∧
      Keeps (State.addr base) len w 6 s.mem t.mem ∧
      P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (K.op_ok s 6 6 6 h.ready hp
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
    (by rw [h.modulus]; exact h.powerBound)) ?_
  rintro t ⟨ready, modulus, bound, value, keeps, pt, frame, rest⟩
  rw [h.modulus] at modulus bound value
  exact ⟨h.after_y ready modulus keeps bound (mont_sq h.coprime h.powerValue value), keeps, pt, frame, rest⟩


theorem sharedExpFinish_ok {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (s : State) {M x E : Nat}
    (h : ExpState base len w M x E s) (hp : P s) :
    WP isa (K.op 6 6 7) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 6 = Spec.Rsa.powMod x E M ∧
      Keeps (State.addr base) len w 6 s.mem t.mem ∧
      P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (K.op_ok s 6 6 7 h.ready hp
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
    (by rw [h.one]; exact h.ready.modulus)) ?_
  rintro t ⟨ready, _, bound, value, keeps, pt, frame, rest⟩
  rw [h.modulus] at bound value
  rw [h.one] at value
  have final := mont_final_factor h.coprime h.powerValue value
  rw [Nat.mod_eq_of_lt bound, Nat.mul_one, ← powMod_eq] at final
  exact ⟨ready, final, keeps, pt, frame, rest⟩

end VG.Proof.Bignum.Arm
