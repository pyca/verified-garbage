module

public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Impl.Bignum.Arm.MontOp
public import VerifiedGarbage.Proof.Bignum.Arm.MontOp
public import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
public import VerifiedGarbage.Impl.Bignum.Arm.ReduceOperand
public import VerifiedGarbage.Proof.Bignum.Arm.ReduceOperandCT
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.StackCT

/-! # A Montgomery product that may write the 48 bytes below the stack

`CallOp` is a Montgomery product for any workspace whose caller leaves it the
48 bytes below the stack (`CallStack`): the inline product (`inlineCallOp`),
which writes only its workspace, and a call to a shared product
(`MontBackend.callOp`). Code generic over it is one proof for both. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.FrameStack VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

structure CallOp where
  op : Nat → Nat → Nat → Prog isa
  mont : ∀ (base sp : BitVec 32) (len w : Nat),
    TwoExp.Montgomery base len w (TwoExp.CallReady base sp len) [⟨State.addr base, 8 * len⟩, belowA sp 48]
  mont_op : ∀ base sp len w, (mont base sp len w).op = op
  timing : ∀ (base sp : BitVec 32) (len w : Nat), arrAt w 3 + 32 ≤ 8 * len →
    TwoExp.MontgomeryTiming (mont base sp len w)

/-- The inline product, `montOp`. -/
def inlineCallOp : CallOp where
  op := montOp
  mont _ _ _ _ := {
    op := montOp
    workspace := by simp
    stable := fun _ rest h => ⟨h.1.of_rest rest, rest.sp.trans h.2⟩
    op_ok := by
      intro s o a b ready hp ho ha hb ho0 operand
      refine WP.mono (montOp_ok s ready ho ha hb ho0 operand) ?_
      rintro t ⟨r, m, bd, v, k, f, rest⟩
      exact ⟨r, m, bd, v, k, ⟨hp.1.of_rest rest, rest.sp.trans hp.2⟩, f.mono (by simp), rest⟩ }
  mont_op _ _ _ _ := rfl
  timing _ _ _ _ fit := ⟨fun _ _ _ ho ha hb => (montOp_ct ho ha hb fit).mono
    (fun _ _ h => ⟨⟨h.1.1, h.1.2.2⟩, ⟨h.2.1.1, h.2.1.2.2⟩, h.2.2⟩) (fun _ _ _ => trivial)⟩

/-- A call to `b`'s product. -/
def MontBackend.callOp (b : MontBackend) : CallOp where
  op := MontCall.op b.name b.mul
  mont base sp len w := TwoExp.sharedMontgomery base sp len w b.name b.mul
    (fun _ _ _ ho ha hb z input => b.correct z input ho ha hb) b.stackOk
  mont_op _ _ _ _ := rfl
  timing base sp len w _ := TwoExp.sharedMontgomeryTiming base sp len w b.name b.mul
    (fun _ _ _ ho ha hb z input => b.correct z input ho ha hb) b.stackOk
    (fun _ _ _ ho ha hb => b.rawCT ho ha hb)

/-! ## Encoding and reduction by any Montgomery product -/

/-- `montEncode_ok`, by the product of `K`. -/
theorem montEncodeWith_ok {base : BitVec 32} {len w o a M : Nat} {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (s : State)
    (h : ArithmeticReady base len w s) (hp : P s) (ho : Operand o) (ha : Operand a) (ho0 : o ≠ 0)
    (modulus : numAt s.mem (State.addr base) w 0 = M) (odd : M % 2 = 1)
    (r2 : numAt s.mem (State.addr base) w 4 = 2 ^ (128 * w) % M) :
    WP isa (K.op o a 4) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w o = numAt s.mem (State.addr base) w a * 2 ^ (64 * w) % M ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧ P t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  have positive : 0 < M := by have := h.modulus; rw [modulus] at this; omega_using [odd]
  refine WP.mono (K.op_ok s o a 4 h hp ho ha
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) ho0
    (by rw [modulus, r2]; exact Nat.mod_lt _ positive)) ?_
  rintro t ⟨ready, modT, bound, value, keeps, pt, frame, rest⟩
  rw [modulus] at modT bound value
  have encoded : numAt t.mem (State.addr base) w o % M = numAt s.mem (State.addr base) w a * 2 ^ (64 * w) % M := by
    apply mont_cancel (coprime_pow2 odd (64 * w))
    rw [value, r2, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod,
      show 128 * w = 64 * w + 64 * w by omega_using [], Nat.pow_add, Nat.mul_assoc]
  rw [Nat.mod_eq_of_lt bound] at encoded
  exact ⟨ready, modT, encoded, keeps, pt, frame, rest⟩

/-- `reduceOperand_ok`, by the product of `K`. -/
theorem reduceOperandWith_ok {base : BitVec 32} {len w o M : Nat} {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (s : State)
    (h : ArithmeticReady base len w s) (hp : P s) (ho : Operand o) (ho0 : o ≠ 0) (ho7 : o ≠ 7)
    (modulus : numAt s.mem (State.addr base) w 0 = M) (odd : M % 2 = 1)
    (r2 : numAt s.mem (State.addr base) w 4 = 2 ^ (128 * w) % M)
    (one : numAt s.mem (State.addr base) w 7 = 1) :
    WP isa (reduceOperandWith K.op o) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w o = numAt s.mem (State.addr base) w o % M ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧ P t ∧
      Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  have op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  rw [reduceOperandWith, WP.seq_iff]
  refine WP.mono (montEncodeWith_ok K s h hp ho ho ho0 modulus odd r2) ?_
  rintro u ⟨readyU, modU, encoded, keepsU, pu, frameU, restU⟩
  have oneU := (keeps_array_num keepsU fits op7 (Ne.symm ho7)).trans one
  refine WP.mono (K.op_ok u o o 7 readyU pu ho ho op7 ho0 (by rw [oneU]; exact readyU.modulus)) ?_
  rintro t ⟨ready, modT, bound, value, keepsT, pt, frameT, restT⟩
  rw [modU] at modT bound value
  rw [oneU, Nat.mul_one, encoded, Nat.mod_mod] at value
  have reduced := mont_cancel (coprime_pow2 odd (64 * w)) value
  rw [Nat.mod_eq_of_lt bound] at reduced
  exact ⟨ready, modT, reduced, fun i hi sep => (keepsT i hi sep).trans (keepsU i hi sep), pt,
    frameU.trans frameT, restU.trans restT⟩

/-! ## The product with the stack its caller leaves it -/

theorem CallOp.op_ok (A : CallOp) (s : State) {base : BitVec 32} {len w o a b : Nat}
    (h : ArithmeticReady base len w s) (cs : CallStack base len s)
    (ho : Operand o) (ha : Operand a) (hb : Operand b) (ho0 : o ≠ 0)
    (operand : numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0) :
    WP isa (A.op o a b) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % numAt s.mem (State.addr base) w 0 =
        numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w b % numAt s.mem (State.addr base) w 0 ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩, belowA s.sp 48] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [← A.mont_op base s.sp len w]
  exact ((A.mont base s.sp len w).op_ok s o a b h ⟨cs, rfl⟩ ho ha hb ho0 operand).mono
    fun _ ⟨r, m, bd, v, k, _, f, rest⟩ => ⟨r, m, bd, v, k, f, rest⟩

theorem CallOp.op_ct (A : CallOp) {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b) (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t =>
      (ArithmeticReady base len w s ∧ CallStack base len s ∧
        numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0) ∧
      (ArithmeticReady base len w t ∧ CallStack base len t ∧
        numAt t.mem (State.addr base) w b < numAt t.mem (State.addr base) w 0) ∧ s.sp = t.sp)
      (A.op o a b) (fun _ _ => True) := by
  intro s t tr1 tr2 u v h e1 e2
  rw [← A.mont_op base s.sp len w] at e1 e2
  exact (A.timing base s.sp len w fit).op_ct o a b ho ha hb s t tr1 tr2 u v
    ⟨⟨h.1.1, ⟨h.1.2.1, rfl⟩, h.1.2.2⟩, ⟨h.2.1.1, ⟨h.2.1.2.1, h.2.2.symm⟩, h.2.1.2.2⟩, h.2.2⟩ e1 e2

/-- `reduceOperand_ct`, by `A`'s product. -/
theorem CallOp.reduceOperand_ct (A : CallOp) {base : BitVec 32} {len w o : Nat}
    (ho : Operand o) (ho0 : o ≠ 0) (ho7 : o ≠ 7) (fit : arrAt w 3 + 32 ≤ 8 * len) :
    RelCT isa (fun s t => (ReduceOperandReady base len w s ∧ CallStack base len s) ∧
      (ReduceOperandReady base len w t ∧ CallStack base len t) ∧ s.sp = t.sp)
      (reduceOperandWith A.op o) (fun _ _ => True) := by
  let P := fun s : State => ReduceOperandReady base len w s ∧ CallStack base len s
  let Q := fun s : State => ArithmeticReady base len w s ∧
    numAt s.mem (State.addr base) w 7 < numAt s.mem (State.addr base) w 0 ∧ CallStack base len s
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have encode : RelCT isa (fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp) (A.op o o 4) (fun _ _ => True) :=
    (A.op_ct ho ho op4 fit).mono (fun _ _ h => ⟨⟨h.1.1.ready, h.1.2, h.1.1.r2bound⟩,
      ⟨h.2.1.1.ready, h.2.1.2, h.2.1.1.r2bound⟩, h.2.2⟩) (fun _ _ _ => trivial)
  have wp (s : State) (h : P s) : WP isa (A.op o o 4) s Q := by
    refine WP.mono (A.op_ok s h.1.ready h.2 ho ho op4 ho0 h.1.r2bound) ?_
    rintro t ⟨ready, modulus, _, _, keeps, _, rest⟩
    have fits : arrAt w 8 ≤ 8 * len := h.1.ready.width ▸ h.1.ready.layout.2.2.1
    have one := keeps_array_num keeps fits op7 (Ne.symm ho7)
    exact ⟨ready, by rw [one, modulus]; exact h.1.onebound, h.2.of_rest rest⟩
  have encoded := (relCT_keep_sp encode (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  rw [reduceOperandWith]
  exact encoded.seq ((A.op_ct ho ho op7 fit).mono
    (fun _ _ h => ⟨⟨h.2.1.1, h.2.1.2.2, h.2.1.2.1⟩, ⟨h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩, h.1⟩)
    (fun _ _ _ => trivial))

end VG.Proof.Bignum.Arm
