module

public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpShared
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpSharedCT
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Block

/-! # A call of a backend's Montgomery product, in a caller's RSA workspace

`MontCall.op B.name B.mul o a b`, the call of the product `B` with the
operands `o a b` (`MontCall.op`), does what `montOp o a b` does, given the
48 bytes below the stack apart from the workspace (`CallStack`), which it may
write: `MontBackend.op_ok` and `op_ct` are `montOp_ok` and `montOp_ct` for
it, and `encode_ok` and `reduce_ok`, `reduce_ct` are `montEncode_ok` and
`reduceOperand_ok`, `reduceOperand_ct` for its calls. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.FrameStack VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem MontBackend.op_ok (B : MontBackend) (s : State) {base : BitVec 32} {len w o a b : Nat}
    (h : ArithmeticReady base len w s) (cs : CallStack base len s)
    (ho : Operand o) (ha : Operand a) (hb : Operand b) (ho0 : o ≠ 0)
    (operand : numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0) :
    WP isa (MontCall.op B.name B.mul o a b) s fun t =>
      ArithmeticReady base len w t ∧ CallStack base len t ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o < numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w o * 2 ^ (64 * w) % numAt s.mem (State.addr base) w 0 =
        numAt s.mem (State.addr base) w a * numAt s.mem (State.addr base) w b % numAt s.mem (State.addr base) w 0 ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩, belowA s.sp 48] s.mem t.mem ∧ Rest roundClobbers s t :=
  montCallOp_ok B.name B.mul (fun z input => B.correct z input ho ha hb) B.stackOk s h cs ho ha hb ho0 operand

theorem MontBackend.op_ct (B : MontBackend) {base : BitVec 32} {len w o a b : Nat}
    (ho : Operand o) (ha : Operand a) (hb : Operand b) :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧
      CallStack base len s ∧ CallStack base len t ∧
      numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w b < numAt t.mem (State.addr base) w 0 ∧ s.sp = t.sp)
      (MontCall.op B.name B.mul o a b) (fun s t => s.sp = t.sp) :=
  montCallOp_ct B.name B.mul (B.rawCT ho ha hb) ho ha hb

/-- `montEncode_ok`, by a call. -/
theorem MontBackend.encode_ok (B : MontBackend) (s : State) {base : BitVec 32} {len w o a M : Nat}
    (h : ArithmeticReady base len w s) (cs : CallStack base len s) (ho : Operand o) (ha : Operand a) (ho0 : o ≠ 0)
    (modulus : numAt s.mem (State.addr base) w 0 = M) (odd : M % 2 = 1)
    (r2 : numAt s.mem (State.addr base) w 4 = 2 ^ (128 * w) % M) :
    WP isa (MontCall.op B.name B.mul o a 4) s fun t => ArithmeticReady base len w t ∧ CallStack base len t ∧
      numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w o = numAt s.mem (State.addr base) w a * 2 ^ (64 * w) % M ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩, belowA s.sp 48] s.mem t.mem ∧ Rest roundClobbers s t := by
  have positive : 0 < M := by have := h.modulus; rw [modulus] at this; omega_using [odd]
  refine WP.mono (B.op_ok s h cs ho ha
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) ho0
    (by rw [modulus, r2]; exact Nat.mod_lt _ positive)) ?_
  rintro t ⟨ready, cs', modT, bound, value, keeps, frame, rest⟩
  rw [modulus] at modT bound value
  have encoded : numAt t.mem (State.addr base) w o % M = numAt s.mem (State.addr base) w a * 2 ^ (64 * w) % M := by
    apply mont_cancel (coprime_pow2 odd (64 * w))
    rw [value, r2, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod,
      show 128 * w = 64 * w + 64 * w by omega_using [], Nat.pow_add, Nat.mul_assoc]
  rw [Nat.mod_eq_of_lt bound] at encoded
  exact ⟨ready, cs', modT, encoded, keeps, frame, rest⟩

/-- `reduceOperand_ok`, by two calls: `[o] := [o] mod M`. -/
theorem MontBackend.reduce_ok (B : MontBackend) (s : State) {base : BitVec 32} {len w o M : Nat}
    (h : ArithmeticReady base len w s) (cs : CallStack base len s) (ho : Operand o) (ho0 : o ≠ 0) (ho7 : o ≠ 7)
    (modulus : numAt s.mem (State.addr base) w 0 = M) (odd : M % 2 = 1)
    (r2 : numAt s.mem (State.addr base) w 4 = 2 ^ (128 * w) % M)
    (one : numAt s.mem (State.addr base) w 7 = 1) :
    WP isa (.seq (MontCall.op B.name B.mul o o 4) (MontCall.op B.name B.mul o o 7)) s fun t =>
      ArithmeticReady base len w t ∧ CallStack base len t ∧
      numAt t.mem (State.addr base) w 0 = M ∧
      numAt t.mem (State.addr base) w o = numAt s.mem (State.addr base) w o % M ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩, belowA s.sp 48] s.mem t.mem ∧ Rest roundClobbers s t := by
  have op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  rw [WP.seq_iff]
  refine WP.mono (B.encode_ok s h cs ho ho ho0 modulus odd r2) ?_
  rintro u ⟨readyU, csU, modU, encoded, keepsU, frameU, restU⟩
  have oneU := (keeps_array_num keepsU fits op7 (Ne.symm ho7)).trans one
  refine WP.mono (B.op_ok u readyU csU ho ho op7 ho0 (by rw [oneU]; exact readyU.modulus)) ?_
  rintro t ⟨ready, csT, modT, bound, value, keepsT, frameT, restT⟩
  rw [modU] at modT bound value
  rw [oneU, Nat.mul_one, encoded, Nat.mod_mod] at value
  have reduced := mont_cancel (coprime_pow2 odd (64 * w)) value
  rw [Nat.mod_eq_of_lt bound] at reduced
  rw [restU.sp] at frameT
  exact ⟨ready, csT, modT, reduced, fun i hi sep => (keepsT i hi sep).trans (keepsU i hi sep),
    frameU.trans frameT, restU.trans restT⟩

/-- `reduceOperand_ct`, by two calls. -/
theorem MontBackend.reduce_ct (B : MontBackend) {base : BitVec 32} {len w o : Nat}
    (ho : Operand o) (ho0 : o ≠ 0) (ho7 : o ≠ 7) :
    RelCT isa (fun s t => (ArithmeticReady base len w s ∧ CallStack base len s ∧
        numAt s.mem (State.addr base) w 4 < numAt s.mem (State.addr base) w 0 ∧
        numAt s.mem (State.addr base) w 7 < numAt s.mem (State.addr base) w 0) ∧
      (ArithmeticReady base len w t ∧ CallStack base len t ∧
        numAt t.mem (State.addr base) w 4 < numAt t.mem (State.addr base) w 0 ∧
        numAt t.mem (State.addr base) w 7 < numAt t.mem (State.addr base) w 0) ∧ s.sp = t.sp)
      (.seq (MontCall.op B.name B.mul o o 4) (MontCall.op B.name B.mul o o 7)) (fun _ _ => True) := by
  let P := fun s : State => ArithmeticReady base len w s ∧ CallStack base len s ∧
    numAt s.mem (State.addr base) w 4 < numAt s.mem (State.addr base) w 0 ∧
    numAt s.mem (State.addr base) w 7 < numAt s.mem (State.addr base) w 0
  let Q := fun s : State => ArithmeticReady base len w s ∧ CallStack base len s ∧
    numAt s.mem (State.addr base) w 7 < numAt s.mem (State.addr base) w 0
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have encode : RelCT isa (fun (s t : State) => P s ∧ P t ∧ s.sp = t.sp)
      (MontCall.op B.name B.mul o o 4) (fun _ _ => True) :=
    (B.op_ct ho ho op4).mono (fun _ _ h => ⟨h.1.1, h.2.1.1, h.1.2.1, h.2.1.2.1, h.1.2.2.1, h.2.1.2.2.1, h.2.2⟩)
      (fun _ _ _ => trivial)
  have wp (s : State) (h : P s) : WP isa (MontCall.op B.name B.mul o o 4) s Q := by
    refine WP.mono (B.op_ok s h.1 h.2.1 ho ho op4 ho0 h.2.2.1) ?_
    rintro t ⟨ready, cs, modulus, _, _, keeps, _, _⟩
    have fits : arrAt w 8 ≤ 8 * len := h.1.width ▸ h.1.layout.2.2.1
    have one := keeps_array_num keeps fits op7 (Ne.symm ho7)
    exact ⟨ready, cs, by rw [one, modulus]; exact h.2.2.2⟩
  have encoded := (relCT_keep_sp encode (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wp s h.1, wp t h.2.1⟩)
  exact encoded.seq ((B.op_ct ho ho op7).mono
    (fun _ _ h => ⟨h.2.1.1, h.2.2.1, h.2.1.2.1, h.2.2.2.1, h.2.1.2.2, h.2.2.2.2, h.1⟩) (fun _ _ _ => trivial))

end VG.Proof.Bignum.Arm
