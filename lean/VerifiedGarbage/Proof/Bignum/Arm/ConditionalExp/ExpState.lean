module
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady

import VerifiedGarbage.Proof.Bignum.Arm.HeaderStore
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout

/-! # Binary exponentiation invariants in the shared RSA workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.ConditionalExp

variable {ok : Prop}
open VG VG.Arm
open VG.Proof.Rsa.Mont (numAt arrAt Keeps)

/-- Array 5 holds the Montgomery input, array 6 the running power, and array 7 ordinary one. -/
structure ExpState (ok : Prop) (base : BitVec 32) (len w M x E : Nat) (s : State) : Prop where
  ready : ArithmeticReady base len w s
  modulus : numAt s.mem (State.addr base) w 0 = M
  coprime : Nat.Coprime (2 ^ (64 * w)) M
  inputBound : numAt s.mem (State.addr base) w 5 < M
  inputValue : ok → numAt s.mem (State.addr base) w 5 % M = x * 2 ^ (64 * w) % M
  powerBound : numAt s.mem (State.addr base) w 6 < M
  powerValue : ok → numAt s.mem (State.addr base) w 6 % M = x ^ E * 2 ^ (64 * w) % M
  one : numAt s.mem (State.addr base) w 7 = 1
  r2 : ok → numAt s.mem (State.addr base) w 4 = 2 ^ (128 * w) % M

theorem ExpState.after_y {s t : State} {base : BitVec 32} {len w M x E F : Nat}
    (h : ExpState ok base len w M x E s) (ready : ArithmeticReady base len w t)
    (modulus : numAt t.mem (State.addr base) w 0 = M)
    (keeps : Keeps (State.addr base) len w 6 s.mem t.mem)
    (bound : numAt t.mem (State.addr base) w 6 < M)
    (value : ok → numAt t.mem (State.addr base) w 6 % M = x ^ F * 2 ^ (64 * w) % M) :
    ExpState ok base len w M x F t := by
  have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  have input := keeps_array_num keeps fits (q := 5) (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
  have one := keeps_array_num keeps fits (q := 7) (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
  exact ⟨ready, modulus, h.coprime, by rw [input]; exact h.inputBound,
    by rw [input]; exact h.inputValue, bound, value, one.trans h.one,
    fun ho => (keeps_array_num keeps fits (q := 4)
      (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)).trans (h.r2 ho)⟩

theorem ExpState.of_mem {s t : State} {base : BitVec 32} {len w M x E : Nat} {rs : List Reg}
    (h : ExpState ok base len w M x E s) (mem : t.mem = s.mem)
    (rest : VG.Proof.X25519.Arm.Rest rs s t) (ptr : t.gpr .r0 = base) : ExpState ok base len w M x E t := by
  refine ⟨h.ready.of_mem mem rest ptr, ?_, h.coprime, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [mem]
  exacts [h.modulus, h.inputBound, h.inputValue, h.powerBound, h.powerValue, h.one, h.r2]

theorem ExpState.after_header {s t : State} {base : BitVec 32} {len w M x E d : Nat} {value : BitVec 32}
    {rs : List Reg} (h : ExpState ok base len w M x E s) (hd : 128 ≤ d) (hd' : d + 4 ≤ 256)
    (mem : t.mem = s.mem.writeW (VG.Proof.Mont.off (State.addr base) d) value)
    (rest : VG.Proof.X25519.Arm.Rest rs s t) (ptr : t.gpr .r0 = base) :
    ExpState ok base len w M x E t ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem := by
  obtain ⟨ready, frame, arrays⟩ := h.ready.after_header hd hd' mem rest ptr
  refine ⟨⟨ready, ?_, h.coprime, ?_, ?_, ?_, ?_, ?_, ?_⟩, frame⟩
  · rw [arrays 0 (by decide)]; exact h.modulus
  · rw [arrays 5 (by decide)]; exact h.inputBound
  · rw [arrays 5 (by decide)]; exact h.inputValue
  · rw [arrays 6 (by decide)]; exact h.powerBound
  · rw [arrays 6 (by decide)]; exact h.powerValue
  · rw [arrays 7 (by decide)]; exact h.one
  · rw [arrays 4 (by decide)]; exact h.r2

end VG.Proof.Bignum.Arm.ConditionalExp
