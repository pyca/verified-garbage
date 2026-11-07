module

public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.HeaderStore
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout

/-! # The generator-two exponentiation invariant

The base is public and fixed. Keeping ordinary two in array 5 makes each
conditional multiply a linear modular doubling rather than a Montgomery
product. The exponent length and scalar distribution are unchanged.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm.TwoExp
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Keeps)
open VG.Proof.X25519.Arm (Rest)

structure Power (base : BitVec 32) (len w M E : Nat) (s : State) : Prop where
  ready : ArithmeticReady base len w s
  modulus : numAt s.mem (State.addr base) w 0 = M
  coprime : Nat.Coprime (2 ^ (64 * w)) M
  bound : numAt s.mem (State.addr base) w 6 < M
  value : numAt s.mem (State.addr base) w 6 % M = 2 ^ E * 2 ^ (64 * w) % M
  two : numAt s.mem (State.addr base) w 5 = 2
  one : numAt s.mem (State.addr base) w 7 = 1
  r2 : numAt s.mem (State.addr base) w 4 = 2 ^ (128 * w) % M

theorem Power.two_low {s : State} {base : BitVec 32} {len w M E : Nat}
    (h : Power base len w M E s) : w32 s.mem (State.addr base) (arrAt w 5) = 2 := by
  have hw : 2 ≤ w := h.ready.width ▸ h.ready.layout.1
  have eq := h.two
  rw [numAt_native, show 2 * w = (2 * w - 1) + 1 by omega, val32] at eq
  simp only [Nat.reducePow] at eq
  omega

theorem Power.after_y {s t : State} {base : BitVec 32} {len w M E F : Nat}
    (h : Power base len w M E s) (ready : ArithmeticReady base len w t)
    (modulus : numAt t.mem (State.addr base) w 0 = M)
    (keeps : Keeps (State.addr base) len w 6 s.mem t.mem)
    (bound : numAt t.mem (State.addr base) w 6 < M)
    (value : numAt t.mem (State.addr base) w 6 % M = 2 ^ F * 2 ^ (64 * w) % M) :
    Power base len w M F t := by
  have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  refine ⟨ready, modulus, h.coprime, bound, value, ?_, ?_, ?_⟩
  · rw [keeps_array_num keeps fits (q := 5)
      (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)]
    exact h.two
  · rw [keeps_array_num keeps fits (q := 7)
      (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)]
    exact h.one
  · rw [keeps_array_num keeps fits (q := 4)
      (by simp [Proof.Rsa.Mont.Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)]
    exact h.r2

end VG.Proof.Bignum.Arm.TwoExp
