module

public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Impl.Bignum.RISCV64.MontMul
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Montgomery multiplication on RISC-V: the steps of a round

`fiosStep_ok`: a word of a round, `tⱼ + aᵢ bⱼ + u mⱼ` plus the two carries,
its low word stored and the carries replaced. A carry out of an addition is
`sltu` of the sum and an operand (`carry_toNat`).
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum.RISCV64

/-- The carry out of `x + y`, as `sltu` of the sum and `y` computes it. -/
theorem carry_toNat (x y : BitVec 64) :
    (if x + y < y then (1 : BitVec 64) else 0).toNat = (decide (2 ^ 64 ≤ x.toNat + y.toNat)).toNat := by
  have hx := x.isLt
  have hy := y.isLt
  by_cases h : 2 ^ 64 ≤ x.toNat + y.toNat
  · have : x + y < y := by
      rw [BitVec.lt_def, BitVec.toNat_add]; omega
    simp [this, h]
  · have : ¬ x + y < y := by
      rw [BitVec.lt_def, BitVec.toNat_add]; omega
    simp only [this, h, ite_false, decide_false, Bool.toNat_false]; rfl

/-- The carry out of `y + x`, as `sltu` of the sum and `y` computes it. -/
theorem carry_toNat' (x y : BitVec 64) :
    (if y + x < y then (1 : BitVec 64) else 0).toNat = (decide (2 ^ 64 ≤ x.toNat + y.toNat)).toNat := by
  rw [BitVec.add_comm, carry_toNat]

/-- The arithmetic of one of a step's two sums: with `c₁ = c + x` and its
carry `k₁`, and `l = p q + c₁` and its carry `k₂`, the low word `l` and
`2⁶⁴` times the high word of `p q` plus both carries make `x + p q + c`,
below `2¹²⁸`. -/
theorem fios_chain (x p q c : BitVec 64) :
    (p * q + (c + x)).toNat +
      2 ^ 64 * (BitVec.ofNat 64 (p.toNat * q.toNat / 2 ^ 64) + (if c + x < x then 1 else 0) +
        (if p * q + (c + x) < c + x then 1 else 0)).toNat =
      x.toNat + p.toNat * q.toNat + c.toNat := by
  have hx := x.isLt
  have hp := p.isLt
  have hq := q.isLt
  have hc := c.isLt
  have hP : p.toNat * q.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  simp only [BitVec.toNat_add (_ + _), BitVec.toNat_add (BitVec.ofNat 64 _), carry_toNat]
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  by_cases h1 : 2 ^ 64 ≤ c.toNat + x.toNat <;>
    by_cases h2 : 2 ^ 64 ≤ p.toNat * q.toNat % 2 ^ 64 + (c.toNat + x.toNat) % 2 ^ 64 <;>
    simp only [h1, h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith

theorem fiosStep_writes (k : Nat) : writesOnly [.s0, .s1, .s2, .s3, .s4] (.block (fiosStep k)) = true := by
  rfl

theorem fiosStep_ok {s : State} {B : Addr} {Z dT dB dM k : Nat} (hs : Scr s B Z)
    (h3 : s.gpr .t3 = off B dT) (h4 : s.gpr .t4 = off B dB) (h0 : s.gpr .a0 = off B dM)
    (hk : k + 8 < 2048) (hk8 : k % 8 = 0) (hT8 : dT % 8 = 0) (hB8 : dB % 8 = 0) (hM8 : dM % 8 = 0)
    (hT : dT + k + 16 ≤ Z) (hB : dB + k + 16 ≤ Z) (hM : dM + k + 16 ≤ Z) :
    WP isa (.block (fiosStep k)) s fun s' =>
      (∃ v : BitVec 64, s'.mem = s.mem.writeW (off B (dT + k)) v ∧
        v.toNat + 2 ^ 64 * ((s'.gpr .s0).toNat + (s'.gpr .s1).toNat) =
          (word s.mem B (dT + (k + 8))).toNat + (s.gpr .t6).toNat * (word s.mem B (dB + (k + 8))).toNat +
            (s.gpr .t2).toNat * (word s.mem B (dM + (k + 8))).toNat +
            ((s.gpr .s0).toNat + (s.gpr .s1).toNat)) ∧ Keep [.s0, .s1, .s2, .s3, .s4] s s' := by
  have hk1 : k < 2048 := by omega_arith
  refine WP.keep _ ?_ (fiosStep_writes k) (by rfl)
  unfold fiosStep
  brun [h3, h4, h0, hk, hk1, hs.ld (show dT + (k + 8) + 8 ≤ Z by omega_arith),
    hs.ld (show dB + (k + 8) + 8 ≤ Z by omega_arith), hs.ld (show dM + (k + 8) + 8 ≤ Z by omega_arith),
    hs.st (show dT + k + 8 ≤ Z by omega_arith),
    hs.al8 (show dT + (k + 8) + 8 ≤ Z by omega_arith) (by omega_arith),
    hs.al8 (show dB + (k + 8) + 8 ≤ Z by omega_arith) (by omega_arith),
    hs.al8 (show dM + (k + 8) + 8 ≤ Z by omega_arith) (by omega_arith),
    hs.al8 (show dT + k + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine ⟨_, rfl, ?_⟩
  have h1 := fios_chain (word s.mem B (dT + (k + 8))) (s.gpr .t6) (word s.mem B (dB + (k + 8))) (s.gpr .s0)
  have h2 := fios_chain (s.gpr .t6 * word s.mem B (dB + (k + 8)) + (s.gpr .s0 + word s.mem B (dT + (k + 8))))
    (s.gpr .t2) (word s.mem B (dM + (k + 8))) (s.gpr .s1)
  simp only [Nat.reducePow, word] at h1 h2 ⊢
  omega_arith

end VG.Proof.Bignum.RISCV64
