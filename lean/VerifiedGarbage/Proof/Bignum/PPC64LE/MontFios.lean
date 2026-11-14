module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public meta import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
public meta import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
public import VerifiedGarbage.Impl.Bignum.PPC64LE.MontMul
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Multiword arithmetic on PPC64LE: carrying blocks and words of a round

`mcrun`: `prun` with the carrying adds (`State.writeCarry`, read through with
`Proof/Framework/PPC64LE/Carry.lean`). The arithmetic of the words of a round
(`MontRounds.lean`) and of the code that stores words of a number: words
appended (`fios_wordsVal_append`, `fios_wordsVal_write_top`,
`fios_wordsVal_write2`), sums of pieces (`fios_sum_group`, `fios_round_sum`),
and the counts of a round (`fios_rem`, `fios_quot`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Impl.Bignum.PPC64LE

theorem mont_ca_mem (s : State) (m : Mem) : ({ s with mem := m } : State).ca = s.ca := rfl

/-- `prun` through carrying writes. -/
tactic_template "mcrun" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
                       prun [exec_mulhu, exec_addc, exec_addze, exec_subc, exec_sube, gpr_writeCarry,
                         ca_writeCarry, ca_write, mont_ca_mem, mem_writeCarry, rd_writeCarry, wr_writeCarry,
                         sp_writeCarry, lr_writeCarry, $ls,*]))

/-! ## The words of a round -/

/-- A store of word `j` of a number of `j + 1` words. -/
theorem fios_wordsVal_write_top (m : Mem) (B : Addr) (d j : Nat) (v : BitVec 64) (h : d + 8 * j + 8 ≤ 2 ^ 64) :
    wordsVal (m.writeW (off B (d + 8 * j)) v) B d (j + 1) = wordsVal m B d j + 2 ^ (64 * j) * v.toNat := by
  rw [wordsVal_succ_top, (writeW_outside m B v h).wordsVal (by omega_arith) (by omega_arith), word_writeW_self]

theorem fios_wordsVal_append (m : Mem) (B : Addr) (d j k : Nat) :
    wordsVal m B d (j + k) = wordsVal m B d j + 2 ^ (64 * j) * wordsVal m B (d + 8 * j) k := by
  induction j generalizing d with
  | zero => simp only [wordsVal, Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.add_zero]
  | succ j ih =>
    rw [Nat.add_right_comm, wordsVal, ih, wordsVal, pow64_succ, show d + 8 + 8 * j = d + 8 * (j + 1) by omega_arith,
      Nat.mul_add, Nat.mul_assoc]
    omega_arith

/-- The sum of a loop's iterations, as the sum of the first ones and the last. -/
theorem fios_sum_group {W T S M W' C₀ C₁ C₂ a u G T' S' M' P Q : Nat}
    (e₁ : W + P * C₁ = T + a * S + u * M + C₀) (e₂ : G + Q * C₂ = T' + a * S' + u * M' + C₁)
    (hW : W' = W + P * G) :
    W' + P * Q * C₂ = T + P * T' + a * (S + P * S') + u * (M + P * M') + C₀ := by
  subst hW
  have e : P * G + P * Q * C₂ = P * (T' + a * S' + u * M' + C₁) := by
    rw [← e₂, Nat.mul_add, Nat.mul_assoc]
  grind

/-! ## The start and the end of a round -/

theorem fios_rem (n : Nat) : BitVec.ofNat 64 n <<< 62 >>> 62 = BitVec.ofNat 64 (n % 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  omega_arith

theorem fios_quot (n : Nat) (h : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 2 = BitVec.ofNat 64 (n / 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_arith

/-- Two words stored at `d + 8 j`, `d + 8 j + 8`, above `j` words at `d`. -/
theorem fios_wordsVal_write2 (m : Mem) (B : Addr) (d j : Nat) (v v' : BitVec 64) (h : d + 8 * j + 16 ≤ 2 ^ 64) :
    wordsVal ((m.writeW (off B (d + 8 * j)) v).writeW (off B (d + 8 * j + 8)) v') B d (j + 2) =
      wordsVal m B d j + 2 ^ (64 * j) * (v.toNat + 2 ^ 64 * v'.toNat) := by
  rw [show d + 8 * j + 8 = d + 8 * (j + 1) by omega_arith, fios_wordsVal_write_top _ _ _ _ _ (by omega_arith),
    fios_wordsVal_write_top _ _ _ _ _ (by omega_arith), Nat.mul_succ, Nat.pow_add]
  grind

/-- The sum of a round: `2⁶⁴ (W + P (c + t_w + d)) = T + aᵢ b + u m`, from that of
words `1` to `w - 1`, `W + P (c + d) = T' + aᵢ b' + u m' + C₀`, and of word 0,
`2⁶⁴ C₀ = t₀ + aᵢ b₀ + u m₀`. -/
theorem fios_round_sum {W T S M C₀ c d a u t0 b0 m0 tw x P : Nat}
    (e : W + P * (c + d) = T + a * S + u * M + C₀) (h0 : 2 ^ 64 * C₀ = t0 + a * b0 + u * m0)
    (hx : x = c + tw + d) :
    2 ^ 64 * (W + P * x) = t0 + 2 ^ 64 * (T + P * tw) + a * (b0 + 2 ^ 64 * S) + u * (m0 + 2 ^ 64 * M) := by
  subst hx
  grind

theorem fios_wordsVal_pred (m : Mem) (B : Addr) (d : Nat) {w : Nat} (hw : 1 ≤ w) :
    wordsVal m B d w = (word m B d).toNat + 2 ^ 64 * wordsVal m B (d + 8) (w - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega_arith⟩
  rfl

end VG.Proof.Bignum.PPC64LE
