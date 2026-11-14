module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Mont.PPC64LE
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# Montgomery arithmetic on PPC64LE: lemmas on the words of a number

Lists of instructions one after the other (`wp_append`), the words of a
number split at a word (`wordsVal_append`), and a stored word that leaves
the others (`word_writeW_ne`).
-/

@[expose] public section

namespace VG.Proof.Mont.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont.PPC64LE VG.Proof.Mont

theorem wp_append {l₁ l₂ : List Instr} {s : State} {Q : State → Prop}
    (h : WP isa (.block l₁) s (fun s₁ => WP isa (.block l₂) s₁ Q)) : WP isa (.block (l₁ ++ l₂)) s Q :=
  WP.block_append h

theorem wordsVal_append (m : Mem) (base : Addr) (d j k : Nat) :
    wordsVal m base d (j + k) = wordsVal m base d j + 2 ^ (64 * j) * wordsVal m base (d + 8 * j) k := by
  induction j generalizing d with
  | zero => simp only [wordsVal, Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.add_zero]
  | succ j ih =>
    rw [Nat.add_right_comm, wordsVal, ih, wordsVal, pow64_succ, show d + 8 + 8 * j = d + 8 * (j + 1) by omega_arith,
      Nat.mul_add, Nat.mul_assoc]
    omega_arith

/-- A word stored at `o` leaves the word at `d`, apart from it. -/
theorem word_writeW_ne {m : Mem} {base : Addr} {o d : Nat} (v : BitVec 64) (hsep : d + 8 ≤ o ∨ o + 8 ≤ d)
    (ho : o + 8 ≤ 2 ^ 64) (hd : d + 8 ≤ 2 ^ 64) : word (m.writeW (off base o) v) base d = word m base d :=
  (writeW_outside m base v ho).word (by omega_arith) hd

end VG.Proof.Mont.PPC64LE
