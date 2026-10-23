module

import VerifiedGarbage.Proof.Mont.PPC64LE.Loop
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Mont.PPC64LE
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words

/-!
# Montgomery arithmetic on PPC64LE: constants in the working space

`setConst n o x` stores the `2n` 32-bit words of `x` at `[r3 + o]`, each as
`lis`, `ori` and `stw` (`setConst_ok`): the number there is then `x`, for
`x < 2^(64 n)`.
-/

@[expose] public section

namespace VG.Proof.Mont.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Mont.PPC64LE VG.Proof.Mont

/-- `x mod 2^(32 k)` by its digits. -/
theorem val32_digits {m : Mem} {base : Addr} {o x : Nat} :
    ∀ {k : Nat}, (∀ j < k, w32 m base (o + 4 * j) = (x >>> (32 * j)) % 2 ^ 32) → val32 m base o k = x % 2 ^ (32 * k)
  | 0, _ => by simp [val32, Nat.mod_one]
  | k + 1, h => by
    rw [val32_succ, val32_digits fun j hj => h j (by omega), h k (by omega), Nat.shiftRight_eq_div_pow,
      show 32 * (k + 1) = 32 * k + 32 by omega, Nat.pow_add, Nat.mod_mul]

/-- The first `k` words of `setConst`. -/
def consts (o x k : Nat) : List Instr :=
  (List.range k).flatMap fun j =>
    movImm .r11 (BitVec.ofNat 32 (x >>> (32 * j))) ++ ([.store .w .r11 wb (o + 4 * j)] : List Instr)

theorem consts_succ (o x k : Nat) : consts o x (k + 1) = consts o x k ++
    (movImm .r11 (BitVec.ofNat 32 (x >>> (32 * k))) ++ ([.store .w .r11 wb (o + 4 * k)] : List Instr)) := by
  simp only [consts, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem consts_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {o x : Nat}
    (h3 : At s base .r3 0) : ∀ {k : Nat}, o + 4 * k ≤ size →
    WP isa (.block (consts o x k)) s fun u =>
      Outside base o (4 * k) s.mem u.mem ∧ (∀ j < k, w32 u.mem base (o + 4 * j) = (x >>> (32 * j)) % 2 ^ 32) ∧
      Kp [.r11] s u
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _), Kp.refl _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [consts_succ]
    refine wp_append (WP.mono (consts_ok hs h3 (k := k) (by omega)) fun s₁ ⟨O₁, Z₁, K₁⟩ => ?_)
    refine wp_movImm fun v hv => ?_
    refine wp_step (stw0_ok ((K₁.ws hs).write _ _) ((K₁.at h3).write _) (by decide) (d := o + 4 * k) (by omega))
      (WP.block_nil ?_)
    simp only [write_gpr, ite_true, write_mem]
    have W := writeW32_outside s₁.mem base (d := o + 4 * k) (BitVec.ofNat 32 v.toNat) (by omega)
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (W.mono (by omega) (by omega)), fun j hj => ?_,
      (K₁.trans (Kp.write _ _ (by decide))).trans (Kp.store _ _ _)⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [w32_write_ne hn (by omega) (by omega) (by omega)]; exact Z₁ j hj
    · rw [w32_write_self, BitVec.toNat_ofNat, hv, BitVec.toNat_ofNat]

/-- `[r3 + o] = x`, `n` words, for `x < 2^(64 n)`. -/
theorem setConst_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {n o x : Nat}
    (h3 : At s base .r3 0) (ho : o + 8 * n ≤ size) (hx : x < 2 ^ (64 * n)) :
    WP isa (.block (setConst n o x)) s fun u =>
      Outside base o (8 * n) s.mem u.mem ∧ val32 u.mem base o (2 * n) = x ∧ Kp [.r11] s u := by
  refine WP.mono (consts_ok hs h3 (o := o) (x := x) (k := 2 * n) (by omega)) fun u ⟨O, Z, K⟩ =>
    ⟨O.mono (Nat.le_refl _) (by omega), ?_, K⟩
  rw [val32_digits Z, show 32 * (2 * n) = 64 * n by omega, Nat.mod_eq_of_lt hx]

end VG.Proof.Mont.PPC64LE
