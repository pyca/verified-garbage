module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Copy
public import VerifiedGarbage.Impl.Ecdh.RISCV64.Shr
import VerifiedGarbage.Proof.Weierstrass.BytesLen
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# A number shifted right in place on RISC-V

`shrWords n o sh` (`Impl/Ecdh/RISCV64/Shr.lean`) shifts the `n`-word
number at `[o]` of the working space right by `0 < sh < 64` bits
(`shrWords_ok`), a word at a time from the lowest (`shrStep_ok`): each word
shifted right, or'd with the next one shifted left by `64 - sh`, which is
its low `sh` bits rotated to the top (`shl_eq_rotr`), as
`wordsVal_shr` (`Proof/Weierstrass/BytesLen.lean`) has the shifted number.
As on PPC64LE (`Proof/Weierstrass/PPC64LE/BytesLen.lean`).
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Proof.Mont
open VG.Proof.Weierstrass.RISCV64
open VG.Proof.X25519.RISCV64 (Rest)

/-- Word `j` of `[o]` shifted right by `sh`, from the words of `m`. -/
def shrWord (m : Mem) (base : Addr) (n o sh j : Nat) : BitVec 64 :=
  if j + 1 < n then (word m base (o + 8 * j) >>> sh) |||
    (word m base (o + 8 * (j + 1)) &&& BitVec.ofNat 64 (2 ^ sh - 1)).rotateRight sh
  else word m base (o + 8 * j) >>> sh

/-- The low `sh` bits of a word rotated to the top are it shifted left by
`64 - sh`. -/
theorem shl_eq_rotr (w : BitVec 64) {sh : Nat} (h0 : 0 < sh) (h64 : sh < 64) :
    w <<< (64 - sh) = (w &&& BitVec.ofNat 64 (2 ^ sh - 1)).rotateRight sh := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_rotateRight, BitVec.getLsbD_and,
    BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, Nat.mod_eq_of_lt h64, hi, decide_true, Bool.true_and]
  by_cases h : i < 64 - sh
  · simp only [h, decide_true, Bool.not_true, Bool.false_and, ite_true]
    simp only [show ¬ sh + i < sh by omega_arith, decide_false, Bool.and_false]
  · simp only [h, decide_false, Bool.not_false, Bool.true_and, ite_false]
    rw [show i - (64 - sh) = i - (64 - sh) from rfl]
    simp only [show i - (64 - sh) < sh by omega_arith, decide_true, Bool.and_true,
      show i - (64 - sh) < 64 by omega_arith]

/-- Word `k` of `shrWords`, from words `k` and `k + 1` of `m`. -/
theorem shrStep_ok {s : State} {base : Addr} (hw : WsReg s base) {n o sh k : Nat} (ho : o + 8 * n ≤ 4096)
    (ho8 : o % 8 = 0) (hsh : 1 ≤ sh) (hsh' : sh < 64) (hk : k < n) {m : Mem}
    (hm : ∀ j, k ≤ j → j < n → word s.mem base (o + 8 * j) = word m base (o + 8 * j)) :
    WP isa (.block (shrStep n o sh k)) s fun s' =>
      s'.mem = s.mem.writeW (off base (o + 8 * k)) (shrWord m base n o sh k) ∧ Rest [.t0, .t1] s s' := by
  rw [shrStep, List.append_assoc, List.append_assoc, List.singleton_append]
  refine ldAt_ws hw (d := o + 8 * k) (by omega_arith) (by omega_arith) fun s₁ u₁ => ?_
  refine wp_srl hsh' fun s₂ u₂ => ?_
  have K₂ : Rest [.t0, .t1] s s₂ := (u₁.rest (by decide)).trans (u₂.rest (by decide))
  by_cases hc : k + 1 < n
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine ldAt_ws (hw.of_rest K₂) (d := o + 8 * (k + 1)) (by omega_arith) (by omega_arith) fun s₃ u₃ => ?_
    refine wp_sll (by omega_arith : 64 - sh < 64) fun s₄ u₄ => wp_or fun s₅ u₅ => ?_
    have K₅ : Rest [.t0, .t1] s s₅ :=
      K₂.trans ((u₃.rest (by decide)).trans ((u₄.rest (by decide)).trans (u₅.rest (by decide))))
    rw [← List.append_nil (sdAt .t0 wb (o + 8 * k))]
    refine sdAt_ws (hw.of_rest K₅) (by decide) (by omega_arith) (by omega_arith) fun s₆ u₆ =>
      WP.block_nil ⟨?_, K₅.trans (u₆.rest _)⟩
    have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂, u₅.gpr, u₄.other .t0 (by decide), u₄.gpr, u₃.other .t0 (by decide),
      u₃.gpr, u₂.gpr, u₁.gpr, m₂, shrWord, ite_eq_left_of_eq_true _ _ (eq_true hc), hm k (Nat.le_refl _) hk, hm (k + 1) (by omega_arith) hc,
      shl_eq_rotr _ (by omega_arith) hsh']
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc), List.nil_append, ← List.append_nil (sdAt .t0 wb (o + 8 * k))]
    refine sdAt_ws (hw.of_rest K₂) (by decide) (by omega_arith) (by omega_arith) fun s₃ u₃ =>
      WP.block_nil ⟨?_, K₂.trans (u₃.rest _)⟩
    rw [u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr, shrWord, ite_eq_right_of_eq_false _ _ (eq_false hc), hm k (Nat.le_refl _) hk]

theorem shrSteps_ok {s : State} {base : Addr} (hw : WsReg s base) {n o sh : Nat} (ho : o + 8 * n ≤ 4096)
    (ho8 : o % 8 = 0) (hsh : 1 ≤ sh) (hsh' : sh < 64) : ∀ k, k ≤ n →
    WP isa (.block ((List.range k).flatMap (shrStep n o sh))) s fun s' =>
      (∀ j < k, word s'.mem base (o + 8 * j) = shrWord s.mem base n o sh j) ∧
      Rest [.t0, .t1] s s' ∧ Outside base o (8 * k) s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Rest.refl _ _, Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hw.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (shrSteps_ok hw ho ho8 hsh hsh' k (by omega_arith)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
    refine WP.mono (shrStep_ok (hw.of_rest k₁) ho ho8 hsh hsh' (k := k) (by omega_arith) (m := s.mem)
      fun j hj _ => O₁.word (by omega_arith) (by omega_arith)) fun s₂ ⟨m₂, k₂⟩ => ?_
    have O₂ : Outside base (o + 8 * k) 8 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega_arith)
    refine ⟨fun j hj => ?_, k₁.trans k₂,
      (O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.word (by omega_arith) (by omega_arith), e₁ j h]
    · obtain rfl : j = k := by omega_arith
      rw [m₂, word_writeW_self]

/-- `[o] = [o] >> sh`, `n` words, for `0 < sh < 64`. -/
theorem shrWords_ok {s : State} {base : Addr} (hw : WsReg s base) {n o sh : Nat} (ho : o + 8 * n ≤ 4096)
    (ho8 : o % 8 = 0) (hsh : 1 ≤ sh) (hsh' : sh < 64) :
    WP isa (.block (shrWords n o sh)) s fun s' =>
      wordsVal s'.mem base o n = wordsVal s.mem base o n >>> sh ∧
      Rest [.t0, .t1] s s' ∧ Outside base o (8 * n) s.mem s'.mem :=
  WP.mono (shrSteps_ok hw ho ho8 hsh hsh' n (Nat.le_refl _)) fun s' ⟨e, k, O⟩ =>
    ⟨VG.Proof.Weierstrass.wordsVal_shr _ _ _ _ _ _ (by omega_arith) hsh' fun j hj => e j hj, k, O⟩

end VG.Proof.Ecdh.RISCV64
