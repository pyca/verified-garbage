import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-!
# A candidate on AArch64: the table of small primes

`tabStore i` builds word `i` of the table by `movz` and three `movk`
(`movk_word`) and stores it (`tabStore_ok`); `tabWrite`, 256 of them,
writes the table (`tabWrites_ok`), composed by induction rather than run
in one block.
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- `movz` and three `movk` of the 16-bit pieces of `W` build `W`. -/
theorem movk_word (W : Nat) :
    ((BitVec.setWidth 64 (BitVec.ofNat 16 W) <<< (16 * 0) &&& ~~~((65535 : BitVec 64) <<< (16 * 1)) |||
              BitVec.setWidth 64 (BitVec.ofNat 16 (W / 2 ^ 16)) <<< (16 * 1)) &&&
            ~~~((65535 : BitVec 64) <<< (16 * 2)) |||
          BitVec.setWidth 64 (BitVec.ofNat 16 (W / 2 ^ 32)) <<< (16 * 2)) &&&
        ~~~((65535 : BitVec 64) <<< (16 * 3)) |||
      BitVec.setWidth 64 (BitVec.ofNat 16 (W / 2 ^ 48)) <<< (16 * 3) =
    BitVec.ofNat 64 W := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have e : ∀ m : Nat, m < 64 → (65535 : BitVec 64).getLsbD m = decide (m < 16) := by decide
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, Nat.testBit_div_two_pow, hk, decide_true, Bool.true_and]
  rw [e (k - 16 * 1) (by omega), e (k - 16 * 2) (by omega), e (k - 16 * 3) (by omega)]
  simp only [Nat.reduceMul, Nat.sub_zero]
  rcases (show k < 16 ∨ (16 ≤ k ∧ k < 32) ∨ (32 ≤ k ∧ k < 48) ∨ 48 ≤ k by omega) with h | h | h | h <;>
    simp (disch := omega) only [decide_eq_true, decide_eq_false, Nat.sub_add_cancel, Bool.not_true,
      Bool.not_false, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.or_false,
      Bool.false_or]

/-- `tabStore n`: word `n` of the table to `[x9 + 8 n]`. -/
theorem tabStore_ok {t : State} {B : Addr} {Z T n : Nat} (hs : Scr t B Z) (h9 : t.gpr .x9 = off B T)
    (hT : T + 8 * n + 8 ≤ Z) (hn : n < 256) :
    WP isa (.block (tabStore n)) t fun t' =>
      t'.mem = t.mem.writeW (off B (T + 8 * n)) (BitVec.ofNat 64 (tabWord n)) ∧ Keep [.x3] t t' := by
  have hst : InRegions t.wr (off B (T + 8 * n)) 8 := hs.st hT
  have ho : 8 * n % 8 = 0 ∧ 8 * n < 32768 := ⟨Nat.mul_mod_right _ _, by omega⟩
  unfold tabStore
  -- Kept opaque: `simp` would otherwise evaluate the table word.
  generalize tabWord n = W
  refine WP.keep [.x3] ?_ rfl rfl rfl
  brun [exec_movz_x' (show 0 < 4 by decide), exec_movk_x (show 1 < 4 by decide), exec_movk_x (show 2 < 4 by decide),
    exec_movk_x (show 3 < 4 by decide), h9, ho, hst, movk_word]

/-- The first `n` words of the table at `T` (in `x9`). -/
theorem tabWrites_ok {s : State} {B : Addr} {Z T : Nat} (hs : Scr s B Z) (hT : T + 2048 ≤ Z)
    (h9 : s.gpr .x9 = off B T) : ∀ n ≤ 256,
    WP isa (.block ((List.range n).flatMap tabStore)) s fun t =>
      (∀ i < n, word t.mem B (T + 8 * i) = BitVec.ofNat 64 (tabWord i)) ∧ Outside B T (8 * n) s.mem t.mem ∧
      Keep [.x3] s t
  | 0, _ => WP.block_nil ⟨fun i hi => absurd hi (by omega), Outside.refl _ _ _ _, Keep.refl _ _⟩
  | n + 1, hn => by
    have hb := hs.nowrap
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (tabWrites_ok hs hT h9 n (by omega)) fun t ⟨hv, ho, k⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (tabStore_ok (hs.congr k.wr) ((k.gpr .x9 (by decide)).trans h9) (by omega) (by omega))
      fun t' ⟨hm, k'⟩ => ⟨fun i hi => ?_, ?_, (k.trans k').mono (by decide)⟩
    · rw [hm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [(writeW_outside t.mem B _ (by omega)).word (by omega) (by omega)]; exact hv i hi
      · exact word_writeW_self _ _ _ _
    · rw [hm]
      intro x hx
      rw [writeW_outside t.mem B _ (by omega) x (by omega)]
      exact ho x (by omega)

end VG.Proof.RsaKeyGen.AArch64
