module
public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Candidate
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-!
# A candidate on AArch64: the table of small primes

`tabStore i` builds word `i` of the table by `movz` and three `movk`
(`movk_word`) and stores it (`tabStore_ok`); `tabWrite`, 256 of them,
writes the table (`tabWrites_ok`), composed by induction rather than run
in one block.
-/

@[expose] public section

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
  rw [e (k - 16 * 1) (by omega_using [hk]), e (k - 16 * 2) (by omega_using [hk]), e (k - 16 * 3) (by omega_using [hk])]
  simp only [Nat.reduceMul, Nat.sub_zero]
  rcases (show k < 16 ∨ (16 ≤ k ∧ k < 32) ∨ (32 ≤ k ∧ k < 48) ∨ 48 ≤ k by omega_using []) with h | h | h | h <;>
    simp (disch := omega_arith) only [decide_eq_true, decide_eq_false, Nat.sub_add_cancel, Bool.not_true,
      Bool.not_false, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.or_false,
      Bool.false_or]

/-- `tabStore n`: word `n` of the table to `[x9 + 8 n]`. -/
theorem tabStore_ok {t : State} {B : Addr} {Z T n : Nat} (hs : Scr t B Z) (h9 : t.gpr .x9 = off B T)
    (hT : T + 8 * n + 8 ≤ Z) (hn : n < 256) :
    WP isa (.block (tabStore n)) t fun t' =>
      t'.mem = t.mem.writeW (off B (T + 8 * n)) (BitVec.ofNat 64 (tabWord n)) ∧ Keep [.x3] t t' := by
  have hst : InRegions t.wr (off B (T + 8 * n)) 8 := hs.st hT
  have ho : 8 * n % 8 = 0 ∧ 8 * n < 32768 := ⟨Nat.mul_mod_right _ _, by omega_using [hn]⟩
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
  | 0, _ => WP.block_nil ⟨fun i hi => absurd hi (by omega_using []), Outside.refl _ _ _ _, Keep.refl _ _⟩
  | n + 1, hn => by
    have hb := hs.nowrap
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (tabWrites_ok hs hT h9 n (by omega_using [hn])) fun t ⟨hv, ho, k⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (tabStore_ok (hs.congr k.wr) ((k.gpr .x9 (by decide)).trans h9) (by omega_using [hT, hn]) (by omega_using [hn]))
      fun t' ⟨hm, k'⟩ => ⟨fun i hi => ?_, ?_, (k.trans k').mono (by decide)⟩
    · rw [hm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [(writeW_outside t.mem B _ (by omega_using [hT, hn, hb])).word (by omega_arith) (by omega_arith)]; exact hv i hi
      · exact word_writeW_self _ _ _ _
    · rw [hm]
      intro x hx
      rw [writeW_outside t.mem B _ (by omega_using [hT, hn, hb]) x (by omega_using [hx])]
      exact ho x (by omega_using [hx])

/-- Calling the same table writer. The return address is restored; the
additional scratch registers are already scratch in every caller. -/
theorem tabWriteShared_ok {s : State} {B : Addr} {Z T : Nat} (hs : Scr s B Z) (hT : T + 2048 ≤ Z)
    (h9 : s.gpr .x9 = off B T) :
    WP isa tabWriteShared s fun t =>
      (∀ i < 256, word t.mem B (T + 8 * i) = BitVec.ofNat 64 (tabWord i)) ∧ Outside B T 2048 s.mem t.mem ∧
      Keep [.x3, .x4, .x16, .x17] s t := by
  unfold tabWriteShared
  refine WP.seq (WP.mono (WP.keep [.x4] (s := s)
    (Q := fun a => a.gpr .x4 = s.gpr .x30 ∧ a.mem = s.mem) (by brun []) rfl rfl rfl)
    fun a ⟨⟨ha, hm⟩, ka⟩ => ?_)
  have ke : Keep linkRegs a a.callEntry :=
    ⟨fun r hr => State.callEntry_gpr a hr, rfl, rfl, rfl, fun _ _ => rfl⟩
  obtain ⟨tr, b, eb, htab, ho, kb⟩ := tabWrites_ok (hs.congr (ke.wr.trans ka.wr)) hT
    ((ke.gpr .x9 (by decide)).trans ((ka.gpr .x9 (by decide)).trans h9)) 256 (Nat.le_refl _)
  have ret : isa.ret a.callEntry b = some b := by
    simp only [isa, VG.AArch64.ret, kb.gpr .x30 (by decide), ite_true]
  refine WP.seq (show WP isa (.call "vg_prime_table_write" (.block tabWrite)) a _ from
    ⟨_, b, Exec.call (call_callEntry a) eb ret, ?_⟩)
  refine WP.mono (WP.keep [.x30] (s := b)
    (Q := fun t => t.gpr .x30 = b.gpr .x4 ∧ t.mem = b.mem) (by brun []) rfl rfl rfl)
    fun t ⟨⟨ht, hmt⟩, kt⟩ => ?_
  have k := ((ka.trans ke).trans kb).trans kt
  refine ⟨fun i hi => by rw [hmt]; exact htab i hi, ?_, ⟨fun r hr => ?_, k.rd, k.wr, k.sp, k.vcs⟩⟩
  · rw [hmt]
    simpa only [State.callEntry_mem, hm] using ho
  · by_cases heq : r = .x30
    · subst r
      rw [ht, kb.gpr .x4 (by decide), ke.gpr .x4 (by decide), ha]
    · have links : ∀ r, r ∉ ([.x3, .x4, .x16, .x17] : List Reg) → r ≠ .x30 → r ∉ linkRegs := by
        intro r; cases r <;> decide
      rw [kt.gpr r (by simpa using heq), kb.gpr r (by simp_all), ke.gpr r (links r hr heq), ka.gpr r (by simp_all)]

end VG.Proof.RsaKeyGen.AArch64
