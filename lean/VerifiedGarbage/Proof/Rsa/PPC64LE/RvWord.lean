module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCandSet
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvBit
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvMont
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvTop
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyHalf
import VerifiedGarbage.Proof.Rsa.RecoverFusedWords
import VerifiedGarbage.Proof.Framework.Block

/-!
# `vg_rsa_recover_primes` on PPC64LE: the digits of `m`

`wordHead_ok`: the digit `r27 - 1` of `m` into `sWord`; `bits_ok`: its 32
bits, most significant first; `digits_ok`: all `⌈c / 32⌉` digits, the pass
`Fused.eval` over `m`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Impl.Rsa.PPC64LE.Recover (bit wordHead nArr wM sWord)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- The digit `k` of a number. -/
theorem w32_digit {m : Mem} {B : Addr} {d n k : Nat} (hk : k < n) :
    w32 m B (d + 4 * k) = val32 m B d n / 2 ^ (32 * k) % 2 ^ 32 := by
  obtain ⟨r, rfl⟩ : ∃ r, n = k + (r + 1) := ⟨n - k - 1, by omega_arith⟩
  have lo := val32_lt m B d k
  have hw := (m.readW (off B (d + 4 * k)) 32).isLt
  rw [val32_append, val32, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt lo, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw]

/-- `wordHead`: the digit `D - i - 1` of `m` into `sWord`, and 32 bits to go. -/
theorem wordHead_ok {s0 u : State} (c : CF s0 u) (hp : Par s0) {i : Nat} (hi : i < dD s0)
    (h27 : u.gpr .r27 = BitVec.ofNat 64 (dD s0 - i)) :
    WP isa (.block wordHead) u fun v => KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [] [sWord] u.mem v.mem ∧
      slot v.mem (rvB s0) sWord = mV s0 / 2 ^ (32 * (dD s0 - i - 1)) % 2 ^ 32 ∧
      v.gpr .r28 = BitVec.ofNat 64 32 ∧ Keep [.r0, .r5, .r28] u v := by
  have w := c.ws
  have hz : 160 ≤ rvZ s0 := w.hdr_le
  have hW : wW (kK s0) = 2 * ww (kK s0) + 2 := rfl
  have e1 := arrW3 (ww (kK s0)); have e2 := arrW3_end (ww (kK s0))
  have f8 := w.arr_fit (j := 8) (by decide)
  have nw := w.nowrap
  have hD := hp.dW
  let d := arr (ww (kK s0)) (2 * wM) + 4 * (dD s0 - i - 1)
  have hd : d + 4 ≤ rvZ s0 := by
    have : arr (ww (kK s0)) (2 * wM) = arr (ww (kK s0)) 6 := rfl
    simp only [d, this]; omega_arith
  rw [wordHead]
  refine ptr_ok w (r := .r5) (by decide) (by decide) (by decide) (show 2 * wM < 2 ^ 15 by decide) ?_
  have ea : off (rvB s0) (arr (ww (kK s0)) (2 * wM) + 4 * (dD s0 - i)) - 4#64 = off (rvB s0) d := by
    rw [off_sub _ (by omega_arith)]; congr 1; omega_arith
  refine WP.mono (WP.keep [.r0, .r5, .r28] (Q := fun x =>
    x.mem = u.mem.writeW (off (rvB s0) sWord) (((u.mem.readW (off (rvB s0) d) 32).setWidth 64).setWidth 32) ∧
    x.gpr .r28 = BitVec.ofNat 64 32) ?_ (by decide)) fun v ⟨⟨m, a28⟩, kv⟩ => ⟨?_, ?_, a28, ?_⟩
  · prun [h27, shl2_ofNat, off_add, ea, w.r31, exec_load_w (show Reg.r5 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
      w.scr.ld (d := d) (n := 4) hd, BitVec.add_zero,
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sWord < 2 ^ 15 by decide),
      w.scr.st (show sWord + 4 ≤ rvZ s0 by simp only [sWord]; omega_arith)]
  · rw [m]; exact keep_slot _ _ (by simp) (by decide)
  · rw [m, slot_write_self, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
    have := c.vM
    change val32 u.mem (rvB s0) (arr (wW (kK s0)) 3) (wW (kK s0)) = _ at this
    rw [hW, e1, ← hW] at this
    rw [← this]
    exact w32_digit (by omega_arith)
  · exact ((Keep.write _ _ _).trans kv).mono (by decide)

/-- The 32 bits of a digit. -/
theorem bits_ok {s0 u : State} (hn : NOk s0) {j : Nat} (hj : j < 100) {st : Fused.State} {dg : Nat}
    (hdg : dg < 2 ^ 32) (h : BI s0 j st u) (hw : slot u.mem (rvB s0) sWord = dg)
    (h28 : u.gpr .r28 = BitVec.ofNat 64 32) :
    WP isa (.loop bit (.nonzero .d .r28)) u fun t =>
      BI s0 j (Fused.bits (nV s0) (j + 2) 32 dg st) t ∧ t.gpr .r27 = u.gpr .r27 := by
  refine WP.mono (wp_countdown (body := bit) (cnt := .r28) (N := 32) (by decide) (by decide)
    (fun k s => BI s0 j (Fused.bits (nV s0) (j + 2) k (dg / 2 ^ (32 - k)) st) s ∧
      slot s.mem (rvB s0) sWord = Fused.wordReg dg k ∧ s.gpr .r27 = u.gpr .r27)
    (fun k hk s ⟨b, sw, s27⟩ _ => WP.mono (bit_ok hn hj b sw) fun t ⟨bt, wt, t28, t27⟩ =>
      ⟨⟨?_, (by rw [wt, Fused.wordReg_succ]), (by rw [t27, s27])⟩, t28⟩)
    ⟨(by simpa [Fused.bits] using h), (by rw [hw, Fused.wordReg, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hdg]),
      rfl⟩ h28) fun t ⟨bt, _, t27⟩ => ⟨(by simpa using bt), t27⟩
  rw [show 32 - (k + 1) = 31 - k by omega_arith, Fused.bits_word hk]
  exact bt

/-- A digit. -/
theorem word_ok {s0 u : State} (hn : NOk s0) (hp : Par s0) {j : Nat} (hj : j < 100) {i : Nat}
    (hi : i < dD s0) (h : BI s0 j (Fused.eval (nV s0) (j + 2) (mV s0 / 2 ^ (32 * (dD s0 - i)))) u)
    (h27 : u.gpr .r27 = BitVec.ofNat 64 (dD s0 - i)) :
    WP isa VG.Impl.Rsa.PPC64LE.Recover.word u fun t => BI s0 j (Fused.eval (nV s0) (j + 2) (mV s0 / 2 ^ (32 * (dD s0 - (i + 1))))) t ∧
      t.gpr .r27 = u.gpr .r27 - BitVec.ofNat 64 1 := by
  have hn1 : 1 < nV s0 := by have := hn.big; omega_arith
  unfold VG.Impl.Rsa.PPC64LE.Recover.word
  refine WP.seq (WP.mono (wordHead_ok h.cf hp hi h27) fun u1 ⟨kk1, w1, a28, k1⟩ => ?_)
  have b1 := h.of_keep kk1 (by simp) (by decide) (by simp) (by decide) k1 (h.cf.ws.of_keep k1)
  refine WP.seq (WP.mono (bits_ok hn hj (Nat.mod_lt _ (by decide)) b1 w1 a28) fun u2 ⟨b2, r2⟩ => ?_)
  refine WP.mono (WP.keep [.r27] (Q := fun x => x.gpr .r27 = u2.gpr .r27 - BitVec.ofNat 64 1 ∧ x.mem = u2.mem)
    (by prun) (by decide)) fun t ⟨⟨a27, mt⟩, kt⟩ => ⟨?_, ?_⟩
  · have bt := b2.of_keep (show KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [] [] u2.mem t.mem by
      rw [mt]; exact KeyWorkspace.Keep.refl _ _ _ _ _) (by simp) (by simp) (by simp) (by simp) kt
      (b2.cf.ws.of_keep kt)
    rw [Fused.word_eval _ _ _ _ hn1 (Nat.mod_lt _ (by decide))] at bt
    have e : mV s0 / 2 ^ (32 * (dD s0 - i)) * 2 ^ 32 + mV s0 / 2 ^ (32 * (dD s0 - i - 1)) % 2 ^ 32 =
        mV s0 / 2 ^ (32 * (dD s0 - (i + 1))) := by
      rw [show dD s0 - (i + 1) = dD s0 - i - 1 by omega_arith,
        show 32 * (dD s0 - i) = 32 * (dD s0 - i - 1) + 32 by omega_arith, Nat.pow_add, ← Nat.div_div_eq_div_mul]
      exact Nat.div_add_mod' _ _
    rw [e] at bt
    exact bt
  · rw [a27, r2, k1.gpr _ (by decide)]

/-- The digits of `m`: the pass over all of it. -/
theorem digits_ok {s0 u : State} (hn : NOk s0) (hp : Par s0) {j : Nat} (hj : j < 100)
    (h : BI s0 j (Fused.eval (nV s0) (j + 2) 0) u) (h27 : u.gpr .r27 = BitVec.ofNat 64 (dD s0)) :
    WP isa (.loop VG.Impl.Rsa.PPC64LE.Recover.word (.nonzero .d .r27)) u (BI s0 j (Fused.eval (nV s0) (j + 2) (mV s0))) := by
  have c32 : cB s0 ≤ 32 * dD s0 := by simp only [dD]; omega_arith
  have d0 : 0 < dD s0 := by have := hp.c0; simp only [dD]; omega_arith
  have m0 : mV s0 / 2 ^ (32 * dD s0) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hp.mc (Nat.pow_le_pow_right (by decide) c32))
  refine WP.mono (wp_countdown (body := VG.Impl.Rsa.PPC64LE.Recover.word) (cnt := .r27) (N := dD s0)
    (by have := hp.c31; simp only [dD]; omega_arith) d0
    (fun i s => BI s0 j (Fused.eval (nV s0) (j + 2) (mV s0 / 2 ^ (32 * (dD s0 - i)))) s)
    (fun i hi s b c => word_ok hn hp hj hi b c) (by rw [Nat.sub_zero, m0]; exact h) h27) fun t b => ?_
  rwa [Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at b

end VG.Proof.Rsa.PPC64LE.Recover
