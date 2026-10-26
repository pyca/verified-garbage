module

import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
public import VerifiedGarbage.Proof.Rsa.KeyMath
import VerifiedGarbage.Proof.Rsa.X86.DivCount
import VerifiedGarbage.Proof.Framework.Omega
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops

/-! # A step of the key workspace's division at a run-time width

`divStep_ok`: `KeyRt.divStep` is `Rsa.divStep` on the remainder `[r]`
(`w + 1` words, `wide`) and the quotient `[q]`: both shifted up by a bit, the
quotient's top bit into the remainder (through the header word `sCy`), the
divisor subtracted into `[t]` and kept where it did not borrow, and that bit
into the quotient (through `sQb`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S slot arr_disj)

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- An array's `w + 1` words. -/
abbrev wide (m : Mem) (B : Addr) (w j : Nat) : Nat := val32 m B (arr w j) (w + 1)

theorem wide_eq (m : Mem) (B : Addr) (w j : Nat) :
    wide m B w j = num m B w j + 2 ^ (32 * w) * w32 m B (arr w j + 4 * w) := val32_succ _ _ _ _

/-- An array outside a frame keeps its `w + 1` words. -/
theorem keep_wide {w : Nat} {js ds : List Nat} {m m' : Mem} (F : Keep B w js ds m m') {j : Nat}
    (hj : ∀ k ∈ js, k ≠ j) (hd : ∀ d ∈ ds, d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) (fit : arr w j + S w ≤ 2 ^ 64) :
    wide m' B w j = wide m B w j := by
  rw [wide_eq, wide_eq, F.num hj hd fit, F.word (i := w) (by simp only [S]; omega) hj hd fit]

/-- A header word outside a frame of arrays. -/
theorem keep_slot {w : Nat} {js : List Nat} {m m' : Mem} (F : Keep B w js [] m m') {e : Nat}
    (he : e + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) : slot m' B e = slot m B e :=
  F.slot he (by simp)

theorem divStep_ok {s : State} (h : RtWs L s B Z len N) {q r d t : Nat} (hq : q < N) (hr : r < N) (hd : d < N)
    (ht : t < N) (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t)
    (top : w32 s.mem B (arr (kw len) d + 4 * kw len) = 0) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.divStep L q r d t) s fun u => RtWs L u B Z len N ∧
      Keep B (kw len) [q, r, t] [sCy, sQb] s.mem u.mem ∧
      u.gpr .esi = s.gpr .esi - 1 ∧ u.zf = some (s.gpr .esi - 1 == 0) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u ∧
      (wide s.mem B (kw len) r < num s.mem B (kw len) d → (wide u.mem B (kw len) r, num u.mem B (kw len) q) =
        VG.Proof.Rsa.divStep (num s.mem B (kw len) d) (32 * kw len)
          (wide s.mem B (kw len) r, num s.mem B (kw len) q)) := by
  have wpos := h.kw_pos
  have nw := h.ws.workspace.nowrap
  have fq := h.ws.fit64 hq
  have fr := h.ws.fit64 hr
  have fd := h.ws.fit64 hd
  have ft := h.ws.fit64 ht
  have hCy : sCy + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr := by decide
  have hQb : sQb + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr := by decide
  have hdr0 : ∀ e ∈ ([] : List Nat), e + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr := by simp
  have hdrCy : ∀ e ∈ [sCy], e + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr := by simp; decide
  have hdrQb : ∀ e ∈ [sQb], e + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr := by simp; decide
  -- The powers of two.
  have P2 : 2 ^ (32 * kw len) = 2 * 2 ^ (32 * kw len - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega_arith
  have PX : 2 ^ (32 * (kw len + 1)) = 2 ^ (32 * kw len) * 2 ^ 32 := by
    rw [← Nat.pow_add]; congr 1
  have PX2 : 2 * 2 ^ (32 * kw len) ≤ 2 ^ (32 * (kw len + 1)) := by
    rw [PX]; omega_arith
  -- The divisor and the inputs.
  have Dlt : num s.mem B (kw len) d < 2 ^ (32 * kw len) := val32_lt s.mem B (arr (kw len) d) (kw len)
  have Qlt : num s.mem B (kw len) q < 2 ^ (32 * kw len) := val32_lt s.mem B (arr (kw len) q) (kw len)
  have wd : wide s.mem B (kw len) d = num s.mem B (kw len) d := by
    rw [wide_eq, top, Nat.mul_zero, Nat.add_zero]
  unfold VG.Impl.Rsa.X86.KeyRt.divStep
  -- The quotient shifted up, its top bit `c`.
  refine WP.seq (WP.mono (chainAdd_ok h hq hq hq false) fun u1 ⟨h1, k1, ⟨c, ec, v1⟩, r1⟩ => ?_)
  have v1' : num u1.mem B (kw len) q + 2 ^ (32 * kw len) * c.toNat =
      num s.mem B (kw len) q + num s.mem B (kw len) q := v1
  refine WP.seq (wp_movS rfl fun u2a U2a _ => wp_logicS (.inl rfl) rfl fun u2b U2b => ?_)
  have h2b := h1.keep (U2a.keeps.trans U2b.keeps) (by decide) (by decide)
    (by rw [U2b.mem, U2a.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (storeSlot_ok h2b hCy .eax) fun u2 ⟨h2, k2, s2, r2⟩ => ?_
  rw [U2b.mem, U2a.mem] at k2
  have cy2 : slot u2.mem B sCy = c.toNat := by
    rw [s2, U2b.gpr, ite_eq_left rfl, U2a.gpr, ec]; cases c <;> rfl
  -- The remainder shifted up.
  have wr2 : wide u2.mem B (kw len) r = wide s.mem B (kw len) r := by
    rw [keep_wide k2 (by simp) (by simpa using hCy) fr, (keep_wide k1 (by simpa using hqr) hdr0 fr)]
  refine WP.seq (WP.mono (chainAdd_ok h2 hr hr hr true) fun u3 ⟨h3, k3, ⟨c', _, v3⟩, r3⟩ => ?_)
  have v3' : wide u3.mem B (kw len) r + 2 ^ (32 * (kw len + 1)) * c'.toNat =
      wide u2.mem B (kw len) r + wide u2.mem B (kw len) r := v3
  rw [wr2] at v3'
  have cy3 : slot u3.mem B sCy = c.toNat := by rw [keep_slot k3 hCy, cy2]
  refine WP.seq (WP.mono (addLow_ok h3 hr hCy) fun u4 ⟨h4, k4, v4, r4, top4⟩ => ?_)
  -- The difference with the divisor, its borrow `b`.
  have wd4 : wide u4.mem B (kw len) d = num s.mem B (kw len) d := by
    rw [keep_wide k4 (by simpa using hrd) hdr0 fd, keep_wide k3 (by simpa using hrd) hdr0 fd,
      keep_wide k2 (by simp) (by simpa using hCy) fd, keep_wide k1 (by simpa using hqd) hdr0 fd, wd]
  refine WP.seq (WP.mono (chainSub_ok h4 ht hr hd true) fun u5 ⟨h5, k5, ⟨b, eb, v5⟩, r5⟩ => ?_)
  have v5' : wide u5.mem B (kw len) t + wide u4.mem B (kw len) d =
      wide u4.mem B (kw len) r + 2 ^ (32 * (kw len + 1)) * b.toNat := v5
  rw [wd4] at v5'
  -- The bit kept, and the mask selecting the difference.
  refine WP.seq (wp_movS rfl fun a A _ => wp_logicS (.inr rfl) rfl fun a' A' => wp_logicS (.inl rfl) rfl
    fun a'' A'' => wp_logicS (.inr rfl) rfl fun e E => ?_)
  have Ke : Keeps [.ebx, .ecx] u5 e := (((A.keeps.mono (by decide)).trans (A'.keeps.mono (by decide))).trans
    (A''.keeps.mono (by decide))).trans (E.keeps.mono (by decide))
  have me : e.mem = u5.mem := by rw [E.mem, A''.mem, A'.mem, A.mem]
  have he := h5.keep Ke (by decide) (by decide) (by rw [me]; exact Outside.refl _ _ _ _)
  have ebx : (e.gpr .ebx).toNat = (!b).toNat := by
    rw [E.other _ (by decide), A''.gpr, ite_eq_left rfl, A'.gpr, ite_eq_right (by decide), A.gpr, eb]
    cases b <;> rfl
  have ecx : e.gpr .ecx = cmask (!b) := by
    rw [E.gpr, ite_eq_right (by decide), A''.other _ (by decide), A'.other _ (by decide), A.other _ (by decide), eb]
    cases b <;> rfl
  refine WP.mono (storeSlot_ok he hQb .ebx) fun u6 ⟨h6, k6, s6, r6⟩ => ?_
  have ecx6 : u6.gpr .ecx = cmask (!b) := by rw [r6.1 _ (by decide)]; exact ecx
  -- The remainder selected.
  have sepRT := arr_disj (w := kw len) hrt
  have sepQR := arr_disj (w := kw len) hqr
  simp only [S] at sepRT sepQR
  refine WP.seq (WP.mono (selectIn_ok h6 hr ht hrt true (k := !b) ecx6) fun u7 ⟨h7, O7, v7, r7⟩ => ?_)
  have v7' : wide u7.mem B (kw len) r =
      if !b then wide u6.mem B (kw len) t else wide u6.mem B (kw len) r := v7
  have wt6 : wide u6.mem B (kw len) t = wide u5.mem B (kw len) t := by
    rw [keep_wide k6 (by simp) (by simpa using hQb) ft, me]
  have wr6 : wide u6.mem B (kw len) r = wide u4.mem B (kw len) r := by
    rw [keep_wide k6 (by simp) (by simpa using hQb) fr, me, keep_wide k5 (by simpa using hrt.symm) hdr0 fr]
  rw [wt6, wr6] at v7'
  -- The quotient's new bit.
  have nq6 : num u6.mem B (kw len) q = num u1.mem B (kw len) q := by
    rw [k6.num (by simp) (by simpa using hQb) fq, me, k5.num (by simpa using hqt.symm) hdr0 fq,
      k4.num (by simpa using hqr.symm) hdr0 fq, k3.num (by simpa using hqr.symm) hdr0 fq,
      k2.num (by simp) (by simpa using hCy) fq]
  have nq7 : num u7.mem B (kw len) q = num u1.mem B (kw len) q := by
    rw [← nq6]; exact O7.val32 (by simp only [kk, Bool.toNat_true]; omega_arith) (by simp only [S] at fq; omega_arith)
  have evenQ : num u7.mem B (kw len) q % 2 = 0 := by
    rw [nq7]
    cases c with
    | false => simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at v1'; omega_arith
    | true => simp only [Bool.toNat_true, Nat.mul_one, P2] at v1'; omega_arith
  have qb6 : slot u6.mem B sQb = (!b).toNat := by rw [s6, ebx]
  have qb7 : slot u7.mem B sQb = (!b).toNat := by
    rw [← qb6]
    exact O7.w32 (.inl (by unfold sQb; simp only [arr, VG.Impl.Rsa.X86.Keys.hdr]; omega_arith)) (by unfold sQb; omega_arith)
  have bitQb : slot u7.mem B sQb ≤ 1 := by rw [qb7]; cases b <;> decide
  refine WP.block_append (WP.mono (addLow_ok h7 hq hQb) fun u8 ⟨h8, k8, v8, r8, _⟩ =>
    WP.mono (VG.Proof.Rsa.X86.Div.count_ok u8) fun u ⟨esi, zf, mu, ku⟩ => ?_)
  have wr8 : wide u8.mem B (kw len) r = wide u7.mem B (kw len) r := keep_wide k8 (by simpa using hqr) hdr0 fr
  have K7 : Keep B (kw len) [r] [] u6.mem u7.mem :=
    Keep.of_arr (d := 0) (by simpa using O7) (by simp only [S, kk, Bool.toNat_true]; omega_arith) (by simp)
  have Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u :=
    (r1.mono (by decide)).trans (((U2a.keeps.trans U2b.keeps).mono (by decide)).trans ((r2.mono (by decide)).trans
      ((r3.mono (by decide)).trans ((r4.mono (by decide)).trans ((r5.mono (by decide)).trans ((Ke.mono (by decide)).trans
        ((r6.mono (by decide)).trans ((r7.mono (by decide)).trans ((r8.mono (by decide)).trans
          (ku.mono (by decide)))))))))))
  have esi8 : u8.gpr .esi = s.gpr .esi := by
    have K8 : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u8 :=
      (r1.mono (by decide)).trans (((U2a.keeps.trans U2b.keeps).mono (by decide)).trans ((r2.mono (by decide)).trans
        ((r3.mono (by decide)).trans ((r4.mono (by decide)).trans ((r5.mono (by decide)).trans ((Ke.mono (by decide)).trans
          ((r6.mono (by decide)).trans ((r7.mono (by decide)).trans (r8.mono (by decide))))))))))
    exact K8.1 _ (by decide)
  refine ⟨h8.keep ku (by decide) (by decide) (by rw [mu]; exact Outside.refl _ _ _ _), ?_, by rw [esi, esi8],
    by rw [zf, esi8], Kall, ?_⟩
  · rw [mu]
    exact ((((((((k1.mono).trans k2.mono).trans k3.mono).trans k4.mono).trans k5.mono).trans
      (by rw [← me]; exact k6.mono)).trans K7.mono).trans k8.mono)
  · intro less
    have Rlt : wide s.mem B (kw len) r < 2 ^ (32 * kw len) := by omega_arith
    have c'0 : c'.toNat = 0 := by
      cases c' with
      | false => rfl
      | true =>
        exfalso
        have : 2 ^ (32 * (kw len + 1)) * (true : Bool).toNat = 2 ^ (32 * (kw len + 1)) := by simp
        omega_arith
    rw [c'0, Nat.mul_zero, Nat.add_zero] at v3'
    -- Its low bit `c`.
    have numR3 : num u3.mem B (kw len) r = wide u3.mem B (kw len) r % 2 ^ (32 * kw len) := by
      rw [wide_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (val32_lt _ _ _ _)]
    have even3 : num u3.mem B (kw len) r % 2 = 0 := by
      rw [numR3, Nat.mod_mod_of_dvd _ (by rw [P2]; exact Nat.dvd_mul_right 2 _), v3']; omega_arith
    have bitCy : slot u3.mem B sCy ≤ 1 := by rw [cy3]; cases c <;> decide
    have wr4 : wide u4.mem B (kw len) r = 2 * wide s.mem B (kw len) r + c.toNat := by
      have e3 := wide_eq u3.mem B (kw len) r
      rw [wide_eq, v4 even3 bitCy, top4, cy3]; omega_arith
    rw [wr4] at v5' v7'
    rw [mu, wr8, v8 evenQ bitQb, qb7, nq7]
    -- The quotient's top bit and the doubled quotient.
    have qtop : num s.mem B (kw len) q / 2 ^ (32 * kw len - 1) = c.toNat ∧
        2 * num s.mem B (kw len) q % 2 ^ (32 * kw len) = num u1.mem B (kw len) q := by
      have q1lt := val32_lt u1.mem B (arr (kw len) q) (kw len)
      change num u1.mem B (kw len) q < _ at q1lt
      rw [P2] at q1lt Qlt ⊢
      cases c with
      | false =>
        simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at v1'
        refine ⟨Nat.div_eq_of_lt (by omega_arith), ?_⟩
        rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
      | true =>
        simp only [Bool.toNat_true, Nat.mul_one] at v1'
        refine ⟨?_, ?_⟩
        · rw [show num s.mem B (kw len) q = (num s.mem B (kw len) q - 2 ^ (32 * kw len - 1)) + 2 ^ (32 * kw len - 1) by
            omega_arith, Nat.add_div_right _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (by omega_arith)]
          rfl
        rw [show 2 * num s.mem B (kw len) q = num u1.mem B (kw len) q + 2 * 2 ^ (32 * kw len - 1) by omega_arith,
          Nat.add_mod_right, Nat.mod_eq_of_lt q1lt]
    obtain ⟨qd, qm⟩ := qtop
    simp only [VG.Proof.Rsa.divStep, qd, qm]
    have T5 : wide u5.mem B (kw len) t < 2 ^ (32 * (kw len + 1)) := val32_lt u5.mem B (arr (kw len) t) (kw len + 1)
    cases b with
    | false =>
      simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero, Bool.not_false, ite_true] at v5' v7' ⊢
      split <;> simp only [Prod.mk.injEq, Bool.toNat_true, and_true] <;> omega_arith
    | true =>
      simp only [Bool.toNat_true, Nat.mul_one, Bool.not_true, Bool.false_eq_true, ite_false] at v5' v7' ⊢
      split <;> simp only [Prod.mk.injEq, Bool.toNat_false, Nat.add_zero, and_true] <;> omega_arith

end VG.Proof.Rsa.X86.KeyRt
