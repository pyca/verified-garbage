module

import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
public import VerifiedGarbage.Proof.Rsa.KeyMath
import VerifiedGarbage.Proof.Rsa.X86.DivCount
import VerifiedGarbage.Proof.Framework.Omega
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.Prop
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic

/-! ### `Rsa.X86.KeyRt.DivStep`, which only this module used -/

section

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
  rw [wide_eq, wide_eq, F.num hj hd fit, F.word (i := w) (by simp only [S]; omega_using []) hj hd fit]

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
  obtain fq := h.ws.fit64 hq
  obtain fr := h.ws.fit64 hr
  obtain fd := h.ws.fit64 hd
  obtain ft := h.ws.fit64 ht
  obtain hCy : sCy + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr := by decide
  obtain hQb : sQb + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr := by decide
  obtain hdr0 : ∀ e ∈ ([] : List Nat), e + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr := by simp
  obtain hdrCy : ∀ e ∈ [sCy], e + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr := by simp; decide
  obtain hdrQb : ∀ e ∈ [sQb], e + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr := by simp; decide
  -- The powers of two.
  obtain P2 : 2 ^ (32 * kw len) = 2 * 2 ^ (32 * kw len - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega_arith
  obtain PX : 2 ^ (32 * (kw len + 1)) = 2 ^ (32 * kw len) * 2 ^ 32 := by
    rw [← Nat.pow_add]; congr 1
  obtain PX2 : 2 * 2 ^ (32 * kw len) ≤ 2 ^ (32 * (kw len + 1)) := by
    rw [PX]; omega_arith
  -- The divisor and the inputs.
  obtain Dlt : num s.mem B (kw len) d < 2 ^ (32 * kw len) := val32_lt s.mem B (arr (kw len) d) (kw len)
  obtain Qlt : num s.mem B (kw len) q < 2 ^ (32 * kw len) := val32_lt s.mem B (arr (kw len) q) (kw len)
  obtain wd : wide s.mem B (kw len) d = num s.mem B (kw len) d := by
    rw [wide_eq, top, Nat.mul_zero, Nat.add_zero]
  unfold VG.Impl.Rsa.X86.KeyRt.divStep
  -- The quotient shifted up, its top bit `c`.
  refine WP.seq (WP.mono (chainAdd_ok h hq hq hq false) fun u1 ⟨h1, k1, ⟨c, ec, v1⟩, r1⟩ => ?_)
  have v1' : num u1.mem B (kw len) q + 2 ^ (32 * kw len) * c.toNat =
      num s.mem B (kw len) q + num s.mem B (kw len) q := v1
  refine WP.seq (wp_movS rfl fun u2a U2a _ => wp_logicS (.inl rfl) rfl fun u2b U2b => ?_)
  obtain h2b := h1.keep (U2a.keeps.trans U2b.keeps) (by decide) (by decide)
    (by rw [U2b.mem, U2a.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (storeSlot_ok h2b hCy .eax) fun u2 ⟨h2, k2, s2, r2⟩ => ?_
  rw [U2b.mem, U2a.mem] at k2
  obtain cy2 : slot u2.mem B sCy = c.toNat := by
    rw [s2, U2b.gpr, ite_eq_left rfl, U2a.gpr, ec]; cases c <;> rfl
  -- The remainder shifted up.
  obtain wr2 : wide u2.mem B (kw len) r = wide s.mem B (kw len) r := by
    rw [keep_wide k2 (by simp) (by simpa using hCy) fr, (keep_wide k1 (by simpa using hqr) hdr0 fr)]
  refine WP.seq (WP.mono (chainAdd_ok h2 hr hr hr true) fun u3 ⟨h3, k3, ⟨c', _, v3⟩, r3⟩ => ?_)
  have v3' : wide u3.mem B (kw len) r + 2 ^ (32 * (kw len + 1)) * c'.toNat =
      wide u2.mem B (kw len) r + wide u2.mem B (kw len) r := v3
  rw [wr2] at v3'
  obtain cy3 : slot u3.mem B sCy = c.toNat := by rw [keep_slot k3 hCy, cy2]
  refine WP.seq (WP.mono (addLow_ok h3 hr hCy) fun u4 ⟨h4, k4, v4, r4, top4⟩ => ?_)
  -- The difference with the divisor, its borrow `b`.
  obtain wd4 : wide u4.mem B (kw len) d = num s.mem B (kw len) d := by
    rw [keep_wide k4 (by simpa using hrd) hdr0 fd, keep_wide k3 (by simpa using hrd) hdr0 fd,
      keep_wide k2 (by simp) (by simpa using hCy) fd, keep_wide k1 (by simpa using hqd) hdr0 fd, wd]
  refine WP.seq (WP.mono (chainSub_ok h4 ht hr hd true) fun u5 ⟨h5, k5, ⟨b, eb, v5⟩, r5⟩ => ?_)
  have v5' : wide u5.mem B (kw len) t + wide u4.mem B (kw len) d =
      wide u4.mem B (kw len) r + 2 ^ (32 * (kw len + 1)) * b.toNat := v5
  rw [wd4] at v5'
  -- The bit kept, and the mask selecting the difference.
  refine WP.seq (wp_movS rfl fun a A _ => wp_logicS (.inr rfl) rfl fun a' A' => wp_logicS (.inl rfl) rfl
    fun a'' A'' => wp_logicS (.inr rfl) rfl fun e E => ?_)
  obtain Ke : Keeps [.ebx, .ecx] u5 e := (((A.keeps.mono (by decide)).trans (A'.keeps.mono (by decide))).trans
    (A''.keeps.mono (by decide))).trans (E.keeps.mono (by decide))
  obtain me : e.mem = u5.mem := by rw [E.mem, A''.mem, A'.mem, A.mem]
  obtain he := h5.keep Ke (by decide) (by decide) (by rw [me]; exact Outside.refl _ _ _ _)
  obtain ebx : (e.gpr .ebx).toNat = (!b).toNat := by
    rw [E.other _ (by decide), A''.gpr, ite_eq_left rfl, A'.gpr, ite_eq_right (by decide), A.gpr, eb]
    cases b <;> rfl
  obtain ecx : e.gpr .ecx = cmask (!b) := by
    rw [E.gpr, ite_eq_right (by decide), A''.other _ (by decide), A'.other _ (by decide), A.other _ (by decide), eb]
    cases b <;> rfl
  refine WP.mono (storeSlot_ok he hQb .ebx) fun u6 ⟨h6, k6, s6, r6⟩ => ?_
  obtain ecx6 : u6.gpr .ecx = cmask (!b) := by rw [r6.1 _ (by decide)]; exact ecx
  -- The remainder selected.
  obtain sepRT := arr_disj (w := kw len) hrt
  obtain sepQR := arr_disj (w := kw len) hqr
  simp only [S] at sepRT sepQR
  refine WP.seq (WP.mono (selectIn_ok h6 hr ht hrt true (k := !b) ecx6) fun u7 ⟨h7, O7, v7, r7⟩ => ?_)
  have v7' : wide u7.mem B (kw len) r =
      if !b then wide u6.mem B (kw len) t else wide u6.mem B (kw len) r := v7
  obtain wt6 : wide u6.mem B (kw len) t = wide u5.mem B (kw len) t := by
    rw [keep_wide k6 (by simp) (by simpa using hQb) ft, me]
  obtain wr6 : wide u6.mem B (kw len) r = wide u4.mem B (kw len) r := by
    rw [keep_wide k6 (by simp) (by simpa using hQb) fr, me, keep_wide k5 (by simpa using hrt.symm) hdr0 fr]
  rw [wt6, wr6] at v7'
  -- The quotient's new bit.
  obtain nq6 : num u6.mem B (kw len) q = num u1.mem B (kw len) q := by
    rw [k6.num (by simp) (by simpa using hQb) fq, me, k5.num (by simpa using hqt.symm) hdr0 fq,
      k4.num (by simpa using hqr.symm) hdr0 fq, k3.num (by simpa using hqr.symm) hdr0 fq,
      k2.num (by simp) (by simpa using hCy) fq]
  obtain nq7 : num u7.mem B (kw len) q = num u1.mem B (kw len) q := by
    rw [← nq6]; exact O7.val32 (by simp only [kk, Bool.toNat_true]; omega_arith) (by simp only [S] at fq; omega_arith)
  obtain evenQ : num u7.mem B (kw len) q % 2 = 0 := by
    rw [nq7]
    cases c with
    | false => simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at v1'; omega_arith
    | true => simp only [Bool.toNat_true, Nat.mul_one, P2] at v1'; omega_arith
  obtain qb6 : slot u6.mem B sQb = (!b).toNat := by rw [s6, ebx]
  obtain qb7 : slot u7.mem B sQb = (!b).toNat := by
    rw [← qb6]
    exact O7.w32 (.inl (by unfold sQb; simp only [arr, VG.Impl.Rsa.X86.Keys.hdr]; omega_arith)) (by unfold sQb; omega_arith)
  obtain bitQb : slot u7.mem B sQb ≤ 1 := by rw [qb7]; cases b <;> decide
  refine WP.block_append (WP.mono (addLow_ok h7 hq hQb) fun u8 ⟨h8, k8, v8, r8, _⟩ =>
    WP.mono (VG.Proof.Rsa.X86.Div.count_ok u8) fun u ⟨esi, zf, mu, ku⟩ => ?_)
  obtain wr8 : wide u8.mem B (kw len) r = wide u7.mem B (kw len) r := keep_wide k8 (by simpa using hqr) hdr0 fr
  obtain K7 : Keep B (kw len) [r] [] u6.mem u7.mem :=
    Keep.of_arr (d := 0) (by simpa using O7) (by simp only [S, kk, Bool.toNat_true]; omega_arith) (by simp)
  obtain Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u :=
    (r1.mono (by decide)).trans (((U2a.keeps.trans U2b.keeps).mono (by decide)).trans ((r2.mono (by decide)).trans
      ((r3.mono (by decide)).trans ((r4.mono (by decide)).trans ((r5.mono (by decide)).trans ((Ke.mono (by decide)).trans
        ((r6.mono (by decide)).trans ((r7.mono (by decide)).trans ((r8.mono (by decide)).trans
          (ku.mono (by decide)))))))))))
  obtain esi8 : u8.gpr .esi = s.gpr .esi := by
    obtain K8 : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u8 :=
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
    obtain Rlt : wide s.mem B (kw len) r < 2 ^ (32 * kw len) := by omega_arith
    obtain c'0 : c'.toNat = 0 := by
      cases c' with
      | false => rfl
      | true =>
        exfalso
        have : 2 ^ (32 * (kw len + 1)) * (true : Bool).toNat = 2 ^ (32 * (kw len + 1)) := by simp
        omega_arith
    rw [c'0, Nat.mul_zero, Nat.add_zero] at v3'
    -- Its low bit `c`.
    obtain numR3 : num u3.mem B (kw len) r = wide u3.mem B (kw len) r % 2 ^ (32 * kw len) := by
      rw [wide_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (val32_lt _ _ _ _)]
    obtain even3 : num u3.mem B (kw len) r % 2 = 0 := by
      rw [numR3, Nat.mod_mod_of_dvd _ (by rw [P2]; exact Nat.dvd_mul_right 2 _), v3']; omega_arith
    obtain bitCy : slot u3.mem B sCy ≤ 1 := by rw [cy3]; cases c <;> decide
    obtain wr4 : wide u4.mem B (kw len) r = 2 * wide s.mem B (kw len) r + c.toNat := by
      obtain e3 := wide_eq u3.mem B (kw len) r
      rw [wide_eq, v4 even3 bitCy, top4, cy3]; omega_arith
    rw [wr4] at v5' v7'
    rw [mu, wr8, v8 evenQ bitQb, qb7, nq7]
    -- The quotient's top bit and the doubled quotient.
    obtain qtop : num s.mem B (kw len) q / 2 ^ (32 * kw len - 1) = c.toNat ∧
        2 * num s.mem B (kw len) q % 2 ^ (32 * kw len) = num u1.mem B (kw len) q := by
      obtain q1lt := val32_lt u1.mem B (arr (kw len) q) (kw len)
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
    obtain T5 : wide u5.mem B (kw len) t < 2 ^ (32 * (kw len + 1)) := val32_lt u5.mem B (arr (kw len) t) (kw len + 1)
    cases b with
    | false =>
      simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero, Bool.not_false, ite_true] at v5' v7' ⊢
      split <;> simp only [Prod.mk.injEq, Bool.toNat_true, and_true] <;> omega_arith
    | true =>
      simp only [Bool.toNat_true, Nat.mul_one, Bool.not_true, Bool.false_eq_true, ite_false] at v5' v7' ⊢
      split <;> simp only [Prod.mk.injEq, Bool.toNat_false, Nat.add_zero, and_true] <;> omega_arith

end VG.Proof.Rsa.X86.KeyRt

end

end


/-! # The key workspace's division at a run-time width

`div_ok` states `Keys.div_ok`'s result for `KeyRt.div`: `32 w` steps of
`divStep_ok` from a zero remainder leave the quotient in `[q]` and the
remainder in `[r]`, as `Rsa.divIter` does (`Div.loop_ok`'s schedule).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S)

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- An array's `w` words, for its `w + 1` below `2^(32 w)`. -/
theorem num_of_wide {m : Mem} {w j : Nat} (hlt : wide m B w j < 2 ^ (32 * w)) : num m B w j = wide m B w j := by
  rw [wide_eq] at hlt ⊢
  obtain topZero : w32 m B (arr w j + 4 * w) = 0 := by
    by_contra ne
    obtain ge := Nat.mul_le_mul_left (2 ^ (32 * w)) (show 1 ≤ w32 m B (arr w j + 4 * w) by omega_using [ne])
    simp only [Nat.mul_one] at ge
    omega_using [hlt, ge]
  rw [topZero, Nat.mul_zero, Nat.add_zero]

/-- What the division's loop keeps after `i` steps. -/
structure DivInv (L : Lay) (B : Addr) (Z len N : Nat) (q r d t : Nat) (s₀ : State) (D Q i : Nat)
    (s : State) : Prop where
  ws : RtWs L s B Z len N
  index : i ≤ 32 * kw len
  count : s.gpr .esi = BitVec.ofNat 32 (32 * kw len - i)
  frame : Keep B (kw len) [q, r, t] [sCy, sQb] s₀.mem s.mem
  rest : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s₀ s
  divisor : num s.mem B (kw len) d = D
  top : w32 s.mem B (arr (kw len) d + 4 * kw len) = 0
  value : 0 < D → (wide s.mem B (kw len) r, num s.mem B (kw len) q) =
    VG.Proof.Rsa.divIter D (32 * kw len) i (0, Q)

theorem divLoop_ok {s₀ s : State} {q r d t D Q : Nat} (hq : q < N) (hr : r < N) (hd : d < N) (ht : t < N)
    (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t)
    (h : DivInv L B Z len N q r d t s₀ D Q 0 s) (boundQ : Q < 2 ^ (32 * kw len)) :
    WP isa (.loop (VG.Impl.Rsa.X86.KeyRt.divStep L q r d t) .ne) s (DivInv L B Z len N q r d t s₀ D Q (32 * kw len)) := by
  have positive := h.ws.kw_pos
  have wle := h.ws.ws.wle
  obtain fd := h.ws.ws.fit64 hd
  let I := fun k u => ∃ i, i + k = 32 * kw len ∧ 0 < k ∧ DivInv L B Z len N q r d t s₀ D Q i u
  refine WP.loop (M := isa) I ?_ (32 * kw len) s ⟨0, by omega_using [], by omega_using [positive], h⟩
  intro k u pre
  obtain ⟨i, sum, hk, inv⟩ := pre
  refine WP.mono (divStep_ok inv.ws hq hr hd ht hqr hqd hqt hrd hrt inv.top) ?_
  rintro v ⟨hv, frameV, count, zero, restV, valueV⟩
  obtain countV : v.gpr .esi = BitVec.ofNat 32 (32 * kw len - (i + 1)) := by
    rw [count, inv.count]
    change BitVec.ofNat 32 (32 * kw len - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [sum, hk])]
    congr 1
  obtain zeroV : v.zf = some (decide (i + 1 = 32 * kw len)) := by
    rw [zero, inv.count]
    change some (BitVec.ofNat 32 (32 * kw len - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [sum, hk]), ofNat_beq_zero (by omega_using [wle])]
    simp only [show 32 * kw len - i - 1 = 0 ↔ i + 1 = 32 * kw len by omega_using [sum, hk]]
  obtain hdr0 : ∀ e ∈ [sCy, sQb], e + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr := by simp; decide
  obtain next : DivInv L B Z len N q r d t s₀ D Q (i + 1) v := by
    refine ⟨hv, by omega_using [sum, hk], countV, inv.frame.trans frameV, inv.rest.trans restV, ?_, ?_, ?_⟩
    · rw [frameV.num (by simp; omega_using [hqd, hrd, hdt]) hdr0 fd, inv.divisor]
    · rw [frameV.word (i := kw len) (by simp only [S]; omega_using []) (by simp; omega_using [hqd, hrd, hdt]) hdr0 fd, inv.top]
    · intro dPos
      obtain previous := inv.value dPos
      obtain ⟨_, less, _, _, _⟩ := VG.Proof.Rsa.divIter_inv dPos boundQ i (by omega_using [sum])
      rw [← previous] at less
      rw [inv.divisor] at valueV
      exact (valueV less).trans (by rw [previous]; rfl)
  by_cases done : i + 1 = 32 * kw len
  · left
    refine ⟨?_, done ▸ next⟩
    change v.zf.map not = some false
    simp only [zeroV, done, decide_true, Option.map_some, Bool.not_true]
  · right
    refine ⟨?_, k - 1, by omega_using [hk], i + 1, by omega_using [sum, hk], by omega_using [sum, hk, done], next⟩
    change v.zf.map not = some true
    simp only [zeroV, done, decide_false, Option.map_some, Bool.not_false]

theorem div_ok {s : State} (h : RtWs L s B Z len N) {q r d t : Nat} (hq : q < N) (hr : r < N) (hd : d < N)
    (ht : t < N) (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t)
    (top : w32 s.mem B (arr (kw len) d + 4 * kw len) = 0) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.div L q r d t) s fun u => RtWs L u B Z len N ∧
      Keep B (kw len) [q, r, t] [sCy, sQb] s.mem u.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u ∧
      (0 < num s.mem B (kw len) d →
        num u.mem B (kw len) q = num s.mem B (kw len) q / num s.mem B (kw len) d ∧
        num u.mem B (kw len) r = num s.mem B (kw len) q % num s.mem B (kw len) d) := by
  obtain fq := h.ws.fit64 hq
  obtain fd := h.ws.fit64 hd
  unfold VG.Impl.Rsa.X86.KeyRt.div
  obtain boundQ : num s.mem B (kw len) q < 2 ^ (32 * kw len) := val32_lt _ _ _ _
  refine WP.seq (WP.seq (WP.mono (zeroWide_ok h hr) fun u ⟨hu, ku, zu, ru⟩ => ?_))
  rw [show bits L = bits L ++ [] from (List.append_nil _).symm]
  refine bits_ok hu fun v K m e => WP.block_nil ?_
  obtain inv : DivInv L B Z len N q r d t s (num s.mem B (kw len) d) (num s.mem B (kw len) q) 0 v :=
    ⟨hu.keep K (by decide) (by decide) (by rw [m]; exact Outside.refl _ _ _ _), by omega_using [],
      by rw [e]; rfl, by rw [m]; exact ku.mono, (ru.mono (by decide)).trans (K.mono (by decide)),
      by rw [m, ku.num (by simpa using hrd) (by simp) fd],
      by rw [m, ku.word (i := kw len) (by simp only [S]; omega_using []) (by simpa using hrd) (by simp) fd, top],
      fun _ => by
        rw [m, ku.num (by simpa using hqr.symm) (by simp) fq]
        exact Prod.ext zu rfl⟩
  refine WP.mono (divLoop_ok hq hr hd ht hqr hqd hqt hrd hrt hdt inv boundQ) fun w done => ?_
  refine ⟨done.ws, done.frame, done.rest, fun dPos => ?_⟩
  obtain value := done.value dPos
  rw [VG.Proof.Rsa.divIter_done dPos boundQ] at value
  obtain ⟨rem, quot⟩ := Prod.mk.inj value
  refine ⟨quot, ?_⟩
  obtain small := Nat.mod_lt (num s.mem B (kw len) q) dPos
  obtain bound : num s.mem B (kw len) d < 2 ^ (32 * kw len) := val32_lt _ _ _ _
  rw [num_of_wide (by omega_using [rem, small, bound]), rem]

end VG.Proof.Rsa.X86.KeyRt
