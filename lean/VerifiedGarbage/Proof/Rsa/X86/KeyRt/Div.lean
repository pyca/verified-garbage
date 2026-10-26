module

import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.DivStep
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Defs.Prop
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import Mathlib.Util.CompileInductive

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
  have topZero : w32 m B (arr w j + 4 * w) = 0 := by
    by_contra ne
    have ge := Nat.mul_le_mul_left (2 ^ (32 * w)) (show 1 ≤ w32 m B (arr w j + 4 * w) by omega)
    simp only [Nat.mul_one] at ge
    omega
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
  have fd := h.ws.ws.fit64 hd
  let I := fun k u => ∃ i, i + k = 32 * kw len ∧ 0 < k ∧ DivInv L B Z len N q r d t s₀ D Q i u
  refine WP.loop (M := isa) I ?_ (32 * kw len) s ⟨0, by omega, by omega, h⟩
  intro k u pre
  obtain ⟨i, sum, hk, inv⟩ := pre
  refine WP.mono (divStep_ok inv.ws hq hr hd ht hqr hqd hqt hrd hrt inv.top) ?_
  rintro v ⟨hv, frameV, count, zero, restV, valueV⟩
  have countV : v.gpr .esi = BitVec.ofNat 32 (32 * kw len - (i + 1)) := by
    rw [count, inv.count]
    change BitVec.ofNat 32 (32 * kw len - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  have zeroV : v.zf = some (decide (i + 1 = 32 * kw len)) := by
    rw [zero, inv.count]
    change some (BitVec.ofNat 32 (32 * kw len - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [show 32 * kw len - i - 1 = 0 ↔ i + 1 = 32 * kw len by omega]
  have hdr0 : ∀ e ∈ [sCy, sQb], e + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr := by simp; decide
  have next : DivInv L B Z len N q r d t s₀ D Q (i + 1) v := by
    refine ⟨hv, by omega, countV, inv.frame.trans frameV, inv.rest.trans restV, ?_, ?_, ?_⟩
    · rw [frameV.num (by simp; omega) hdr0 fd, inv.divisor]
    · rw [frameV.word (i := kw len) (by simp only [S]; omega) (by simp; omega) hdr0 fd, inv.top]
    · intro dPos
      have previous := inv.value dPos
      obtain ⟨_, less, _, _, _⟩ := VG.Proof.Rsa.divIter_inv dPos boundQ i (by omega)
      rw [← previous] at less
      rw [inv.divisor] at valueV
      exact (valueV less).trans (by rw [previous]; rfl)
  by_cases done : i + 1 = 32 * kw len
  · left
    refine ⟨?_, done ▸ next⟩
    change v.zf.map not = some false
    simp only [zeroV, done, decide_true, Option.map_some, Bool.not_true]
  · right
    refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, next⟩
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
  have fq := h.ws.fit64 hq
  have fd := h.ws.fit64 hd
  unfold VG.Impl.Rsa.X86.KeyRt.div
  have boundQ : num s.mem B (kw len) q < 2 ^ (32 * kw len) := val32_lt _ _ _ _
  refine WP.seq (WP.seq (WP.mono (zeroWide_ok h hr) fun u ⟨hu, ku, zu, ru⟩ => ?_))
  rw [show bits L = bits L ++ [] from (List.append_nil _).symm]
  refine bits_ok hu fun v K m e => WP.block_nil ?_
  have inv : DivInv L B Z len N q r d t s (num s.mem B (kw len) d) (num s.mem B (kw len) q) 0 v :=
    ⟨hu.keep K (by decide) (by decide) (by rw [m]; exact Outside.refl _ _ _ _), by omega,
      by rw [e]; rfl, by rw [m]; exact ku.mono, (ru.mono (by decide)).trans (K.mono (by decide)),
      by rw [m, ku.num (by simpa using hrd) (by simp) fd],
      by rw [m, ku.word (i := kw len) (by simp only [S]; omega) (by simpa using hrd) (by simp) fd, top],
      fun _ => by
        rw [m, ku.num (by simpa using hqr.symm) (by simp) fq]
        exact Prod.ext zu rfl⟩
  refine WP.mono (divLoop_ok hq hr hd ht hqr hqd hqt hrd hrt hdt inv boundQ) fun w done => ?_
  refine ⟨done.ws, done.frame, done.rest, fun dPos => ?_⟩
  have value := done.value dPos
  rw [VG.Proof.Rsa.divIter_done dPos boundQ] at value
  obtain ⟨rem, quot⟩ := Prod.mk.inj value
  refine ⟨quot, ?_⟩
  have small := Nat.mod_lt (num s.mem B (kw len) q) dPos
  have bound : num s.mem B (kw len) d < 2 ^ (32 * kw len) := val32_lt _ _ _ _
  rw [num_of_wide (by omega), rem]

end VG.Proof.Rsa.X86.KeyRt
