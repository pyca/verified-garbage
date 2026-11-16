module
public import VerifiedGarbage.Impl.Rsa.X86.Inverse
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Rsa.X86.KeyBits
import VerifiedGarbage.Proof.Mont.X86.ExponentShift
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Rsa.X86.KeySelect
public import VerifiedGarbage.Proof.Mont.X86.ShiftDown
import VerifiedGarbage.Proof.Rsa.X86.KeySub
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Rsa.KeyMath

/-! ### `Rsa.X86.KeyHalf`, which only this module used -/

section

/-! # Halving an RSA workspace array with an incoming carry -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot

theorem half_ok {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N)
    (hj : j < N) (bit : (s.gpr .ebx).toNat ≤ 1) :
    WP isa (half w j) s fun t => Ws t B Z w N ∧ Keep B w [j] [] s.mem t.mem ∧
      num t.mem B w j = (num s.mem B w j + 2 ^ (32 * w) * (s.gpr .ebx).toNat) / 2 ∧
      Keeps [.eax, .edx, .ebp] s t := by
  obtain fit := h.arr_fit hj
  simp only [S] at fit
  have nw := h.workspace.nowrap
  unfold half
  have wpos := h.wpos
  change WP isa (.seq (.block [.store (VG.Impl.Mont.X86.sc (arr w j + 4 * w)) .ebx])
    (VG.Impl.Mont.X86.Dynamic.shiftDown (w + 1) (arr w j))) s _
  refine WP.seq (wp_storeS (h.workspace.ea (by omega_using [fit])) (h.workspace.write (by omega_using [fit])) fun u U => WP.block_nil ?_)
  obtain hu := h.workspace.of_keeps (U.keeps []) (by decide)
  refine WP.mono (VG.Proof.Mont.X86.Dynamic.shiftDown_ok hu (k := w + 1) (out := arr w j) (by omega_using [wpos]) (by omega_using [fit])) ?_
  rintro t ⟨frame, value, rest⟩
  obtain stored := writeW32_outside s.mem B (d := arr w j + 4 * w) (s.gpr .ebx) (by omega_using [fit, nw])
  obtain keepU : Keep B w [j] [] s.mem u.mem := by
    rw [U.mem]
    exact Keep.of_arr stored (by unfold S; omega_using []) (by simp)
  obtain keepT : Keep B w [j] [] u.mem t.mem :=
    Keep.of_arr (d := 0) (by simpa using frame) (by unfold S; omega_using []) (by simp)
  refine ⟨h.rest ((U.keeps _).trans rest), keepU.trans keepT, ?_, (U.keeps _).trans rest⟩
  obtain original : val32 u.mem B (arr w j) (w + 1) =
      num s.mem B w j + 2 ^ (32 * w) * (s.gpr .ebx).toNat := by
    rw [val32_succ, U.mem, w32_write_self, stored.val32 (by omega_using []) (by omega_using [fit, nw])]
  rw [original] at value
  obtain bound := val32_lt s.mem B (arr w j) w
  obtain positive : 0 < 2 ^ (32 * w) := Nat.two_pow_pos _
  obtain small : (num s.mem B w j + 2 ^ (32 * w) * (s.gpr .ebx).toNat) / 2 < 2 ^ (32 * w) := by
    obtain mul : 2 ^ (32 * w) * (s.gpr .ebx).toNat ≤ 2 ^ (32 * w) := by
      simpa using Nat.mul_le_mul_left (2 ^ (32 * w)) bit
    unfold num
    omega_using [bound, mul]
  obtain lower := val32_lt t.mem B (arr w j) w
  rw [val32_succ] at value
  obtain topZero : w32 t.mem B (arr w j + 4 * w) = 0 := by
    by_contra ne
    obtain ge := Nat.mul_le_mul_left (2 ^ (32 * w)) (show 1 ≤ w32 t.mem B (arr w j + 4 * w) by omega_using [ne])
    simp only [Nat.mul_one] at ge
    omega_using [hj, bit, fit, nw, wpos, value, original, bound, positive, small, lower, ne, ge]
  rw [topZero, Nat.mul_zero, Nat.add_zero] at value
  exact value
end VG.Proof.Rsa.X86.Keys

end

end


/-! # The inverse on i686: `u` and `v` in a step -/

@[expose] public section

namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Proof.Rsa (borrow_iff invU_arith)

/-- The first part of a step from the bank at `A` to the bank at `D`: `u`, `v`, and the masks. -/
def invU (w A D : Nat) : List (Prog isa) := [
  .block (bitOf w sOdd A),
  sub3 w aT1 A (A + 1),
  .block ([.store (VG.Impl.Mont.X86.sc sB) .ebx] ++ andS sC sOdd sB),
  sub3 w aT2 (A + 1) A,
  sel w (D + 1) (A + 1) A sC,
  sel w aT3 aT1 aT2 sC,
  sel w D A aT3 sOdd,
  .block [.mov .ebx (.imm 0)],
  half w D]

theorem invU_ok {s : State} {B : Addr} {Z w N A D : Nat} (h : Ws s B Z w N)
    (hN15 : 15 ≤ N) (hb : (A = 0 ∧ D = 4) ∨ (A = 4 ∧ D = 0)) :
    WP isa (seqs (invU w A D)) s fun t => Ws t B Z w N ∧
      Keep B w [D, D + 1, aT1, aT2, aT3] [sOdd, sB, sC] s.mem t.mem ∧
      slot t.mem B sOdd = num s.mem B w A % 2 ∧
      slot t.mem B sC = (if num s.mem B w A % 2 = 1 ∧ num s.mem B w A < num s.mem B w (A + 1) then 1 else 0) ∧
      num t.mem B w (D + 1) = (if num s.mem B w A % 2 = 1 ∧ num s.mem B w A < num s.mem B w (A + 1)
        then num s.mem B w A else num s.mem B w (A + 1)) ∧
      num t.mem B w D = (if num s.mem B w A % 2 = 1 then
        (if num s.mem B w A < num s.mem B w (A + 1) then (num s.mem B w (A + 1) - num s.mem B w A) / 2
          else (num s.mem B w A - num s.mem B w (A + 1)) / 2) else num s.mem B w A / 2) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  obtain hsOdd : sOdd + 4 ≤ hdr := by decide
  obtain hsB : sB + 4 ≤ hdr := by decide
  obtain hsC : sC + 4 ≤ hdr := by decide
  obtain fA := h.fit64 (j := A) (by idx)
  obtain fA1 := h.fit64 (j := A + 1) (by idx)
  obtain fT1 := h.fit64 (j := aT1) (by idx)
  obtain fT2 := h.fit64 (j := aT2) (by idx)
  obtain fT3 := h.fit64 (j := aT3) (by idx)
  obtain fD1 := h.fit64 (j := D + 1) (by idx)
  generalize hu : num s.mem B w A = u
  generalize hv : num s.mem B w (A + 1) = v
  unfold invU
  -- 1: the low bit of `u`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (bitOf_ok h (by idx) hsOdd) fun t1 ⟨h1, k1, o1, r1⟩ => ?_
  rw [hu] at o1
  obtain u1 : num t1.mem B w A = u := by rw [k1.num (by simp) (by simp; decide) fA, hu]
  obtain v1 : num t1.mem B w (A + 1) = v := by rw [k1.num (by simp) (by simp; decide) fA1, hv]
  -- 2: `u - v`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h1 (by idx) (by idx) (by idx) (by idx) (by idx)) fun t2 ⟨h2, k2, d2, b2, r2⟩ => ?_
  rw [u1, v1] at d2
  -- 3: the masks.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.block_append (WP.mono (store_slot h2 hsB .ebx) fun t3' ⟨h3', k3', sB3, r3'⟩ => ?_)
  obtain o3 : slot t3'.mem B sOdd = u % 2 := by
    rw [k3'.slot hsOdd (by decide), k2.slot hsOdd (by simp), o1]
  refine WP.mono (andS_ok h3' hsC hsOdd hsB (by rw [o3]; omega_arith) (by rw [sB3]; exact b2)) fun t3 ⟨h3, k3, c3, r3⟩ => ?_
  rw [o3, sB3] at c3
  obtain lt : (t2.gpr .ebx).toNat = 1 ↔ u < v := by
    have := borrow_iff d2 (val32_lt _ _ _ _) b2; omega_arith
  obtain c3' : slot t3.mem B sC = (if u % 2 = 1 ∧ u < v then 1 else 0) := by
    rw [c3]; by_cases e : u < v <;> simp [e, lt]
  obtain K3 : Keep B w [] [sB, sC] t2.mem t3.mem := k3'.join k3
  obtain o3' : slot t3.mem B sOdd = u % 2 := by rw [k3.slot hsOdd (by decide), o3]
  obtain u3 : num t3.mem B w A = u := by
    rw [K3.num (by simp) (by simp; decide) fA, k2.num (by idx) (by simp) fA, u1]
  obtain v3 : num t3.mem B w (A + 1) = v := by
    rw [K3.num (by simp) (by simp; decide) fA1, k2.num (by idx) (by simp) fA1, v1]
  -- 4: `v - u`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h3 (by idx) (by idx) (by idx) (by idx) (by idx)) fun t4 ⟨h4, k4, d4, b4, r4⟩ => ?_
  rw [u3, v3] at d4
  obtain cs4 : slot t4.mem B sC = (if u % 2 = 1 ∧ u < v then 1 else 0) := by
    rw [k4.slot hsC (by simp), c3']
  obtain cb4 : slot t4.mem B sC ≤ 1 := by rw [cs4]; split <;> omega_arith
  -- 5: `v'`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok h4 (by idx) (by idx) (by idx) hsC cb4) fun t5 ⟨h5, k5, e5, r5⟩ => ?_
  rw [k4.num (by idx) (by simp) fA1, k4.num (by idx) (by simp) fA, u3, v3, cs4] at e5
  -- 6: `|u - v|`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok h5 (by idx) (by idx) (by idx) hsC
    (by rw [k5.slot hsC (by simp)]; exact cb4)) fun t6 ⟨h6, k6, e6, r6⟩ => ?_
  rw [k5.slot hsC (by simp), cs4, k5.num (by idx) (by simp) fT1, k5.num (by idx) (by simp) fT2,
    k4.num (by idx) (by simp) fT1, K3.num (by simp) (by simp; decide) fT1] at e6
  -- 7: `u'` before the halving.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  obtain od6 : slot t6.mem B sOdd = u % 2 := by
    rw [k6.slot hsOdd (by simp), k5.slot hsOdd (by simp), k4.slot hsOdd (by simp), o3']
  refine WP.mono (sel_ok h6 (by idx) (by idx) (by idx) hsOdd
    (by rw [od6]; omega_arith)) fun t7 ⟨h7, k7, e7, r7⟩ => ?_
  rw [od6, e6, k6.num (by idx) (by simp) fA, k5.num (by idx) (by simp) fA, k4.num (by idx) (by simp) fA, u3] at e7
  -- 8, 9: the halving.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine wp_movS rfl fun t8 u8 _ => WP.block_nil ?_
  obtain h8 := h7.rest u8.keeps (by decide) (by decide)
  refine WP.mono (half_ok h8 (by idx) (by rw [u8.gpr]; decide)) fun t ⟨h9, k9, e9, r9⟩ => ?_
  rw [u8.gpr, u8.mem] at e9
  rw [u8.mem] at k9
  refine ⟨h9, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact k1.mono.trans (k2.mono.trans (K3.mono.trans (k4.mono.trans (k5.mono.trans (k6.mono.trans
      (k7.mono.trans k9.mono))))))
  · rw [k9.slot hsOdd (by simp), k7.slot hsOdd (by simp), od6]
  · rw [k9.slot hsC (by simp), k7.slot hsC (by simp), k6.slot hsC (by simp), k5.slot hsC (by simp), cs4]
  · rw [k9.num (by idx) (by simp) fD1, k7.num (by idx) (by simp) fD1, k6.num (by idx) (by simp) fD1, e5]
    split <;> simp_all
  · rw [e9, e7, show (0 : BitVec 32).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
    exact invU_arith d2 b2 (val32_lt _ _ _ _) d4 b4 (val32_lt _ _ _ _)
  · exact ((((((((r1.mono (by decide)).trans r2).trans (r3'.mono (by decide))).trans
      (r3.mono (by decide))).trans r4).trans (r5.mono (by decide))).trans (r6.mono (by decide))).trans
      (r7.mono (by decide))).trans (u8.keeps.mono (by decide)) |>.trans (r9.mono (by decide))

end VG.Proof.Rsa.X86.Keys
