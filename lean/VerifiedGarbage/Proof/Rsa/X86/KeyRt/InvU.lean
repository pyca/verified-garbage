module

import VerifiedGarbage.Proof.Rsa.X86.KeyRt.InvParts
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Rsa.X86.InvParts
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Half
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Word

/-! # The inverse at a run-time width: `u` and `v` in a step

`invU_ok` states what `Keys.invU_ok` does, for the run-time width's
operations on `RtWs`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S slot wp_seqs_cons wp_seqs_append)
open VG.Impl.Rsa.X86.Keys (aM aNM aZero aT1 aT2 aT3 aT4 sOdd sB sC sT hdr seqs andS)
open VG.Proof.Rsa (borrow_iff invU_arith)

variable {L : Lay}

/-- The first part of a step from the bank at `A` to the bank at `D`: `u`, `v`, and the masks. -/
def invU (L : Lay) (A D : Nat) : List (Prog isa) := [
  .block (bitOf L sOdd A),
  sub3 L aT1 A (A + 1),
  .block ([.store (VG.Impl.Mont.X86.sc sB) .ebx] ++ andS sC sOdd sB),
  sub3 L aT2 (A + 1) A,
  sel L (D + 1) (A + 1) A sC,
  sel L aT3 aT1 aT2 sC,
  sel L D A aT3 sOdd,
  .block [.mov .ebx (.imm 0)],
  half L D]

theorem invU_ok {s : State} {B : Addr} {Z len N A D : Nat} (h : RtWs L s B Z len N)
    (hN15 : 15 ≤ N) (hb : (A = 0 ∧ D = 4) ∨ (A = 4 ∧ D = 0)) :
    WP isa (seqs (invU L A D)) s fun t => RtWs L t B Z len N ∧
      Keep B (kw len) [D, D + 1, aT1, aT2, aT3] [sOdd, sB, sC] s.mem t.mem ∧
      slot t.mem B sOdd = num s.mem B (kw len) A % 2 ∧
      slot t.mem B sC = (if num s.mem B (kw len) A % 2 = 1 ∧ num s.mem B (kw len) A < num s.mem B (kw len) (A + 1) then 1 else 0) ∧
      num t.mem B (kw len) (D + 1) = (if num s.mem B (kw len) A % 2 = 1 ∧ num s.mem B (kw len) A < num s.mem B (kw len) (A + 1)
        then num s.mem B (kw len) A else num s.mem B (kw len) (A + 1)) ∧
      num t.mem B (kw len) D = (if num s.mem B (kw len) A % 2 = 1 then
        (if num s.mem B (kw len) A < num s.mem B (kw len) (A + 1) then (num s.mem B (kw len) (A + 1) - num s.mem B (kw len) A) / 2
          else (num s.mem B (kw len) A - num s.mem B (kw len) (A + 1)) / 2) else num s.mem B (kw len) A / 2) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have hsOdd : sOdd + 4 ≤ hdr := by decide
  have hsB : sB + 4 ≤ hdr := by decide
  have hsC : sC + 4 ≤ hdr := by decide
  have fA := h.ws.fit64 (j := A) (by idx)
  have fA1 := h.ws.fit64 (j := A + 1) (by idx)
  have fT1 := h.ws.fit64 (j := aT1) (by idx)
  have fT2 := h.ws.fit64 (j := aT2) (by idx)
  have fT3 := h.ws.fit64 (j := aT3) (by idx)
  have fD1 := h.ws.fit64 (j := D + 1) (by idx)
  generalize hu : num s.mem B (kw len) A = u
  generalize hv : num s.mem B (kw len) (A + 1) = v
  unfold invU
  -- 1: the low bit of `u`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (bitOf_ok h (by idx) hsOdd) fun t1 ⟨h1, k1, o1, r1⟩ => ?_
  rw [hu] at o1
  have u1 : num t1.mem B (kw len) A = u := by rw [k1.num (by simp) (by simp; decide) fA, hu]
  have v1 : num t1.mem B (kw len) (A + 1) = v := by rw [k1.num (by simp) (by simp; decide) fA1, hv]
  -- 2: `u - v`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h1 (by idx) (by idx) (by idx)) fun t2 ⟨h2, k2, d2, b2, r2⟩ => ?_
  rw [u1, v1] at d2
  -- 3: the masks.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.block_append (WP.mono (storeSlot_ok h2 hsB .ebx) fun t3' ⟨h3', k3', sB3, r3'⟩ => ?_)
  have o3 : slot t3'.mem B sOdd = u % 2 := by
    rw [k3'.slot hsOdd (by decide), k2.slot hsOdd (by simp), o1]
  refine WP.mono (andS_ok h3' hsC hsOdd hsB (by rw [o3]; omega_arith) (by rw [sB3]; exact b2)) fun t3 ⟨h3, k3, c3, r3⟩ => ?_
  rw [o3, sB3] at c3
  have lt : (t2.gpr .ebx).toNat = 1 ↔ u < v := by
    have := borrow_iff d2 (val32_lt _ _ _ _) b2; omega_arith
  have c3' : slot t3.mem B sC = (if u % 2 = 1 ∧ u < v then 1 else 0) := by
    rw [c3]; by_cases e : u < v <;> simp [e, lt]
  have K3 : Keep B (kw len) [] [sB, sC] t2.mem t3.mem := k3'.join k3
  have o3' : slot t3.mem B sOdd = u % 2 := by rw [k3.slot hsOdd (by decide), o3]
  have u3 : num t3.mem B (kw len) A = u := by
    rw [K3.num (by simp) (by simp; decide) fA, k2.num (by idx) (by simp) fA, u1]
  have v3 : num t3.mem B (kw len) (A + 1) = v := by
    rw [K3.num (by simp) (by simp; decide) fA1, k2.num (by idx) (by simp) fA1, v1]
  -- 4: `v - u`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h3 (by idx) (by idx) (by idx)) fun t4 ⟨h4, k4, d4, b4, r4⟩ => ?_
  rw [u3, v3] at d4
  have cs4 : slot t4.mem B sC = (if u % 2 = 1 ∧ u < v then 1 else 0) := by
    rw [k4.slot hsC (by simp), c3']
  have cb4 : slot t4.mem B sC ≤ 1 := by rw [cs4]; split <;> omega_arith
  -- 5: `v'`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok h4 (by idx) (by idx) (by idx) hsC cb4 (.inl (by idx))) fun t5 ⟨h5, k5, e5, r5⟩ => ?_
  rw [k4.num (by idx) (by simp) fA1, k4.num (by idx) (by simp) fA, u3, v3, cs4] at e5
  -- 6: `|u - v|`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok h5 (by idx) (by idx) (by idx) hsC
    (by rw [k5.slot hsC (by simp)]; exact cb4) (.inl (by idx))) fun t6 ⟨h6, k6, e6, r6⟩ => ?_
  rw [k5.slot hsC (by simp), cs4, k5.num (by idx) (by simp) fT1, k5.num (by idx) (by simp) fT2,
    k4.num (by idx) (by simp) fT1, K3.num (by simp) (by simp; decide) fT1] at e6
  -- 7: `u'` before the halving.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have od6 : slot t6.mem B sOdd = u % 2 := by
    rw [k6.slot hsOdd (by simp), k5.slot hsOdd (by simp), k4.slot hsOdd (by simp), o3']
  refine WP.mono (sel_ok h6 (by idx) (by idx) (by idx) hsOdd
    (by rw [od6]; omega_arith) (.inl (by idx))) fun t7 ⟨h7, k7, e7, r7⟩ => ?_
  rw [od6, e6, k6.num (by idx) (by simp) fA, k5.num (by idx) (by simp) fA, k4.num (by idx) (by simp) fA, u3] at e7
  -- 8, 9: the halving.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine wp_movS rfl fun t8 u8 _ => WP.block_nil ?_
  have h8 := h7.keep u8.keeps (by decide) (by decide) (by rw [u8.mem]; exact Outside.refl _ _ _ _)
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
  · exact ((((((((r1.mono (by decide)).trans (r2.mono (by decide))).trans (r3'.mono (by decide))).trans
      (r3.mono (by decide))).trans (r4.mono (by decide))).trans (r5.mono (by decide))).trans (r6.mono (by decide))).trans
      (r7.mono (by decide))).trans (u8.keeps.mono (by decide)) |>.trans (r9.mono (by decide))

end VG.Proof.Rsa.X86.KeyRt
