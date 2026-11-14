module

public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.InvParts
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
public import VerifiedGarbage.Proof.Rsa.X86.InvStep
public import VerifiedGarbage.Proof.Rsa.KeyMath
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
import VerifiedGarbage.Proof.Rsa.X86.DivCount
import Mathlib.Tactic.Widget.Calc

/-! ### `Rsa.X86.KeyRt.InvStep`, which only this module used -/

section

/-! ### `Rsa.X86.KeyRt.InvU`, which only this module used -/

section

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

end

end


/-! # The inverse at a run-time width: one step is `invStep`

`invStep_ok`: the run-time width's `invStep` on `RtWs` takes the bank at
`A` to the bank at `D` by `Proof/Rsa/KeyMath.lean`'s `invStep`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S slot wp_seqs_cons wp_seqs_append bank)
open VG.Impl.Rsa.X86.Keys (aM aNM aZero aT1 aT2 aT3 aT4 sOdd sB sC sT hdr seqs)
open VG.Proof.Rsa (subMod halfMod invStep_arith)

variable {L : Lay}

/-- The selections of `x₁` and `x₂`. -/
def invX (L : Lay) (A D : Nat) : List (Prog isa) :=
  [sel L (D + 3) (A + 3) (A + 2) sC, sel L aT1 aT3 aT2 sC, sel L aT3 (A + 2) aT1 sOdd]

theorem invStep_eq (L : Lay) (A D : Nat) : VG.Impl.Rsa.X86.KeyRt.invStep L A D =
    seqs (invU L A D ++ (subModP L aT3 (A + 2) (A + 3) ++ (subModP L aT2 (A + 3) (A + 2) ++
      (invX L A D ++ halfModP L (D + 2))))) := rfl

theorem invStep_ok {s : State} {B : Addr} {Z len N A D : Nat} (h : RtWs L s B Z len N)
    (hN15 : 15 ≤ N) (hb : (A = 0 ∧ D = 4) ∨ (A = 4 ∧ D = 0)) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.invStep L A D) s fun t => RtWs L t B Z len N ∧
      Keep B (kw len) [D, D + 1, D + 2, D + 3, aT1, aT2, aT3, aT4] [sOdd, sB, sC] s.mem t.mem ∧
      (num s.mem B (kw len) aNM + num s.mem B (kw len) aM = 2 ^ (32 * kw len) → num s.mem B (kw len) aZero = 0 →
        num s.mem B (kw len) (A + 2) < num s.mem B (kw len) aM → num s.mem B (kw len) (A + 3) < num s.mem B (kw len) aM →
        bank t.mem B (kw len) D = VG.Proof.Rsa.invStep (num s.mem B (kw len) aM) (bank s.mem B (kw len) A)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have hsOdd : sOdd + 4 ≤ hdr := by decide
  have hsC : sC + 4 ≤ hdr := by decide
  have fA2 := h.ws.fit64 (j := A + 2) (by idx)
  have fA3 := h.ws.fit64 (j := A + 3) (by idx)
  have fM := h.ws.fit64 (j := aM) (by idx)
  have fNM := h.ws.fit64 (j := aNM) (by idx)
  have fZ := h.ws.fit64 (j := aZero) (by idx)
  have fT1 := h.ws.fit64 (j := aT1) (by idx)
  have fT2 := h.ws.fit64 (j := aT2) (by idx)
  have fT3 := h.ws.fit64 (j := aT3) (by idx)
  have fD := h.ws.fit64 (j := D) (by idx)
  have fD1 := h.ws.fit64 (j := D + 1) (by idx)
  have fD3 := h.ws.fit64 (j := D + 3) (by idx)
  rw [invStep_eq, wp_seqs_append (by unfold invU; exact List.cons_ne_nil _ _) (by unfold subModP; exact List.cons_ne_nil _ _)]
  refine WP.mono (invU_ok h hN15 hb) fun t1 ⟨h1, k1, o1, c1, v1, u1, r1⟩ => ?_
  rw [wp_seqs_append (by unfold subModP; exact List.cons_ne_nil _ _) (by unfold subModP; exact List.cons_ne_nil _ _)]
  refine WP.mono (subModP_ok h1 hN15 (by idx) (by idx) (by idx))
    fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  rw [wp_seqs_append (by unfold subModP; exact List.cons_ne_nil _ _) (by unfold invX; exact List.cons_ne_nil _ _)]
  refine WP.mono (subModP_ok h2 hN15 (by idx) (by idx) (by idx))
    fun t3 ⟨h3, k3, e3, r3⟩ => ?_
  rw [wp_seqs_append (by unfold invX; exact List.cons_ne_nil _ _) (by unfold halfModP; exact List.cons_ne_nil _ _)]
  unfold invX
  have cs3 : slot t3.mem B sC = slot t1.mem B sC := by
    rw [k3.slot hsC (by decide), k2.slot hsC (by decide)]
  have cb3 : slot t3.mem B sC ≤ 1 := by rw [cs3, c1]; split <;> omega_arith
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok h3 (by idx) (by idx) (by idx) hsC cb3 (.inl (by idx))) fun t4 ⟨h4, k4, e4, r4⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok h4 (by idx) (by idx) (by idx) hsC
    (by rw [k4.slot hsC (by simp)]; exact cb3) (.inl (by idx))) fun t5 ⟨h5, k5, e5, r5⟩ => ?_
  have od5 : slot t5.mem B sOdd = slot t1.mem B sOdd := by
    rw [k5.slot hsOdd (by simp), k4.slot hsOdd (by simp), k3.slot hsOdd (by decide), k2.slot hsOdd (by decide)]
  refine WP.mono (sel_ok h5 (by idx) (by idx) (by idx) hsOdd
    (by rw [od5, o1]; omega_arith) (.inl (by idx))) fun t6 ⟨h6, k6, e6, r6⟩ => ?_
  refine WP.mono (halfModP_ok h6 hN15 (by idx)) fun t ⟨h7, k7, e7, r7⟩ => ?_
  refine ⟨h7, k1.mono.trans (k2.mono.trans (k3.mono.trans (k4.mono.trans (k5.mono.trans (k6.mono.trans
    k7.mono))))), fun hNM hZ l2 l3 => ?_, r1.trans (r2.trans (r3.trans ((r4.mono (by decide)).trans ((r5.mono (by decide)).trans ((r6.mono (by decide)).trans r7)))))⟩
  -- What each step left that the others keep.
  have m1 : num t1.mem B (kw len) aM = num s.mem B (kw len) aM := k1.num (by idx) (by idx) fM
  have nm1 : num t1.mem B (kw len) aNM = num s.mem B (kw len) aNM := k1.num (by idx) (by idx) fNM
  have z1 : num t1.mem B (kw len) aZero = num s.mem B (kw len) aZero := k1.num (by idx) (by idx) fZ
  have x1 : num t1.mem B (kw len) (A + 2) = num s.mem B (kw len) (A + 2) := k1.num (by idx) (by idx) fA2
  have x2 : num t1.mem B (kw len) (A + 3) = num s.mem B (kw len) (A + 3) := k1.num (by idx) (by idx) fA3
  have m2 : num t2.mem B (kw len) aM = num s.mem B (kw len) aM := by rw [k2.num (by idx) (by idx) fM, m1]
  have nm2 : num t2.mem B (kw len) aNM = num s.mem B (kw len) aNM := by rw [k2.num (by idx) (by idx) fNM, nm1]
  have z2 : num t2.mem B (kw len) aZero = num s.mem B (kw len) aZero := by rw [k2.num (by idx) (by idx) fZ, z1]
  have x12 : num t2.mem B (kw len) (A + 2) = num s.mem B (kw len) (A + 2) := by rw [k2.num (by idx) (by idx) fA2, x1]
  have x22 : num t2.mem B (kw len) (A + 3) = num s.mem B (kw len) (A + 3) := by rw [k2.num (by idx) (by idx) fA3, x2]
  have E1 := e2 (by rw [nm1, m1]; exact hNM) (by rw [z1]; exact hZ) (by rw [x1, m1]; exact l2) (by rw [x2, m1]; exact l3)
  have E2 := e3 (by rw [nm2, m2]; exact hNM) (by rw [z2]; exact hZ) (by rw [x22, m2]; exact l3)
    (by rw [x12, m2]; exact l2)
  rw [m1, x1, x2] at E1
  rw [m2, x12, x22] at E2
  -- The state at `t6`, and the halving.
  have m6 : num t6.mem B (kw len) aM = num s.mem B (kw len) aM := by
    rw [k6.num (by idx) (by idx) fM, k5.num (by idx) (by idx) fM, k4.num (by idx) (by idx) fM,
      k3.num (by idx) (by idx) fM, m2]
  have nm6 : num t6.mem B (kw len) aNM = num s.mem B (kw len) aNM := by
    rw [k6.num (by idx) (by idx) fNM, k5.num (by idx) (by idx) fNM, k4.num (by idx) (by idx) fNM,
      k3.num (by idx) (by idx) fNM, nm2]
  have z6 : num t6.mem B (kw len) aZero = num s.mem B (kw len) aZero := by
    rw [k6.num (by idx) (by idx) fZ, k5.num (by idx) (by idx) fZ, k4.num (by idx) (by idx) fZ,
      k3.num (by idx) (by idx) fZ, z2]
  have H := e7 (by rw [nm6, m6]; exact hNM) (by rw [z6]; exact hZ)
  rw [m6, e6, od5, o1, k5.num (by idx) (by idx) fA2, k4.num (by idx) (by idx) fA2, k3.num (by idx) (by idx) fA2,
    x12, e5, k4.slot hsC (by simp), cs3, c1, k4.num (by idx) (by idx) fT3, k4.num (by idx) (by idx) fT2,
    k3.num (by idx) (by idx) fT3, E1, E2] at H
  have U : num t.mem B (kw len) D = num t1.mem B (kw len) D := by
    rw [k7.num (by idx) (by idx) fD, k6.num (by idx) (by idx) fD, k5.num (by idx) (by idx) fD,
      k4.num (by idx) (by idx) fD, k3.num (by idx) (by idx) fD, k2.num (by idx) (by idx) fD]
  have V : num t.mem B (kw len) (D + 1) = num t1.mem B (kw len) (D + 1) := by
    rw [k7.num (by idx) (by idx) fD1, k6.num (by idx) (by idx) fD1, k5.num (by idx) (by idx) fD1,
      k4.num (by idx) (by idx) fD1, k3.num (by idx) (by idx) fD1, k2.num (by idx) (by idx) fD1]
  have X2 : num t.mem B (kw len) (D + 3) = num t4.mem B (kw len) (D + 3) := by
    rw [k7.num (by idx) (by idx) fD3, k6.num (by idx) (by idx) fD3, k5.num (by idx) (by idx) fD3]
  rw [e4, cs3, c1, k3.num (by idx) (by idx) fA3, k3.num (by idx) (by idx) fA2, x12, x22] at X2
  rw [bank, bank, U, V, X2, u1, v1, show D + 2 = D + 2 from rfl, H]
  exact invStep_arith

end VG.Proof.Rsa.X86.KeyRt

end

end


/-! # The inverse at a run-time width: `32 w` iterations of two steps

`inverse_ok`: for the run-time width's `inverse` on `RtWs`, from
`(a, m, 1, 0)` in arrays 0–3, for an odd `m > 1`, array 1 ends as
`gcd(a, m)` and array 3 as `x < m` with `x a ≡ gcd(a, m) (mod m)`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S slot bank invArrs invSlots)
open VG.Impl.Rsa.X86.Keys (aM aNM aZero aT1 aT2 aT3 aT4 sOdd sB sC sT hdr)
open VG.Proof.Rsa (invIter InvI)

variable {L : Lay}

/-- The state after `i` iterations. -/
structure InvLoopI (L : Lay) (s0 : State) (B : Addr) (Z len N : Nat) (i : Nat) (t : State) : Prop where
  ws : RtWs L t B Z len N
  keep : Keep B (kw len) invArrs invSlots s0.mem t.mem
  rest : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s0 t
  count : t.gpr .esi = BitVec.ofNat 32 (32 * kw len - i)
  value : num s0.mem B (kw len) aNM + num s0.mem B (kw len) aM = 2 ^ (32 * kw len) → num s0.mem B (kw len) aZero = 0 →
    num s0.mem B (kw len) aM % 2 = 1 → 1 < num s0.mem B (kw len) aM →
    bank s0.mem B (kw len) 0 = (num s0.mem B (kw len) 0, num s0.mem B (kw len) aM, 1, 0) →
    bank t.mem B (kw len) 0 = invIter (num s0.mem B (kw len) aM) (2 * i) (bank s0.mem B (kw len) 0)

theorem inverseBody_ok {s0 t : State} {B : Addr} {Z len N i : Nat} (hN15 : 15 ≤ N) 
    (inv : InvLoopI L s0 B Z len N i t) (hi : i < 32 * kw len) :
    WP isa (.seq (VG.Impl.Rsa.X86.KeyRt.invStep L 0 4) (.seq (VG.Impl.Rsa.X86.KeyRt.invStep L 4 0)
      (.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)]))) t fun u =>
      InvLoopI L s0 B Z len N (i + 1) u ∧ u.zf = some (decide (i + 1 = 32 * kw len)) := by
  have h := inv.ws
  have wle := h.ws.wle
  have fM := h.ws.fit64 (j := aM) (by idx)
  have fNM := h.ws.fit64 (j := aNM) (by idx)
  have fZ := h.ws.fit64 (j := aZero) (by idx)
  have f0 := h.ws.fit64 (j := 0) (by idx)
  have keepM : ∀ {m m' : Mem} {js ds : List Nat}, Keep B (kw len) js ds m m' → (∀ k ∈ js, k ≠ aM ∧ k ≠ aNM ∧ k ≠ aZero) →
      (∀ d ∈ ds, d + 4 ≤ hdr) → num m' B (kw len) aM = num m B (kw len) aM ∧ num m' B (kw len) aNM = num m B (kw len) aNM ∧
        num m' B (kw len) aZero = num m B (kw len) aZero := fun k hk hd =>
    ⟨k.num (fun x hx => (hk x hx).1) hd fM, k.num (fun x hx => (hk x hx).2.1) hd fNM,
      k.num (fun x hx => (hk x hx).2.2) hd fZ⟩
  rw [WP.seq_iff]
  refine WP.mono (invStep_ok h hN15 (.inl ⟨rfl, rfl⟩)) fun t1 ⟨h1, k1, e1, r1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (invStep_ok h1 hN15 (.inr ⟨rfl, rfl⟩)) fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  refine WP.mono (Div.count_ok t2) fun u ⟨countU, hz, m2, r3⟩ => ?_
  have r6 : t2.gpr .esi = t.gpr .esi := (r2.1 _ (by decide)).trans (r1.1 _ (by decide))
  refine ⟨⟨h2.keep r3 (by decide) (by decide) (by rw [m2]; exact Outside.refl _ _ _ _), ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [m2]; exact inv.keep.trans (k1.mono.trans k2.mono)
  · exact inv.rest.trans ((r1.mono (by decide)).trans ((r2.mono (by decide)).trans (r3.mono (by decide))))
  · rw [countU, r6, inv.count]
    change BitVec.ofNat 32 (32 * kw len - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [hi])]
    congr 1
  · intro hNM hZ hodd h1M hst
    have prev := inv.value hNM hZ hodd h1M hst
    obtain ⟨m0, n0, z0⟩ := keepM inv.keep (by idx) (by idx)
    obtain ⟨m1, n1, z1⟩ := keepM k1 (by idx) (by idx)
    have I := VG.Proof.Rsa.invIter_inv hodd (VG.Proof.Rsa.invI_start' (a := num s0.mem B (kw len) 0) hodd h1M) (2 * i)
    rw [← hst, ← prev] at I
    have s1 := e1 (by rw [n0, m0]; exact hNM) (by rw [z0]; exact hZ)
      (by rw [m0]; exact I.x₁_lt) (by rw [m0]; exact I.x₂_lt)
    rw [m0] at s1
    have I1 := VG.Proof.Rsa.invStep_inv hodd I
    rw [← s1] at I1
    have s2 := e2 (by rw [n1, m1, n0, m0]; exact hNM) (by rw [z1, z0]; exact hZ)
      (by rw [m1, m0]; exact I1.x₁_lt) (by rw [m1, m0]; exact I1.x₂_lt)
    rw [m1, m0, s1, prev] at s2
    rw [m2, s2, show 2 * (i + 1) = 2 * i + 1 + 1 by omega_using []]
    rfl
  · rw [hz, r6, inv.count]
    change some (BitVec.ofNat 32 (32 * kw len - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [hi]), ofNat_beq_zero (by omega_using [wle])]
    simp only [show 32 * kw len - i - 1 = 0 ↔ i + 1 = 32 * kw len by omega_using [hi]]

theorem inverse_ok {s : State} {B : Addr} {Z len N : Nat} (h : RtWs L s B Z len N) (hN15 : 15 ≤ N) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.inverse L) s fun t => RtWs L t B Z len N ∧
      Keep B (kw len) invArrs invSlots s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t ∧
      (num s.mem B (kw len) aNM + num s.mem B (kw len) aM = 2 ^ (32 * kw len) → num s.mem B (kw len) aZero = 0 →
        num s.mem B (kw len) aM % 2 = 1 → 1 < num s.mem B (kw len) aM →
        bank s.mem B (kw len) 0 = (num s.mem B (kw len) 0, num s.mem B (kw len) aM, 1, 0) →
        num t.mem B (kw len) 1 = Nat.gcd (num s.mem B (kw len) 0) (num s.mem B (kw len) aM) ∧
        (num s.mem B (kw len) aM : Int) ∣ (num t.mem B (kw len) 3 : Int) * num s.mem B (kw len) 0 - num t.mem B (kw len) 1 ∧
        num t.mem B (kw len) 3 < num s.mem B (kw len) aM) := by
  unfold VG.Impl.Rsa.X86.KeyRt.inverse
  refine WP.seq ?_
  rw [show bits L = bits L ++ [] from (List.append_nil _).symm]
  refine bits_ok h fun s1 u1 m1 e1 => WP.block_nil ?_
  have h1 := h.keep u1 (by decide) (by decide) (by rw [m1]; exact Outside.refl _ _ _ _)
  have wp := h.kw_pos
  have wl := h.ws.wle
  have start : InvLoopI L s B Z len N 0 s1 := ⟨h1, by rw [m1]; exact Keep.refl _ _ _ _ _,
    u1.mono (by decide), by rw [e1]; rfl, fun _ _ _ _ _ => by rw [m1]; rfl⟩
  refine WP.loop (M := isa) (fun k t => ∃ i, i + k = 32 * kw len ∧ 0 < k ∧ InvLoopI L s B Z len N i t) ?_
    (32 * kw len) s1 ⟨0, by omega_using [], by omega_using [wp], start⟩
  · intro k t ⟨i, hik, hk, inv⟩
    refine WP.mono (inverseBody_ok hN15 inv (by omega_using [hik, hk])) fun u ⟨iu, hz⟩ => ?_
    by_cases e : i + 1 = 32 * kw len
    · left
      refine ⟨by change u.zf.map not = some false; simp [hz, e], iu.ws, iu.keep, iu.rest, ?_⟩
      intro hNM hZ hodd h1M hst
      have v := iu.value hNM hZ hodd h1M hst
      rw [e, hst] at v
      have hm : 1 % num s.mem B (kw len) aM = 1 := Nat.mod_eq_of_lt h1M
      have D := VG.Proof.Rsa.invIter_done (a := num s.mem B (kw len) 0) (K := 2 * (32 * kw len)) hodd (by
        have := val32_lt s.mem B (arr (kw len) 0) (kw len)
        have := val32_lt s.mem B (arr (kw len) aM) (kw len)
        calc num s.mem B (kw len) 0 * num s.mem B (kw len) aM < 2 ^ (32 * kw len) * 2 ^ (32 * kw len) :=
              Nat.mul_lt_mul'' (by assumption) (by assumption)
          _ = 2 ^ (2 * (32 * kw len)) := by rw [← Nat.pow_add]; congr 1; omega_using [])
      rw [hm] at D
      dsimp only at D
      rw [← v] at D
      exact ⟨D.2.1, D.2.2.1, D.2.2.2⟩
    · right
      exact ⟨by change u.zf.map not = some true; simp [hz, e], k - 1, by omega_using [hk], i + 1, by omega_using [hik, hk], by omega_using [hik, hk, e], iu⟩

end VG.Proof.Rsa.X86.KeyRt
