module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Entry
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaKeyGen.Contract
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
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Word
public import VerifiedGarbage.Proof.Rsa.KeyMath
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Rsa.X86.DivCount
import Mathlib.Tactic.Widget.Calc
import VerifiedGarbage.Proof.Rsa.KeyBits32

/-! ### `Rsa.X86.KeyRt.InvLoop`, which this module and modules that import it used -/

section

/-! ### `Rsa.X86.KeyRt.InvParts`, which only this module used -/

section

/-! # The inverse's subtraction and halving modulo `m` at a run-time width

`subModP_ok` and `halfModP_ok` state what `Keys`' lemmas do, for the
run-time width's operations on `RtWs`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S slot wp_seqs_cons wp_seqs_append)
open VG.Impl.Rsa.X86.Keys (aM aNM aZero aT1 aT2 aT3 aT4 sOdd sB sC sT hdr seqs)
open VG.Proof.Rsa (subMod halfMod subMod_impl halfMod_impl)
open VG.Proof.Rsa.KeyBits32

variable {L : Lay}

theorem subModP_ok {s : State} {B : Addr} {Z len N o a b : Nat} (h : RtWs L s B Z len N)
    (hN15 : 15 ≤ N) (ho : o < N) (ha : a < N) (hb : b < N) :
    WP isa (seqs (subModP L o a b)) s fun t => RtWs L t B Z len N ∧ Keep B (kw len) [aT1, aT4, o] [sB] s.mem t.mem ∧
      (num s.mem B (kw len) aNM + num s.mem B (kw len) aM = 2 ^ (32 * kw len) → num s.mem B (kw len) aZero = 0 →
        num s.mem B (kw len) a < num s.mem B (kw len) aM → num s.mem B (kw len) b < num s.mem B (kw len) aM →
        num t.mem B (kw len) o = subMod (num s.mem B (kw len) aM) (num s.mem B (kw len) a) (num s.mem B (kw len) b)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have hsB : sB + 4 ≤ hdr := by decide
  unfold subModP
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h (by idx) ha hb) fun t1 ⟨h1, k1, v1, b1, r1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (storeSlot_ok h1 hsB .ebx) fun t2 ⟨h2, k2, s2, r2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok h2 (by idx) (by idx) (by idx) hsB (by rw [s2]; exact b1) (.inl (by idx)))
    fun t3 ⟨h3, k3, v3, r3⟩ => ?_
  refine WP.mono (sub3_ok h3 ho (by idx) (by idx)) fun t ⟨h4, k4, v4, b4, r4⟩ => ?_
  refine ⟨h4, Keep.join (k1.join k2 (js := [aT1, aT4, o]) (ds := [sB])) (k3.join k4 (js := [aT1, aT4, o]) (ds := [sB])),
    fun hNM hZ ha' hb' => ?_, (r1.mono (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans (r4.mono (by decide))))⟩
  -- The values at the later states.
  have fz := h.ws.fit64 (j := aZero) (by idx)
  have fn := h.ws.fit64 (j := aNM) (by idx)
  have fT1 := h.ws.fit64 (j := aT1) (by idx)
  have z3 : num t2.mem B (kw len) aZero = 0 := by
    rw [k2.num (by simp) (by simp; decide) fz, k1.num (by idx) (by simp) fz, hZ]
  have n3 : num t2.mem B (kw len) aNM = num s.mem B (kw len) aNM := by
    rw [k2.num (by simp) (by simp; decide) fn, k1.num (by idx) (by simp) fn]
  have t13 : num t3.mem B (kw len) aT1 = num t1.mem B (kw len) aT1 := by
    rw [k3.num (by idx) (by simp) fT1, k2.num (by simp) (by simp; decide) fT1]
  have ft4 := h.ws.fit64 (j := aT4) (by idx)
  rw [t13] at v4
  rw [s2, z3, n3] at v3
  refine subMod_impl (P := 2 ^ (32 * kw len)) (by omega_arith) hb' v1 (val32_lt _ _ _ _) b1 ?_ v4 (val32_lt _ _ _ _) b4
  rw [v3]
  split <;> omega_arith


/-- The halving of `[aT3]` modulo `m` into `[o]`. -/
def halfModP (L : Lay) (o : Nat) : List (Prog isa) := [
  .block (bitOf L sB aT3), sel L aT4 aZero aNM sB, sub3 L o aT3 aT4,
  .block [.alu .xor .ebx (.mem (VG.Impl.Mont.X86.sc sB))], half L o]

theorem halfModP_ok {s : State} {B : Addr} {Z len N o : Nat} (h : RtWs L s B Z len N)
    (hN15 : 15 ≤ N) (ho : o < N) :
    WP isa (seqs (halfModP L o)) s fun t => RtWs L t B Z len N ∧ Keep B (kw len) [aT4, o] [sB] s.mem t.mem ∧
      (num s.mem B (kw len) aNM + num s.mem B (kw len) aM = 2 ^ (32 * kw len) → num s.mem B (kw len) aZero = 0 →
        num t.mem B (kw len) o = halfMod (num s.mem B (kw len) aM) (num s.mem B (kw len) aT3)) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have hsB : sB + 4 ≤ hdr := by decide
  unfold halfModP
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (bitOf_ok h (by idx) hsB) fun t1 ⟨h1, k1, s1, r1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have b1 : slot t1.mem B sB ≤ 1 := by rw [s1]; omega_arith
  refine WP.mono (sel_ok h1 (by idx) (by idx) (by idx) hsB b1 (.inl (by idx)))
    fun t2 ⟨h2, k2, v2, r2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h2 ho (by idx) (by idx)) fun t3 ⟨h3, k3, v3, b3, r3⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine wp_logicS (.inr rfl) (readSrc_sc h3.ws.workspace (by have := h3.ws.hdr_le; unfold sB hdr at *; omega_arith))
    fun t4 u5 => WP.block_nil ?_
  have h5 := h3.keep u5.keeps (by decide) (by decide) (by rw [u5.mem]; exact Outside.refl _ _ _ _)
  have sB3 : slot t3.mem B sB = slot t1.mem B sB := by
    rw [k3.slot hsB (by simp), k2.slot hsB (by simp)]
  have c4 : (t4.gpr .ebx).toNat = ((t3.gpr .ebx).toNat + num s.mem B (kw len) aT3 % 2) % 2 := by
    rw [u5.gpr, ite_eq_right (by decide)]
    have e : (t3.mem.readW (off B sB) 32).toNat = num s.mem B (kw len) aT3 % 2 := by
      change slot t3.mem B sB = _; rw [sB3, s1]
    rw [bv_xor_bits b3 (by rw [e]; omega_arith), e]
  refine WP.mono (half_ok h5 ho (by rw [c4]; omega_arith)) fun t ⟨h6, k6, v6, r6⟩ => ?_
  have m4 : t4.mem = t3.mem := u5.mem
  rw [m4] at k6 v6
  refine ⟨h6, (k1.join k2 (js := [aT4, o]) (ds := [sB])).join (k3.join k6 (js := [aT4, o]) (ds := [sB]))
      (js := [aT4, o]) (ds := [sB]), fun hNM hZ => ?_,
    (r1.mono (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans ((u5.keeps.mono (by decide)).trans (r6.mono (by decide)))))⟩
  have f3 := h.ws.fit64 (j := aT3) (by idx)
  have fz := h.ws.fit64 (j := aZero) (by idx)
  have fn := h.ws.fit64 (j := aNM) (by idx)
  have x2 : num t2.mem B (kw len) aT3 = num s.mem B (kw len) aT3 := by
    rw [k2.num (by idx) (by simp) f3, k1.num (by simp) (by simp; decide) f3]
  have z1 : num t1.mem B (kw len) aZero = 0 := by rw [k1.num (by simp) (by simp; decide) fz, hZ]
  have n1 : num t1.mem B (kw len) aNM = num s.mem B (kw len) aNM := k1.num (by simp) (by simp; decide) fn
  rw [x2] at v3
  rw [s1, z1, n1] at v2
  rw [v6, c4]
  refine halfMod_impl (P := 2 ^ (32 * kw len)) (by omega_arith) (val32_lt _ _ _ _) ?_ v3 (val32_lt _ _ _ _) b3 rfl
  rw [v2]; split <;> omega_arith


end VG.Proof.Rsa.X86.KeyRt

end

end

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

/-- A selection by a flag that is 1 when `c`: stated here, outside `invU_ok`'s hundred hypotheses. -/
private theorem sel_flag (c : Prop) [Decidable c] (u v : Nat) :
    (if (if c then 1 else 0) = 0 then v else u) = if c then u else v := by
  split <;> simp_all

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
  obtain hsOdd : sOdd + 4 ≤ hdr := by decide
  obtain hsB : sB + 4 ≤ hdr := by decide
  obtain hsC : sC + 4 ≤ hdr := by decide
  obtain fA := h.ws.fit64 (j := A) (by idx)
  obtain fA1 := h.ws.fit64 (j := A + 1) (by idx)
  obtain fT1 := h.ws.fit64 (j := aT1) (by idx)
  obtain fT2 := h.ws.fit64 (j := aT2) (by idx)
  obtain fT3 := h.ws.fit64 (j := aT3) (by idx)
  obtain fD1 := h.ws.fit64 (j := D + 1) (by idx)
  generalize hu : num s.mem B (kw len) A = u
  generalize hv : num s.mem B (kw len) (A + 1) = v
  unfold invU
  -- 1: the low bit of `u`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (bitOf_ok h (by idx) hsOdd) fun t1 ⟨h1, k1, o1, r1⟩ => ?_
  rw [hu] at o1
  obtain u1 : num t1.mem B (kw len) A = u := by rw [k1.num (by simp) (by simp; decide) fA, hu]
  obtain v1 : num t1.mem B (kw len) (A + 1) = v := by rw [k1.num (by simp) (by simp; decide) fA1, hv]
  -- 2: `u - v`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h1 (by idx) (by idx) (by idx)) fun t2 ⟨h2, k2, d2, b2, r2⟩ => ?_
  rw [u1, v1] at d2
  -- 3: the masks.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.block_append (WP.mono (storeSlot_ok h2 hsB .ebx) fun t3' ⟨h3', k3', sB3, r3'⟩ => ?_)
  obtain o3 : slot t3'.mem B sOdd = u % 2 := by
    rw [k3'.slot hsOdd (by decide), k2.slot hsOdd (by simp), o1]
  refine WP.mono (andS_ok h3' hsC hsOdd hsB (by rw [o3]; omega_arith) (by rw [sB3]; exact b2)) fun t3 ⟨h3, k3, c3, r3⟩ => ?_
  rw [o3, sB3] at c3
  obtain lt : (t2.gpr .ebx).toNat = 1 ↔ u < v := by
    have := borrow_iff d2 (val32_lt _ _ _ _) b2; omega_arith
  obtain c3' : slot t3.mem B sC = (if u % 2 = 1 ∧ u < v then 1 else 0) := by
    rw [c3]; by_cases e : u < v <;> simp [e, lt]
  obtain K3 : Keep B (kw len) [] [sB, sC] t2.mem t3.mem := k3'.join k3
  obtain o3' : slot t3.mem B sOdd = u % 2 := by rw [k3.slot hsOdd (by decide), o3]
  obtain u3 : num t3.mem B (kw len) A = u := by
    rw [K3.num (by simp) (by simp; decide) fA, k2.num (by idx) (by simp) fA, u1]
  obtain v3 : num t3.mem B (kw len) (A + 1) = v := by
    rw [K3.num (by simp) (by simp; decide) fA1, k2.num (by idx) (by simp) fA1, v1]
  -- 4: `v - u`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h3 (by idx) (by idx) (by idx)) fun t4 ⟨h4, k4, d4, b4, r4⟩ => ?_
  rw [u3, v3] at d4
  obtain cs4 : slot t4.mem B sC = (if u % 2 = 1 ∧ u < v then 1 else 0) := by
    rw [k4.slot hsC (by simp), c3']
  obtain cb4 : slot t4.mem B sC ≤ 1 := by rw [cs4]; split <;> omega_arith
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
  obtain od6 : slot t6.mem B sOdd = u % 2 := by
    rw [k6.slot hsOdd (by simp), k5.slot hsOdd (by simp), k4.slot hsOdd (by simp), o3']
  refine WP.mono (sel_ok h6 (by idx) (by idx) (by idx) hsOdd
    (by rw [od6]; omega_arith) (.inl (by idx))) fun t7 ⟨h7, k7, e7, r7⟩ => ?_
  rw [od6, e6, k6.num (by idx) (by simp) fA, k5.num (by idx) (by simp) fA, k4.num (by idx) (by simp) fA, u3] at e7
  -- 8, 9: the halving.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine wp_movS rfl fun t8 u8 _ => WP.block_nil ?_
  obtain h8 := h7.keep u8.keeps (by decide) (by decide) (by rw [u8.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (half_ok h8 (by idx) (by rw [u8.gpr]; decide)) fun t ⟨h9, k9, e9, r9⟩ => ?_
  rw [u8.gpr, u8.mem] at e9
  rw [u8.mem] at k9
  refine ⟨h9, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact k1.mono.trans (k2.mono.trans (K3.mono.trans (k4.mono.trans (k5.mono.trans (k6.mono.trans
      (k7.mono.trans k9.mono))))))
  · rw [k9.slot hsOdd (by simp), k7.slot hsOdd (by simp), od6]
  · rw [k9.slot hsC (by simp), k7.slot hsC (by simp), k6.slot hsC (by simp), k5.slot hsC (by simp), cs4]
  · rw [k9.num (by idx) (by simp) fD1, k7.num (by idx) (by simp) fD1, k6.num (by idx) (by simp) fD1, e5]
    exact sel_flag _ _ _
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
  obtain hsOdd : sOdd + 4 ≤ hdr := by decide
  obtain hsC : sC + 4 ≤ hdr := by decide
  obtain fA2 := h.ws.fit64 (j := A + 2) (by idx)
  obtain fA3 := h.ws.fit64 (j := A + 3) (by idx)
  obtain fM := h.ws.fit64 (j := aM) (by idx)
  obtain fNM := h.ws.fit64 (j := aNM) (by idx)
  obtain fZ := h.ws.fit64 (j := aZero) (by idx)
  obtain fT1 := h.ws.fit64 (j := aT1) (by idx)
  obtain fT2 := h.ws.fit64 (j := aT2) (by idx)
  obtain fT3 := h.ws.fit64 (j := aT3) (by idx)
  obtain fD := h.ws.fit64 (j := D) (by idx)
  obtain fD1 := h.ws.fit64 (j := D + 1) (by idx)
  obtain fD3 := h.ws.fit64 (j := D + 3) (by idx)
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
  obtain cs3 : slot t3.mem B sC = slot t1.mem B sC := by
    rw [k3.slot hsC (by decide), k2.slot hsC (by decide)]
  obtain cb3 : slot t3.mem B sC ≤ 1 := by rw [cs3, c1]; split <;> omega_arith
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok h3 (by idx) (by idx) (by idx) hsC cb3 (.inl (by idx))) fun t4 ⟨h4, k4, e4, r4⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok h4 (by idx) (by idx) (by idx) hsC
    (by rw [k4.slot hsC (by simp)]; exact cb3) (.inl (by idx))) fun t5 ⟨h5, k5, e5, r5⟩ => ?_
  obtain od5 : slot t5.mem B sOdd = slot t1.mem B sOdd := by
    rw [k5.slot hsOdd (by simp), k4.slot hsOdd (by simp), k3.slot hsOdd (by decide), k2.slot hsOdd (by decide)]
  refine WP.mono (sel_ok h5 (by idx) (by idx) (by idx) hsOdd
    (by rw [od5, o1]; omega_arith) (.inl (by idx))) fun t6 ⟨h6, k6, e6, r6⟩ => ?_
  refine WP.mono (halfModP_ok h6 hN15 (by idx)) fun t ⟨h7, k7, e7, r7⟩ => ?_
  refine ⟨h7, k1.mono.trans (k2.mono.trans (k3.mono.trans (k4.mono.trans (k5.mono.trans (k6.mono.trans
    k7.mono))))), fun hNM hZ l2 l3 => ?_, r1.trans (r2.trans (r3.trans ((r4.mono (by decide)).trans ((r5.mono (by decide)).trans ((r6.mono (by decide)).trans r7)))))⟩
  -- What each step left that the others keep.
  obtain m1 : num t1.mem B (kw len) aM = num s.mem B (kw len) aM := k1.num (by idx) (by idx) fM
  obtain nm1 : num t1.mem B (kw len) aNM = num s.mem B (kw len) aNM := k1.num (by idx) (by idx) fNM
  obtain z1 : num t1.mem B (kw len) aZero = num s.mem B (kw len) aZero := k1.num (by idx) (by idx) fZ
  obtain x1 : num t1.mem B (kw len) (A + 2) = num s.mem B (kw len) (A + 2) := k1.num (by idx) (by idx) fA2
  obtain x2 : num t1.mem B (kw len) (A + 3) = num s.mem B (kw len) (A + 3) := k1.num (by idx) (by idx) fA3
  obtain m2 : num t2.mem B (kw len) aM = num s.mem B (kw len) aM := by rw [k2.num (by idx) (by idx) fM, m1]
  obtain nm2 : num t2.mem B (kw len) aNM = num s.mem B (kw len) aNM := by rw [k2.num (by idx) (by idx) fNM, nm1]
  obtain z2 : num t2.mem B (kw len) aZero = num s.mem B (kw len) aZero := by rw [k2.num (by idx) (by idx) fZ, z1]
  obtain x12 : num t2.mem B (kw len) (A + 2) = num s.mem B (kw len) (A + 2) := by rw [k2.num (by idx) (by idx) fA2, x1]
  obtain x22 : num t2.mem B (kw len) (A + 3) = num s.mem B (kw len) (A + 3) := by rw [k2.num (by idx) (by idx) fA3, x2]
  obtain E1 := e2 (by rw [nm1, m1]; exact hNM) (by rw [z1]; exact hZ) (by rw [x1, m1]; exact l2) (by rw [x2, m1]; exact l3)
  obtain E2 := e3 (by rw [nm2, m2]; exact hNM) (by rw [z2]; exact hZ) (by rw [x22, m2]; exact l3)
    (by rw [x12, m2]; exact l2)
  rw [m1, x1, x2] at E1
  rw [m2, x12, x22] at E2
  -- The state at `t6`, and the halving.
  obtain m6 : num t6.mem B (kw len) aM = num s.mem B (kw len) aM := by
    rw [k6.num (by idx) (by idx) fM, k5.num (by idx) (by idx) fM, k4.num (by idx) (by idx) fM,
      k3.num (by idx) (by idx) fM, m2]
  obtain nm6 : num t6.mem B (kw len) aNM = num s.mem B (kw len) aNM := by
    rw [k6.num (by idx) (by idx) fNM, k5.num (by idx) (by idx) fNM, k4.num (by idx) (by idx) fNM,
      k3.num (by idx) (by idx) fNM, nm2]
  obtain z6 : num t6.mem B (kw len) aZero = num s.mem B (kw len) aZero := by
    rw [k6.num (by idx) (by idx) fZ, k5.num (by idx) (by idx) fZ, k4.num (by idx) (by idx) fZ,
      k3.num (by idx) (by idx) fZ, z2]
  obtain H := e7 (by rw [nm6, m6]; exact hNM) (by rw [z6]; exact hZ)
  rw [m6, e6, od5, o1, k5.num (by idx) (by idx) fA2, k4.num (by idx) (by idx) fA2, k3.num (by idx) (by idx) fA2,
    x12, e5, k4.slot hsC (by simp), cs3, c1, k4.num (by idx) (by idx) fT3, k4.num (by idx) (by idx) fT2,
    k3.num (by idx) (by idx) fT3, E1, E2] at H
  obtain U : num t.mem B (kw len) D = num t1.mem B (kw len) D := by
    rw [k7.num (by idx) (by idx) fD, k6.num (by idx) (by idx) fD, k5.num (by idx) (by idx) fD,
      k4.num (by idx) (by idx) fD, k3.num (by idx) (by idx) fD, k2.num (by idx) (by idx) fD]
  obtain V : num t.mem B (kw len) (D + 1) = num t1.mem B (kw len) (D + 1) := by
    rw [k7.num (by idx) (by idx) fD1, k6.num (by idx) (by idx) fD1, k5.num (by idx) (by idx) fD1,
      k4.num (by idx) (by idx) fD1, k3.num (by idx) (by idx) fD1, k2.num (by idx) (by idx) fD1]
  obtain X2 : num t.mem B (kw len) (D + 3) = num t4.mem B (kw len) (D + 3) := by
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
  obtain fM := h.ws.fit64 (j := aM) (by idx)
  obtain fNM := h.ws.fit64 (j := aNM) (by idx)
  obtain fZ := h.ws.fit64 (j := aZero) (by idx)
  obtain f0 := h.ws.fit64 (j := 0) (by idx)
  obtain keepM : ∀ {m m' : Mem} {js ds : List Nat}, Keep B (kw len) js ds m m' → (∀ k ∈ js, k ≠ aM ∧ k ≠ aNM ∧ k ≠ aZero) →
      (∀ d ∈ ds, d + 4 ≤ hdr) → num m' B (kw len) aM = num m B (kw len) aM ∧ num m' B (kw len) aNM = num m B (kw len) aNM ∧
        num m' B (kw len) aZero = num m B (kw len) aZero := fun k hk hd =>
    ⟨k.num (fun x hx => (hk x hx).1) hd fM, k.num (fun x hx => (hk x hx).2.1) hd fNM,
      k.num (fun x hx => (hk x hx).2.2) hd fZ⟩
  rw [WP.seq_iff]
  refine WP.mono (invStep_ok h hN15 (.inl ⟨rfl, rfl⟩)) fun t1 ⟨h1, k1, e1, r1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (invStep_ok h1 hN15 (.inr ⟨rfl, rfl⟩)) fun t2 ⟨h2, k2, e2, r2⟩ => ?_
  refine WP.mono (Div.count_ok t2) fun u ⟨countU, hz, m2, r3⟩ => ?_
  obtain r6 : t2.gpr .esi = t.gpr .esi := (r2.1 _ (by decide)).trans (r1.1 _ (by decide))
  refine ⟨⟨h2.keep r3 (by decide) (by decide) (by rw [m2]; exact Outside.refl _ _ _ _), ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [m2]; exact inv.keep.trans (k1.mono.trans k2.mono)
  · exact inv.rest.trans ((r1.mono (by decide)).trans ((r2.mono (by decide)).trans (r3.mono (by decide))))
  · rw [countU, r6, inv.count]
    change BitVec.ofNat 32 (32 * kw len - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [hi])]
    congr 1
  · intro hNM hZ hodd h1M hst
    obtain prev := inv.value hNM hZ hodd h1M hst
    obtain ⟨m0, n0, z0⟩ := keepM inv.keep (by idx) (by idx)
    obtain ⟨m1, n1, z1⟩ := keepM k1 (by idx) (by idx)
    obtain I := VG.Proof.Rsa.invIter_inv hodd (VG.Proof.Rsa.invI_start' (a := num s0.mem B (kw len) 0) hodd h1M) (2 * i)
    rw [← hst, ← prev] at I
    obtain s1 := e1 (by rw [n0, m0]; exact hNM) (by rw [z0]; exact hZ)
      (by rw [m0]; exact I.x₁_lt) (by rw [m0]; exact I.x₂_lt)
    rw [m0] at s1
    obtain I1 := VG.Proof.Rsa.invStep_inv hodd I
    rw [← s1] at I1
    obtain s2 := e2 (by rw [n1, m1, n0, m0]; exact hNM) (by rw [z1, z0]; exact hZ)
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
  obtain h1 := h.keep u1 (by decide) (by decide) (by rw [m1]; exact Outside.refl _ _ _ _)
  have wp := h.kw_pos
  have wl := h.ws.wle
  obtain start : InvLoopI L s B Z len N 0 s1 := ⟨h1, by rw [m1]; exact Keep.refl _ _ _ _ _,
    u1.mono (by decide), by rw [e1]; rfl, fun _ _ _ _ _ => by rw [m1]; rfl⟩
  refine WP.loop (M := isa) (fun k t => ∃ i, i + k = 32 * kw len ∧ 0 < k ∧ InvLoopI L s B Z len N i t) ?_
    (32 * kw len) s1 ⟨0, by omega_using [], by omega_using [wp], start⟩
  · intro k t ⟨i, hik, hk, inv⟩
    refine WP.mono (inverseBody_ok hN15 inv (by omega_using [hik, hk])) fun u ⟨iu, hz⟩ => ?_
    by_cases e : i + 1 = 32 * kw len
    · left
      refine ⟨by change u.zf.map not = some false; simp [hz, e], iu.ws, iu.keep, iu.rest, ?_⟩
      intro hNM hZ hodd h1M hst
      obtain v := iu.value hNM hZ hodd h1M hst
      rw [e, hst] at v
      obtain hm : 1 % num s.mem B (kw len) aM = 1 := Nat.mod_eq_of_lt h1M
      obtain D := VG.Proof.Rsa.invIter_done (a := num s.mem B (kw len) 0) (K := 2 * (32 * kw len)) hodd (by
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

end

end

/-! # `vg_rsa_keygen_inverse` runs `KeyRt.inverse` in its frame and restores the caller's registers -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Inverse
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Proof.Rsa.X86.KeyRt (RtWs kw)
open VG.Proof.Rsa.X86.Keys (Keep num invArrs invSlots)
open VG.Impl.Rsa.X86.Keys (aM aNM aZero)

/-- What the inversion leaves: its frame in the working space, and the gcd and coefficient. -/
structure Done (s t : State) : Prop where
  keep : Keep (base s) (kw (len s)) invArrs invSlots (Compact.entered s).mem t.mem
  gcd : num t.mem (base s) (kw (len s)) 1 =
    Nat.gcd (num s.mem (base s) (kw (len s)) 0) (num s.mem (base s) (kw (len s)) aM)
  bezout : (num s.mem (base s) (kw (len s)) aM : Int) ∣
    (num t.mem (base s) (kw (len s)) 3 : Int) * num s.mem (base s) (kw (len s)) 0 - num t.mem (base s) (kw (len s)) 1
  lt : num t.mem (base s) (kw (len s)) 3 < num s.mem (base s) (kw (len s)) aM

theorem inner_noSp : NoSp (.seq (.block (VG.Impl.Rsa.X86.KeyRt.restoreEdi VG.Impl.RsaKeyGen.X86.Inverse.lay))
    (.seq (VG.Impl.Rsa.X86.KeyRt.inverse VG.Impl.RsaKeyGen.X86.Inverse.lay) (.block Compact.restoreRegs))) :=
  NoSp.of_all (by decide +kernel)

theorem framed_ok {s : State} (h : contract.pre s) :
    WP isa VG.Impl.RsaKeyGen.X86.Inverse.code s fun t => abiPreserved s t ∧
      ∃ t₀, Done s t₀ ∧ Frame [below (s.gpr .esp) 16] t₀.mem t.mem := by
  obtain A := entry h
  obtain fit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega_using [this]
  obtain frameWs : (below (s.gpr .esp) 16).Disjoint ⟨base s, size s⟩ := by
    unfold below
    rw [Taint.sub_setWidth fit]
    exact A.stackWs.sub_left (Offset.sub_below _ (by decide) (by decide))
  unfold VG.Impl.RsaKeyGen.X86.Inverse.code
  refine WP.frame (rs := Compact.savedRegisters) (by decide) (by decide) (by decide) fit inner_noSp ?_
  refine WP.seq (WP.mono (start_ok A) fun u ⟨H, mu, Ku⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Rsa.X86.KeyRt.inverse_ok H (by decide)) fun v ⟨Hv, Kv, KRv, res⟩ => ?_)
  have hws := H.ws
  obtain O : Outside (base s) 0 (size s) u.mem v.mem :=
    VG.Proof.Rsa.X86.KeyRt.keep_outside hws Kv (by decide) (by decide)
  obtain FV : Frame [⟨base s, size s⟩] u.mem v.mem := by
    obtain F := VG.Proof.Bignum.outside_frame O (by have := A.wsFit; unfold size at *; omega_using [])
    simpa only [off, BitVec.add_zero] using F
  obtain spV : v.gpr .esp = (Compact.entered s).gpr .esp := by
    rw [KRv.1 .esp (by decide), Ku.1 .esp (by decide)]
  obtain pFit : ((Compact.entered s).gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    rw [Compact.entered, pushed_esp, show 4 * Compact.savedRegisters.length = 16 from rfl,
      BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := (s.gpr .esp).isLt
    omega_using [fit]
  obtain frameAt : below (s.gpr .esp) 16 = ⟨((Compact.entered s).gpr .esp).setWidth 64, 16⟩ := by
    rw [Compact.entered, pushed_esp]; rfl
  have word (i : Nat) (hi : i < 4) : v.mem.readW (addr ((Compact.entered s).gpr .esp) (4 * i)) 32 =
      s.gpr (Compact.savedRegisters[3 - i]'(by change 3 - i < 4; omega_using [])) := by
    obtain same := FV.readW (r := below (s.gpr .esp) 16) (a := addr ((Compact.entered s).gpr .esp) (4 * i))
      (w := 32) (by rw [frameAt, addr_eq (by omega_using [pFit, hi])]; exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact frameWs) (by decide)
    rw [same, mu]
    exact pushed_word (rs := Compact.savedRegisters) (s := s) (by decide) fit hi
  have read (i : Nat) (hi : i < 4) : readSrc v (.mem (at_ .esp (4 * i))) = some
      (s.gpr (Compact.savedRegisters[3 - i]'(by change 3 - i < 4; omega_using []))) := by
    obtain access : InRegions (v.rd ++ v.wr) (addr (v.gpr .esp) (4 * i)) 4 := by
      rw [KRv.2.1, KRv.2.2, Ku.2.1, Ku.2.2, spV]
      refine ⟨below (s.gpr .esp) 16, List.mem_append_right _ List.mem_cons_self, ?_⟩
      rw [frameAt, addr_eq (by omega_using [pFit, hi])]
      exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
    change v.load32 (addr (v.gpr .esp) (4 * i)) = _
    rw [State.load32, ite_eq_left access, spV, word i hi]
  refine WP.mono (Compact.restore_ok (read 0 (by decide)) (read 1 (by decide)) (read 2 (by decide))) ?_
  rintro w ⟨edi, esi, ebp, memory, keep⟩
  obtain spW : w.gpr .esp = (Compact.entered s).gpr .esp := (keep.1 .esp (by decide)).trans spV
  obtain separate : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (below (s.gpr .esp) 16) := by
    unfold below
    rw [Taint.sub_setWidth fit]
    exact Offset.base_disjoint_below _ (by decide)
  obtain returnSame : v.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
    obtain same := FV.readW (w := 32) (Region.contains_self ((s.gpr .esp).setWidth 64) 4)
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact A.returnWs) (by decide)
    rw [same, mu]
    obtain pushed := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) fit
    exact pushed.readW (w := 32) (Region.contains_self _ _)
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate) (by decide)
  obtain mem0 := A.entered_num (j := 0) (by decide)
  obtain memM := A.entered_num (j := aM) (by decide)
  have premises := res
    (by
      rw [mu, A.entered_num (j := aNM) (by decide), memM, ← inverseNum_num, ← inverseNum_num]
      unfold aNM aM
      rw [A.negated]
      simp only [kw, Spec.Rsa.modulusWords, Proof.RsaKeyGen.inverseBytes]
      congr 1; omega_using [])
    (by rw [mu, A.entered_num (j := aZero) (by decide), ← inverseNum_num]; exact A.zero)
    (by rw [mu, memM, ← inverseNum_num]; exact A.odd)
    (by rw [mu, memM, ← inverseNum_num]; exact A.large)
    (by
      simp only [VG.Proof.Rsa.X86.Keys.bank, Nat.zero_add]
      rw [mu, A.entered_num (j := 1) (by decide), A.entered_num (j := 2) (by decide),
        A.entered_num (j := 3) (by decide), mem0, memM, ← inverseNum_num, ← inverseNum_num,
        ← inverseNum_num, ← inverseNum_num, ← inverseNum_num]
      unfold aM
      rw [A.v, A.x₁, A.x₂])
  rw [mu, mem0, memM] at premises
  obtain ⟨g, b, l⟩ := premises
  intro m _ fl
  refine ⟨⟨?_, ?_⟩, popped .ebx Compact.savedRegisters.length w, ⟨?_, ?_, ?_, ?_⟩, by rw [popped_mem]; exact fl⟩
  · intro r hr
    show (popped .ebx Compact.savedRegisters.length w).gpr r = _
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [show Compact.savedRegisters.length = 4 from rfl, Compact.popped_four_value, spW, memory]
      exact word 3 (by decide)
    · rw [popped_gpr _ _ _ (by decide) (by decide)]
      exact esi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]
      exact edi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]
      exact ebp
    · rw [popped_esp, spW, Compact.entered, pushed_esp]
      exact BitVec.sub_add_cancel _ _
  · show m.readW _ _ = _
    rw [fl.readW (Region.contains_self _ _) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact separate) (by decide), memory]
    exact returnSame
  · rw [popped_mem, memory, ← mu]
    exact Kv
  · rw [popped_mem, memory]; exact g
  · rw [popped_mem, memory]; exact b
  · rw [popped_mem, memory]; exact l

end VG.Proof.RsaKeyGen.X86.Inverse
