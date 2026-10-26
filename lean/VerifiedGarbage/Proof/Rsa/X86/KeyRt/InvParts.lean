module

import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Half
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
public import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Rsa.KeyBits32
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Rsa.KeyMath
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Word

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
