module

import VerifiedGarbage.Proof.Rsa.MulModArithmetic
import VerifiedGarbage.Proof.Rsa.X86.InvParts
public import VerifiedGarbage.Impl.Rsa.X86.MulMod
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Proof.Rsa.X86.KeySelect
import VerifiedGarbage.Proof.Rsa.X86.KeySub
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import Mathlib.Basic.IsEmpty.Defs
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.TCB.X86.State
import VerifiedGarbage.Proof.Rsa.KeyMath

/-! # `addMod` on i686: `[o] = ([a] + [b]) mod [m]` -/

@[expose] public section

namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot

/-- A sum below `2 m` modulo `m`. -/
theorem mod_of_lt_two {x M : Nat} (h : x < 2 * M) : x % M = if x < M then x else x - M :=
  VG.Proof.Rsa.mod_of_lt_two h

/-- The arithmetic of `addMod`: the negation of `b`, the sum, and the difference with `m`. -/
theorem addMod_impl {P A Bv M N1 β1 T β2 U β3 : Nat} (hA : A < M) (hB : Bv < M) (hM : 2 * M ≤ P)
    (h1 : N1 + Bv = 0 + P * β1) (_hN1 : N1 < P) (hβ1 : β1 ≤ 1)
    (h2 : T + N1 = A + P * β2) (hT : T < P) (hβ2 : β2 ≤ 1)
    (h3 : U + M = T + P * β3) (hU : U < P) (hβ3 : β3 ≤ 1) :
    (if β3 = 0 then U else T) = (A + Bv) % M :=
  VG.Proof.Rsa.addMod_impl hA hB hM h1 _hN1 hβ1 h2 hT hβ2 h3 hU hβ3

theorem addMod_ok {s : State} {B : Addr} {Z w N o a b m z t : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hm : m < N) (hz : z < N) (ht : t + 2 < N)
    (htz : t ≠ z) (htb : t ≠ b) (hat : a ≠ t) (hat1 : a ≠ t + 1) (hmt : m ≠ t) (hmt1 : m ≠ t + 1)
    (hmt2 : m ≠ t + 2) :
    WP isa (seqs (addMod w o a b m z t)) s fun u => Ws u B Z w N ∧
      Keep B w [t, t + 1, t + 2, o] [sC] s.mem u.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx] s u ∧
      (num s.mem B w z = 0 → num s.mem B w a < num s.mem B w m → num s.mem B w b < num s.mem B w m →
        2 * num s.mem B w m ≤ 2 ^ (32 * w) →
        num u.mem B w o = (num s.mem B w a + num s.mem B w b) % num s.mem B w m) := by
  have hsC : sC + 4 ≤ hdr := by decide
  unfold addMod
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h (o := t) (a := z) (b := b) (by omega) hz hb htz htb)
    fun t1 ⟨h1, k1, v1, b1, r1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h1 (o := t + 1) (a := a) (b := t) (by omega) ha (by omega) (Ne.symm hat1)
    (by omega)) fun t2 ⟨h2, k2, v2, b2, r2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sub3_ok h2 (o := t + 2) (a := t + 1) (b := m) ht (by omega) hm (by omega)
    (Ne.symm hmt2)) fun t3 ⟨h3, k3, v3, b3, r3⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (store_slot h3 hsC .ebx) fun t4 ⟨h4, k4, s4, r4⟩ => ?_
  refine WP.mono (sel_ok h4 (o := o) (a := t + 2) (b := t + 1) (sl := sC) ho ht (by omega) hsC
    (by rw [s4]; exact b3)) fun u ⟨hu, k5, v5, r5⟩ => ?_
  refine ⟨hu, ((k1.mono.trans k2.mono).trans k3.mono).trans (k4.mono.trans k5.mono),
    r1.trans (r2.trans (r3.trans ((r4.mono (by simp)).trans (r5.mono (by simp))))), fun hZ hA hB hM => ?_⟩
  have fa := h.fit64 ha
  have fm := h.fit64 hm
  have ft1 := h.fit64 (j := t + 1) (by omega)
  have ft2 := h.fit64 (j := t + 2) (by omega)
  -- The values the later steps read.
  have a1 : num t1.mem B w a = num s.mem B w a := k1.num (by simp; omega) (by simp) fa
  have m2 : num t2.mem B w m = num s.mem B w m := by
    rw [k2.num (by simp; omega) (by simp) fm, k1.num (by simp; omega) (by simp) fm]
  have T3 : num t3.mem B w (t + 1) = num t2.mem B w (t + 1) := k3.num (by simp) (by simp) ft1
  have T4 : num t4.mem B w (t + 1) = num t2.mem B w (t + 1) := by
    rw [k4.num (by simp) (by simp; decide) ft1, T3]
  have U4 : num t4.mem B w (t + 2) = num t3.mem B w (t + 2) := k4.num (by simp) (by simp; decide) ft2
  rw [v5, s4, T4, U4]
  rw [hZ] at v1
  rw [a1] at v2
  rw [m2] at v3
  exact addMod_impl hA hB hM v1 (val32_lt _ _ _ _) b1 v2 (val32_lt _ _ _ _) b2 v3
    (val32_lt _ _ _ _) b3

end VG.Proof.Rsa.X86.Keys
