module

public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
public import VerifiedGarbage.Proof.Rsa.Arm.DivReduce
import VerifiedGarbage.Proof.Rsa.Arm.DivLoop
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Rsa.KeyMath

/-! # The division of `Impl/Rsa/Arm/Div.lean` on arrays of the key working space

With the division's header (bytes 0–19) naming the arrays `q`, `r`, `d`
and `t` and the count `w`, and the word after `[d]` zero, `div_ok`:
`[q] := [q] / [d]` and `[r] := [q] mod [d]` for `[d] > 0`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Div
open VG.Proof.X25519.Arm

/-- The division's geometry on arrays `q`, `r`, `d`, `t`. -/
def divGeom (B : BitVec 32) (Z w q r d t : Nat) : Geometry where
  base := B
  size := Z
  offsets i := match i.val with | 0 => arr w q | 1 => arr w r | 2 => arr w d | _ => arr w t
  n := w

theorem divGeom_o0 {B : BitVec 32} {Z w q r d t : Nat} : (divGeom B Z w q r d t).offsets 0 = arr w q := rfl
theorem divGeom_o1 {B : BitVec 32} {Z w q r d t : Nat} : (divGeom B Z w q r d t).offsets 1 = arr w r := rfl
theorem divGeom_o3 {B : BitVec 32} {Z w q r d t : Nat} : (divGeom B Z w q r d t).offsets 3 = arr w t := rfl
theorem divGeom_base {B : BitVec 32} {Z w q r d t : Nat} : (divGeom B Z w q r d t).base = B := rfl
theorem divGeom_n {B : BitVec 32} {Z w q r d t : Nat} : (divGeom B Z w q r d t).n = w := rfl

/-- The division's header in memory. -/
structure DivHdr (m : Mem) (B : BitVec 32) (w q r d t : Nat) : Prop where
  q : m.readW (off (State.addr B) 0) 32 = B + BitVec.ofNat 32 (arr w q)
  r : m.readW (off (State.addr B) 4) 32 = B + BitVec.ofNat 32 (arr w r)
  d : m.readW (off (State.addr B) 8) 32 = B + BitVec.ofNat 32 (arr w d)
  t : m.readW (off (State.addr B) 12) 32 = B + BitVec.ofNat 32 (arr w t)
  n : m.readW (off (State.addr B) 16) 32 = BitVec.ofNat 32 w

theorem divGeom_ctx {s : State} {B : BitVec 32} {Z w N q r d t : Nat} (h : Ws s B Z w N)
    (hq : q < N) (hr : r < N) (hd : d < N) (ht : t < N)
    (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t)
    (hh : DivHdr s.mem B w q r d t) : Context (divGeom B Z w q r d t) s := by
  have fq := h.arr_fit hq
  have fr := h.arr_fit hr
  have fd := h.arr_fit hd
  have ft := h.arr_fit ht
  have hS : S w = 4 * (w + 2) := rfl
  have hw := h.wle
  have hf : 20 ≤ Z := by have := h.hdr_le; simp only [hdr] at this; omega
  refine ⟨⟨h.nowrap, h.writable⟩, h.wpos, by rw [divGeom_n]; omega, hf, ?_, ?_, ?_, h.r8, ?_, hh.n⟩
  · intro i; rcases i with ⟨_ | _ | _ | _ | i, hi⟩ <;> simp only [divGeom, Geometry.words] <;>
      (try split) <;> first | omega | (simp at hi; omega) | (simp at *)
  · intro i
    have e : ∀ x, 20 ≤ arr w x := fun x => Nat.le_trans (by decide : 20 ≤ hdr) (Nat.le_add_right _ _)
    rcases i with ⟨_ | _ | _ | _ | i, hi⟩ <;> simp only [divGeom] <;> first | exact e _ | (simp at hi)
  · intro i j hij
    -- Keep the arithmetic solver independent of the workspace and memory facts.
    have qr := arr_disj (w := w) hqr; have qd := arr_disj (w := w) hqd; have qt := arr_disj (w := w) hqt
    have rd := arr_disj (w := w) hrd; have rt := arr_disj (w := w) hrt; have dt := arr_disj (w := w) hdt
    rcases i with ⟨_ | _ | _ | _ | i, hi⟩ <;> rcases j with ⟨_ | _ | _ | _ | j, hj⟩ <;>
      simp only [divGeom, Geometry.words, Fin.mk.injEq, ne_eq, not_true_eq_false] at hij ⊢ <;>
      (try split) <;> (try split) <;>
      first | omega_using [qr, qd, qt, rd, rt, dt, hij, hi, hj, hS] | (exact absurd rfl hij) | (simp at hi) | (simp at hj)
  · intro i; rcases i with ⟨_ | _ | _ | _ | i, hi⟩
    · exact hh.q
    · exact hh.r
    · exact hh.d
    · exact hh.t
    · omega

theorem val32_top {m : Mem} {base : Addr} {d w : Nat} (h : w32 m base (d + 4 * w) = 0) :
    val32 m base d (w + 1) = val32 m base d w := by
  rw [val32_succ, h, Nat.mul_zero, Nat.add_zero]

theorem val32_low {m : Mem} {base : Addr} {d w : Nat} (h : val32 m base d (w + 1) < 2 ^ (32 * w)) :
    val32 m base d w = val32 m base d (w + 1) := by
  rw [val32_succ] at h ⊢
  have := val32_lt m base d w
  rcases Nat.eq_zero_or_pos (w32 m base (d + 4 * w)) with e | e
  · rw [e, Nat.mul_zero, Nat.add_zero]
  · exfalso
    have : 2 ^ (32 * w) ≤ 2 ^ (32 * w) * w32 m base (d + 4 * w) := Nat.le_mul_of_pos_right _ e
    omega

theorem div_ok {s : State} {B : BitVec 32} {Z w N q r d t : Nat} (h : Ws s B Z w N)
    (hq : q < N) (hr : r < N) (hd : d < N) (ht : t < N)
    (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t)
    (hh : DivHdr s.mem B w q r d t) (top : w32 s.mem (State.addr B) (arr w d + 4 * w) = 0) :
    WP isa Impl.Rsa.Arm.Div.code s fun u => Keep B w [q, r, t] [] s.mem u.mem ∧
      Rest (.r6 :: clobbers) s u ∧
      (0 < num s.mem B w d → num u.mem B w r = num s.mem B w q % num s.mem B w d ∧
        num u.mem B w q = num s.mem B w q / num s.mem B w d) := by
  have c := divGeom_ctx h hq hr hd ht hqr hqd hqt hrd hrt hdt hh
  refine WP.mono (code_ok c) fun u ⟨_, fr, rest, v⟩ => ⟨?_, rest, fun pos => ?_⟩
  · intro x hx
    refine fr x fun rg hrg => ?_
    simp only [Geometry.ranges, divGeom_o0, divGeom_o1, divGeom_o3, divGeom_n, List.mem_cons,
      List.not_mem_nil, or_false] at hrg
    have hS : S w = 4 * (w + 2) := rfl
    rw [divGeom_base]
    rcases hrg with rfl | rfl | rfl
    · have := hx (arr w q, S w) (by simp [ranges]); dsimp only; omega
    · have := hx (arr w r, S w) (by simp [ranges]); dsimp only; omega
    · have := hx (arr w t, S w) (by simp [ranges]); dsimp only; omega
  · have eD : (divGeom B Z w q r d t).value s.mem 2 = num s.mem B w d := val32_top top
    have lt := val32_lt s.mem (State.addr B) (arr w d) w
    have v' := v (by rw [eD]; exact pos) (by rw [eD]; exact lt)
    rw [eD] at v'
    obtain ⟨vr, vq⟩ := v'
    refine ⟨?_, vq⟩
    have : (divGeom B Z w q r d t).value u.mem 1 < 2 ^ (32 * w) := by
      rw [vr]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ pos) (Nat.le_of_lt lt)
    exact (val32_low this).trans vr

end VG.Proof.Rsa.Arm.Keys
