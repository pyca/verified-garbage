module

public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Div
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Defs.Prop
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DivisionLoad
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DivisionStore
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseFrame
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Impl.Rsa.X86.KeyWs
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionLoad
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDivisionStore
/-! # Divide persistent arrays in the full native RSA workspace -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/Divide.lean`, which only this module imported.
section

/-! # The runtime division kernel is shared with RSA key checking -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num Keep arr)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Impl.Rsa.X86.KeyRt (sCy sQb)

theorem divide_ok {s : State} {B : Addr} {Z n N : Nat} {w : Width}
    (h : Ws s B Z n N) (bound : 4 ≤ N) (hw : w ≠ .correction)
    (top : w32 s.mem B (arr (w.words n) 2 + 4 * w.words n) = 0) :
    WP isa (divide w) s fun t => Ws t B Z n N ∧
      Keep B (w.words n) [0, 1, 3] [sCy, sQb] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧
      (0 < num s.mem B (w.words n) 2 →
        num t.mem B (w.words n) 0 = num s.mem B (w.words n) 0 / num s.mem B (w.words n) 2 ∧
        num t.mem B (w.words n) 1 = num s.mem B (w.words n) 0 % num s.mem B (w.words n) 2) := by
  have code : divide w = VG.Impl.Rsa.X86.KeyRt.div w.lay 0 1 2 3 := by
    cases w <;> simp_all [divide]
  rw [code]
  have H := shrinkRt (h.runtime hw) bound
  have core := VG.Proof.Rsa.X86.KeyRt.div_ok H
    (by decide : 0 < 4) (by decide : 1 < 4) (by decide : 2 < 4) (by decide : 3 < 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simpa only [kw_words h.width] using top)
  rw [kw_words h.width] at core
  refine WP.mono core fun t ⟨_, O, K, V⟩ => ⟨h.afterBank hw K O ?_ (by decide), O, K, V⟩
  intro j hj
  have small := (by decide : ∀ j ∈ ([0, 1, 3] : List Nat), j < 4) j hj
  omega

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/Division.lean`, which only this module imported.
section

/-! # Quotient and remainder share the runtime RSA division kernel

Division uses four arrays of the shared temporary bank. Its frame also
includes the two saved division bits.
-/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys (hdr)
open VG.Impl.Rsa.X86.KeyRt (sCy sQb)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (DivisionInputs DivisionOutputs inverseRanges
  inverse_frame inverse_frame_clear)

def divisionRanges (d q r : Nat) : List (Nat × Nat) :=
  [(hdr, 4 * (4 * (d + 2))), (sCy, 4), (sQb, 4), (q, 4 * d), (r, 4 * d)]

theorem divisionFrom_ok {s : State} {B : Addr} {Z n N : Nat} {w : Width}
    {src divisor quotient remainder : Loc} (h : Ws s B Z n N) (bound : 4 ≤ N)
    (hw : w ≠ .correction)
    (input : DivisionInputs Z (w.words n) (src.offset n) (divisor.offset n))
    (output : DivisionOutputs Z (w.words n) (quotient.offset n) (remainder.offset n))
    (positive : 0 < val32 s.mem B (divisor.offset n) (w.words n)) :
    WP isa (divisionFrom w src divisor quotient remainder) s fun t =>
      Ws t B Z n N ∧ Outs B (divisionRanges (w.words n) (quotient.offset n) (remainder.offset n))
        s.mem t.mem ∧
      val32 t.mem B (quotient.offset n) (w.words n) =
        val32 s.mem B (src.offset n) (w.words n) / val32 s.mem B (divisor.offset n) (w.words n) ∧
      val32 t.mem B (remainder.offset n) (w.words n) =
        val32 s.mem B (src.offset n) (w.words n) % val32 s.mem B (divisor.offset n) (w.words n) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold divisionFrom
  refine WP.seq (WP.mono (divisionLoad_ok h bound hw input)
    fun u ⟨hu, Ou, numerator, modulus, top, Ku⟩ => ?_)
  refine WP.seq (WP.mono (divide_ok hu bound hw top) fun v ⟨hv, Ov, Kv, computed⟩ => ?_)
  have result := computed (by rw [modulus]; exact positive)
  rw [numerator, modulus] at result
  refine WP.mono (divisionStore_ok hv bound hw output) fun t ⟨ht, Ot, Q, R, Kt⟩ => ?_
  refine ⟨ht, ?_, Q.trans result.1, R.trans result.2,
    (Ku.mono (by decide)).trans (Kv.trans (Kt.mono (by decide)))⟩
  have first : Outs B (divisionRanges (w.words n) (quotient.offset n) (remainder.offset n))
      s.mem u.mem := Outs.of_outside Ou (List.mem_cons_self ..)
  have middle : Outs B (divisionRanges (w.words n) (quotient.offset n) (remainder.offset n))
      u.mem v.mem := Ov.cover (by
    intro region member
    simp only [VG.Proof.Rsa.X86.Keys.ranges, List.mem_append, List.mem_map] at member
    rcases member with ⟨j, hj, rfl⟩ | ⟨slot, hs, rfl⟩
    · refine ⟨(hdr, 4 * (4 * (w.words n + 2))), List.mem_cons_self .., Nat.le_add_right .., ?_⟩
      have small : j < 4 := by
        have bounds := (by decide : ∀ j ∈ ([0, 1, 3] : List Nat), j < 4) j hj
        exact bounds
      have last := VG.Proof.Rsa.X86.Keys.arr_end (w := w.words n) small
      simpa only [VG.Proof.Rsa.X86.Keys.arr, VG.Proof.Rsa.X86.Keys.S,
        Nat.mul_assoc, Nat.mul_left_comm] using last
    · refine ⟨(slot, 4), ?_, Nat.le_refl _, Nat.le_refl _⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;> simp [divisionRanges])
  have last : Outs B (divisionRanges (w.words n) (quotient.offset n) (remainder.offset n))
      v.mem t.mem := Ot.mono (by
    intro region member
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)))
  exact (first.trans middle).trans last

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr
open VG.Proof.RsaKeyGen.X86.Key (DivisionInputs DivisionOutputs)

def arrayDivisionRanges (n q r : Nat) : List (Nat × Nat) :=
  [(VG.Impl.Rsa.X86.Keys.hdr, 4 * S n), (136, 4), (140, 4),
    (arr n q, 4 * n), (arr n r, 4 * n)]

theorem arrayDivision_ok {s : State} {B : Addr} {Z n a d q r : Nat} (h : Ws s B Z n 32)
    (ha : a < 32) (hd : d < 32) (hq : q < 32) (hr : r < 32)
    (pa : 4 ≤ a) (pd : 4 ≤ d) (pq : 4 ≤ q) (pr : 4 ≤ r) (qr : q ≠ r)
    (positive : 0 < num s.mem B n d) :
    WP isa (divFull a d q r) s fun t =>
      Ws t B Z n 32 ∧ Outs B (arrayDivisionRanges n q r) s.mem t.mem ∧
      num t.mem B n q = num s.mem B n a / num s.mem B n d ∧
      num t.mem B n r = num s.mem B n a % num s.mem B n d ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have fa := h.arr_fit ha
  have fd := h.arr_fit hd
  have fq := h.arr_fit hq
  have fr := h.arr_fit hr
  have input : DivisionInputs Z n (arr n a) (arr n d) := by
    refine ⟨?_, ?_, Or.inr (arr_mono pa), Or.inr (arr_mono pd)⟩
    · unfold S at fa
      omega
    · unfold S at fd
      omega
  have output : DivisionOutputs Z n (arr n q) (arr n r) := by
    refine ⟨?_, ?_, Or.inr (arr_mono pq), Or.inr (arr_mono pr), ?_⟩
    · unfold S at fq
      omega
    · unfold S at fr
      omega
    · have disj := arr_disj (w := n) qr
      unfold S at disj
      omega
  refine WP.mono (divisionFrom_ok h (by decide) (by decide)
    (show DivisionInputs Z (Width.modulus.words n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr a).offset n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr d).offset n) from input)
    (show DivisionOutputs Z (Width.modulus.words n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr q).offset n)
      ((VG.Impl.RsaKeyGen.X86.KeyRuntime.arr r).offset n) from output) positive)
    fun t ⟨ht, O, Q, R, K⟩ => ?_
  exact ⟨ht, by simpa only [arrayDivisionRanges, divisionRanges, Width.words,
    VG.Impl.RsaKeyGen.X86.KeyRuntime.arr, offset_array, S,
    VG.Impl.Rsa.X86.KeyRt.sCy, VG.Impl.Rsa.X86.KeyRt.sQb, Nat.mul_assoc] using O,
    Q, R, K.mono (by decide)⟩

theorem arrayDivision_preserves_num {m m' : Mem} {B : Addr} {n q r j : Nat}
    (persistent : 4 ≤ j) (jq : j ≠ q) (jr : j ≠ r) (fit : arr n j + S n ≤ 2 ^ 64)
    (O : Outs B (arrayDivisionRanges n q r) m m') : num m' B n j = num m B n j := by
  change val32 m' B (arr n j) n = val32 m B (arr n j) n
  apply O.val32 _ (by unfold S at fit; omega)
  intro region mem
  simp only [arrayDivisionRanges, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (arr_mono persistent)
  · exact Or.inr (Nat.le_trans (by decide : 136 + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) (Nat.le_add_right ..))
  · exact Or.inr (Nat.le_trans (by decide : 140 + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) (Nat.le_add_right ..))
  · have D := arr_disj (w := n) jq
    simp only at D ⊢
    unfold S at D
    omega
  · have D := arr_disj (w := n) jr
    simp only at D ⊢
    unfold S at D
    omega

end VG.Proof.RsaKeyGen.X86.KeyRuntime
