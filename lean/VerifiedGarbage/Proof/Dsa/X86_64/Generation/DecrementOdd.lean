module
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces

import VerifiedGarbage.Proof.Rsa.X86_64.CvCheck
import VerifiedGarbage.Proof.Rsa.X86_64.Div
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push

/-! # The generator's upper endpoint p−1 requires only a low-limb decrement -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 VG.Impl.Rsa.X86_64.Keys

theorem decrementOdd_ok {s : State} {B : Addr} {Z w j : Nat}
    (h : Ws s B Z w) (hj : j < 16) (ho : wv s.mem B (slot w j) w % 2 = 1) :
    WP isa (.block (decA j)) s fun t =>
      Ws t B Z w ∧ wv t.mem B (slot w j) w = wv s.mem B (slot w j) w - 1 ∧
      Outside B (slot w j) 8 s.mem t.mem ∧ Keep [.r12, .r9, .rbx, .rax] s t := by
  have room := h.sl hj
  have nowrap := h.scr.nowrap
  have hw := h.w1
  refine WP.mono (decA_ok h hj) fun t ⟨hm, hk⟩ => ?_
  have hf : Outside B (slot w j) 8 s.mem t.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by omega)
  have ff : Frm B [(slot w j, 8)] s.mem t.mem := Frm.of_outside hf (by simp)
  refine ⟨h.congr ff (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot _ _ _)
    hk (by decide), ?_, hf, hk⟩
  have upper : wv t.mem B (slot w j + 8) (w - 1) = wv s.mem B (slot w j + 8) (w - 1) :=
    hf.wv (Or.inr (by omega)) (by omega)
  have low : word t.mem B (slot w j) = word s.mem B (slot w j) - 1 := by
    rw [hm, word_writeW_self]
  have odd : (word s.mem B (slot w j)).toNat % 2 = 1 := by
    rw [wv_low (by omega : 0 < w)] at ho
    omega
  have sub : (word s.mem B (slot w j) - 1).toNat = (word s.mem B (slot w j)).toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
    rfl
  rw [wv_low (by omega : 0 < w), upper, low, sub, wv_low (m := s.mem) (by omega : 0 < w)]
  omega

end VG.Proof.Dsa.X86_64.Generation
