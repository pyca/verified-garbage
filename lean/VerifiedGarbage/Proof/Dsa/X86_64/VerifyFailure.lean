module
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Impl.Dsa.X86_64.Core

import VerifiedGarbage.Proof.Bignum.X86_64.PubOut
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Aesop.BuiltinRules
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Dsa.X86_64.Operands

/-! # Early verification failure restores System V registers -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem verifyFailure_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z)
    :
    WP isa (.block (([.mov32 .rax (.imm 0)] : List Instr) ++ exit)) s fun t =>
      t.gpr .rax = 0 ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)) ∧
      t.mem = s.mem ∧ Keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 :=
    fun i hi => hs.ld (Nat.le_trans (show 8 * i + 8 ≤ pWorkspace by change 8 * i + 8 ≤ 3456; omega) hZ)
  rw [exit_eq]
  refine WP.mono (WP.keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
    t.gpr .rax = 0 ∧
    t.gpr .rbx = word s.mem B 0 ∧ t.gpr .rbp = word s.mem B 8 ∧
    t.gpr .r12 = word s.mem B 16 ∧ t.gpr .r13 = word s.mem B 24 ∧
    t.gpr .r14 = word s.mem B 32 ∧ t.gpr .r15 = word s.mem B 40 ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨ht, h0, h1, h2, h3, h4, h5, hmem⟩, hk⟩ => ?_
  · simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, hdi, hdrOff, Core.field, fieldAddress,
     
      hl 0 (by decide), hl 1 (by decide), hl 2 (by decide), hl 3 (by decide), hl 4 (by decide), hl 5 (by decide)]
  · refine ⟨ht, ?_, hmem, hk⟩
    intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5

end VG.Proof.Dsa.X86_64
