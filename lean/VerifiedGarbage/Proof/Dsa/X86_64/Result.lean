module

public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import VerifiedGarbage.Proof.Bignum.X86_64.PubOut
import VerifiedGarbage.Proof.Dsa.Layout
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core

/-! # Returning the DSA acceptance bit and restoring System V registers -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem result_ok {s : State} {B : Addr} {Z : Nat} {valid : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z)
    (hm : word s.mem B Field.mask.offset = mask valid) :
    WP isa (.block SignVerify.result) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 valid.toNat ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)) ∧
      t.mem = s.mem ∧ Keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 :=
    fun i hi => hs.ld (Nat.le_trans (show 8 * i + 8 ≤ pWorkspace by change 8 * i + 8 ≤ 3456; omega) hZ)
  unfold SignVerify.result
  rw [exit_eq]
  refine WP.mono (WP.keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
    t.gpr .rax = BitVec.ofNat 64 valid.toNat ∧
    t.gpr .rbx = word s.mem B 0 ∧ t.gpr .rbp = word s.mem B 8 ∧
    t.gpr .r12 = word s.mem B 16 ∧ t.gpr .r13 = word s.mem B 24 ∧
    t.gpr .r14 = word s.mem B 32 ∧ t.gpr .r15 = word s.mem B 40 ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨ht, h0, h1, h2, h3, h4, h5, hmem⟩, hk⟩ => ?_
  · simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, hdi, hdrOff, Core.field, fieldAddress,
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .mask).2 hZ), hm, mask_and1,
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
