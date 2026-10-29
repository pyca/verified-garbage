module

import VerifiedGarbage.Proof.Bignum.X86.PublicSave
public import VerifiedGarbage.Impl.Rsa.X86.CrtValues
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Spec.Weierstrass

/-! # Establishing the arithmetic workspace while preserving the caller ABI -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.X86.Wp VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Bignum.X86 VG.Proof.Bignum.X86

theorem entry_ok {s : State} {base : Addr} {size : Nat} {ptr : BitVec 32}
    (read : readSrc s (.mem (PublicFn.argument 14)) = some ptr)
    (hb : ptr.setWidth 64 = base) (hf : ptr.toNat + size ≤ 2 ^ 32) (hz : 16 ≤ size)
    (hw : (⟨base, size⟩ : Region) ∈ s.wr) (stk : StkOk (s.gpr .esp) base size) :
    WP isa (.block VG.Impl.Rsa.X86.CrtValues.entry) s fun t =>
      Scr t base size ∧ Saved t.mem (off base) s.gpr PublicFn.savedRegisters ∧
      Keeps [.eax, .edi] s t ∧ Outside base 0 size s.mem t.mem := by
  unfold VG.Impl.Rsa.X86.CrtValues.entry
  simp only [List.singleton_append]
  refine wp_movS read fun u U _ => ?_
  refine WP.block_append (WP.mono (entrySave_ok (base := base) (size := size) (by rw [U.gpr]; exact hb)
    (by rw [U.gpr]; exact hf) hz (by rw [U.wr]; exact hw)) fun v ⟨G, Rd, Wr, S, F⟩ => ?_)
  refine wp_movS rfl fun t T _ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [T.gpr, G, U.gpr]; exact hb
    · rw [T.wr, Wr, U.wr]; exact hw
    · rw [← hb, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans ptr.isLt (by decide))]
      exact hf
    · rw [T.other _ (by decide), G, U.other _ (by decide)]
      exact stk
  · intro p hp
    rw [T.mem, S p hp]
    have H : p.1 ≠ .eax := by
      simp only [PublicFn.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide
    exact U.other _ H
  · refine ⟨?_, ?_, ?_⟩
    · intro reg hr
      rw [T.other reg (by intro H; subst reg; exact hr (by simp)), G]
      exact U.other reg (by intro H; subst reg; exact hr (by simp))
    · rw [T.rd, Rd, U.rd]
    · rw [T.wr, Wr, U.wr]
  · intro a ha
    rw [T.mem]
    have H : ¬ InRegions [⟨base, size⟩] a 1 := by
      simp only [InRegions, List.mem_singleton, exists_eq_left, Region.Contains]
      change ¬ (ofs base a + 1 ≤ size)
      omega
    exact (F a (by intro reg hreg hcontains; exact H ⟨reg, hreg, hcontains⟩)).trans (congrFun U.mem a)

end VG.Proof.Rsa.X86.CrtValues
