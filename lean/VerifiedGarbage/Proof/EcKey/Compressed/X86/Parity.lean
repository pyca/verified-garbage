module

public import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
public import VerifiedGarbage.Proof.EcKey.Compressed.Parity
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Match the recovered root's low bit on 32-bit x86 -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86

theorem xor_low_mask32 (x y : BitVec 32) :
    0 - ((x ^^^ y) &&& 1) = mask32 (x.toNat % 2 ≠ y.toNat % 2) := by
  have hlow : (x ^^^ y) &&& 1 = if x.toNat % 2 = y.toNat % 2 then 0 else 1 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_xor, show (1 : BitVec 32).toNat = 1 from rfl,
      Nat.and_one_is_mod, show 2 = 2 ^ 1 from rfl, Nat.xor_mod_two_pow]
    rcases Nat.mod_two_eq_zero_or_one x.toNat with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one y.toNat with hy | hy <;> simp [hx, hy]
  rw [hlow]
  by_cases h : x.toNat % 2 = y.toNat % 2 <;> simp [h, mask32]

theorem parityMask_ok {c : Cfg} {s : State} {base : Addr}
    (hs : Scr s base size) (hn : 0 < c.n)
    (hy : c.sl Impl.Ecdh.X86.QY + 4 ≤ size) (ht : c.sl D + 4 ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.X86.parityMask c)) s fun t =>
      t.gpr .ecx = mask32 (sv c base s Impl.Ecdh.X86.QY % 2 ≠
        (s.mem.readW (off base (c.sl D)) 32).toNat % 2) ∧
      Keeps [.eax, .ecx, .edx] s t ∧ t.mem = s.mem := by
  unfold Impl.EcKey.Compressed.X86.parityMask
  refine wp_movS (readSrc_sc hs hy) fun s₁ u₁ _ => ?_
  have hs₁ := hs.of_keeps (u₁.keeps) (by decide)
  refine wp_movS (readSrc_sc hs₁ ht) fun s₂ u₂ _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₃ u₃ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₄ u₄ => ?_
  refine wp_movi fun s₅ u₅ => ?_
  refine wp_subS rfl fun s₆ u₆ _ => ?_
  refine wp_mov fun t u₇ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [u₇.gpr, u₆.gpr, u₅.gpr, u₅.other .ecx (by decide), u₄.gpr, u₃.gpr,
      u₂.gpr, u₂.other .eax (by decide), u₁.gpr, u₁.mem]
    simp only [ite_true, reduceCtorEq, ite_false]
    rw [BitVec.xor_comm, xor_low_mask32, slot32_parity _ _ _ _ hn]
  · exact (u₁.keeps.mono (by simp)).trans ((u₂.keeps.mono (by simp)).trans
      ((u₃.keeps.mono (by simp)).trans ((u₄.keeps.mono (by simp)).trans
      ((u₅.keeps.mono (by simp)).trans ((u₆.keeps.mono (by simp)).trans (u₇.keeps.mono (by simp)))))))
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

theorem invertMask_ok (s : State) (P : Prop) [Decidable P] (h : s.gpr .ecx = mask32 P) :
    WP isa (.block Impl.EcKey.Compressed.X86.invertMask) s fun t =>
      t.gpr .edx = mask32 (¬ P) ∧ Keeps [.eax, .edx] s t ∧ t.mem = s.mem := by
  unfold Impl.EcKey.Compressed.X86.invertMask
  refine wp_mov fun s₁ u₁ => ?_
  refine wp_addS rfl fun s₂ u₂ _ => ?_
  refine wp_movi fun s₃ u₃ => ?_
  refine wp_subS rfl fun s₄ u₄ _ => ?_
  refine wp_mov fun t u₅ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [u₅.gpr, u₄.gpr, u₃.gpr, u₃.other .edx (by decide), u₂.gpr, u₁.gpr, h]
    by_cases hp : P <;> simp [mask32, hp]
  · exact (u₁.keeps.mono (by simp)).trans ((u₂.keeps.mono (by simp)).trans
      ((u₃.keeps.mono (by simp)).trans ((u₄.keeps.mono (by simp)).trans (u₅.keeps.mono (by simp)))))
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

end VG.Proof.EcKey.Compressed.X86
