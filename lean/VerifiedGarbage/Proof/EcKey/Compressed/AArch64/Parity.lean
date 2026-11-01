module

public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Decompress
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
import VerifiedGarbage.Proof.EcKey.Compressed.Parity
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Weierstrass.Words
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.InverseContract

/-! # The canonical root's parity mismatch mask -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

 theorem parityMask_ok {c : Cfg} {s : State} {base : Addr}
    (hs : Scr s base size) (hn : 0 < c.n)
    (hy : c.sl Impl.Ecdh.AArch64.QY + 8 ≤ size) (ht : c.sl D + 8 ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.AArch64.parityMask c)) s fun t =>
      t.gpr .x3 = mask (sv c base s Impl.Ecdh.AArch64.QY % 2 ≠
        (word s.mem base (c.sl D)).toNat % 2) ∧ Keeps [.x1, .x2, .x3, .x7] s t := by
  change WP isa (.block ([ld .x1 (c.sl Impl.Ecdh.AArch64.QY)] ++
    ([ld .x2 (c.sl D)] ++ _))) s _
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hs hy (sl_mod8 c _) .x1) fun s₁ ⟨y₁, k₁, _⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok (hs.of_keeps k₁ (by decide)) ht (sl_mod8 c D) .x2)
    fun s₂ ⟨tag₂, k₂, _⟩ => ?_
  have y₂ : s₂.gpr .x1 = word s.mem base (c.sl Impl.Ecdh.AArch64.QY) :=
    (k₂.gpr _ (by decide)).trans y₁
  rw [k₁.mem] at tag₂
  refine WP.mono (show WP isa (.block _) s₂ (fun t =>
    t.gpr .x3 = 0 - ((s₂.gpr .x1 ^^^ s₂.gpr .x2) &&& 1) ∧ Keeps [.x1, .x2, .x3, .x7] s₂ t) by
    apply WP.of_runBlock
    simp only [zero7, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
      show 16 * 0 < Size.x.bits by decide, ite_true, RegUpd.gpr_write,
      BitVec.setWidth_eq, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · rw [BitVec.xor_comm]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false])
    fun t ⟨m, k₃⟩ => ?_
  refine ⟨?_, ((k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))).trans k₃⟩
  rw [m, y₂, tag₂, xor_low_mask, slot_parity _ _ _ _ hn]

 theorem invertMask_ok (s : State) (P : Prop) [Decidable P] (h : s.gpr .x3 = mask P) :
    WP isa (.block Impl.EcKey.Compressed.AArch64.invertMask) s fun t =>
      t.gpr .x2 = mask (¬ P) ∧ Keeps [.x2, .x7] s t := by
  apply WP.of_runBlock
  simp only [Impl.EcKey.Compressed.AArch64.invertMask, zero7,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 16 * 0 < Size.x.bits by decide, show (1 : Nat) < 4096 by decide,
    ite_true, RegUpd.gpr_write, BitVec.setWidth_eq,
    reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · rw [h]
    by_cases hp : P <;> simp [mask, hp] <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

end VG.Proof.EcKey.Compressed.AArch64
