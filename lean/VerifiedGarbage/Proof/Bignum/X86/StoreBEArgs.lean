module

public import VerifiedGarbage.Impl.Bignum.X86.StoreBE
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Setting the source pointer for RSA integer export -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem storeBEArgs_ok (s : State) (src : Nat) {k : Nat} (hk : 0 < k)
    (count : s.gpr .ecx = BitVec.ofNat 32 k) :
    WP isa (.block (storeBEArgs src)) s fun t =>
      t.gpr .esi = (s.gpr .edi + BitVec.ofNat 32 src) + BitVec.ofNat 32 (k - 1) ∧
      t.mem = s.mem ∧ Keeps [.esi] s t := by
  unfold storeBEArgs
  refine wp_movS rfl fun s₁ u₁ _ => ?_
  refine wp_addS rfl fun s₂ u₂ _ => ?_
  refine wp_addS rfl fun s₃ u₃ _ => ?_
  refine wp_subS rfl fun t u₄ _ => WP.block_nil ?_
  refine ⟨?_, ?_, ((u₁.keeps.trans u₂.keeps).trans u₃.keeps).trans u₄.keeps⟩
  · rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, u₂.other .ecx (by decide),
      u₁.other .ecx (by decide), count]
    change (s.gpr .edi + BitVec.ofNat 32 src) + BitVec.ofNat 32 k - BitVec.ofNat 32 1 = _
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      Offset.ofNat_sub_ofNat (by omega)]
  · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]

end VG.Proof.Bignum.X86
