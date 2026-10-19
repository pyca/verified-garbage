module

public import VerifiedGarbage.Impl.Bignum.X86.LoadBE
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Setting the pointers for runtime-sized integer import -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem loadBEArgs_ok (s : State) (out : Nat) {k : Nat} (hk : 0 < k)
    (count : s.gpr .ecx = BitVec.ofNat 32 k) :
    WP isa (.block (loadBEArgs out)) s fun t =>
      t.gpr .ebx = s.gpr .edi + BitVec.ofNat 32 out ∧
      t.gpr .esi = s.gpr .esi + BitVec.ofNat 32 (k - 1) ∧
      t.gpr .ecx = BitVec.ofNat 32 k ∧ t.mem = s.mem ∧ Keeps [.ebx, .esi] s t := by
  unfold loadBEArgs
  refine wp_movS rfl fun s₁ u₁ _ => ?_
  refine wp_addS rfl fun s₂ u₂ _ => ?_
  refine wp_addS rfl fun s₃ u₃ _ => ?_
  refine wp_subS rfl fun t u₄ _ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [u₄.other .ebx (by decide), u₃.other .ebx (by decide), u₂.gpr, u₁.gpr]
  · rw [u₄.gpr, u₃.gpr, u₂.other .esi (by decide), u₁.other .esi (by decide),
      u₂.other .ecx (by decide), u₁.other .ecx (by decide), count]
    change s.gpr .esi + BitVec.ofNat 32 k - BitVec.ofNat 32 1 = _
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      Offset.ofNat_sub_ofNat (by omega)]
  · rw [u₄.other .ecx (by decide), u₃.other .ecx (by decide), u₂.other .ecx (by decide),
      u₁.other .ecx (by decide), count]
  · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · exact (((u₁.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps).widen u₄.keeps

end VG.Proof.Bignum.X86
