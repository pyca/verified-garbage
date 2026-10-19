module
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Rsa.X86.PrivChecked
public import VerifiedGarbage.Proof.Framework.X86.RelCT

import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Call-argument setup reveals only the public stack pointer -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Dsa.X86

theorem crtArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block crtArgs)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem precomputeArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block precomputeArgs)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem publicArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block publicArgs)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem pair_seq_ct {P₁ P₂ Q₁ Q₂ : State → Prop} {a b : Prog isa}
    (first : RelCT isa (fun s t => P₁ s ∧ P₂ t) a (fun _ _ => True))
    (left : ∀ s, P₁ s → WP isa a s Q₁) (right : ∀ s, P₂ s → WP isa a s Q₂)
    (next : RelCT isa (fun s t => Q₁ s ∧ Q₂ t) b (fun _ _ => True)) :
    RelCT isa (fun s t => P₁ s ∧ P₂ t) (.seq a b) (fun _ _ => True) :=
  VG.RelCT.seq (first.wp (fun s t h => ⟨left s h.1, right t h.2⟩))
    (next.mono (fun _ _ h => h.2) (fun _ _ _ => trivial))

end VG.Proof.Rsa.X86.PrivChecked
