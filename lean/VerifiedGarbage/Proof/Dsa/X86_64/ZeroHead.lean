module

public import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import VerifiedGarbage.Proof.Dsa.Layout

/-! # Resolving the operand of a DSA zero check -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem zeroHead_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z)
    (a : Operand) (ha : pointerFits a.pointer) :
    WP isa (.block (Core.pointer a.pointer ++ ([.mov .rsi (.reg .rax),
      .mov .rcx (.mem (Core.field a.length)), .mov32 .r8 (.imm 0)] : List Instr))) s fun t =>
      t.gpr .rsi = pointerValue s.mem B a.pointer ∧ t.gpr .rcx = word s.mem B a.length.offset ∧
      t.gpr .r8 = 0 ∧ t.mem = s.mem ∧ Keep [.rax, .rsi, .rcx, .r8] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (pointer_ok hs hdi hZ a.pointer ha) fun u ⟨hua, hum, hku⟩ => ?_
  have hudi := (hku.gpr (show Reg.rdi ∉ [Reg.rax] by decide)).trans hdi
  have hul : word u.mem B a.length.offset = word s.mem B a.length.offset := by rw [hum]
  have hus := hs.congr hku.2.2
  refine WP.mono (WP.keep [.rsi, .rcx, .r8] (Q := fun v =>
    v.gpr .rsi = pointerValue s.mem B a.pointer ∧ v.gpr .rcx = word s.mem B a.length.offset ∧
    v.gpr .r8 = 0 ∧ v.mem = u.mem) ?_ rfl) fun v ⟨⟨hvp, hvn, hv8, hvm⟩, hkv⟩ =>
      ⟨hvp, hvn, hv8, hvm.trans hum, (hku.trans hkv).mono (by decide)⟩
  xrun [hua, State.ea, Core.field, hudi, fieldAddress, hul,
    hus.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds a.length).2 hZ)]

end VG.Proof.Dsa.X86_64
