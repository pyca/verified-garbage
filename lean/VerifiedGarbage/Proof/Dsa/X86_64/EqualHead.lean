module

public import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import VerifiedGarbage.Proof.Dsa.Layout

/-! # Resolving both operands of a DSA equality check -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem equalHead_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z)
    (a b : Operand) (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) :
    WP isa (.block (Core.pointer a.pointer ++ ([.mov .rsi (.reg .rax)] : List Instr) ++
      Core.pointer b.pointer ++ ([.mov .rdx (.reg .rax), .mov .rcx (.mem (Core.field a.length)),
        .mov32 .r8 (.imm 0)] : List Instr))) s fun t =>
      t.gpr .rsi = pointerValue s.mem B a.pointer ∧ t.gpr .rdx = pointerValue s.mem B b.pointer ∧
      t.gpr .rcx = word s.mem B a.length.offset ∧ t.gpr .r8 = 0 ∧ t.mem = s.mem ∧
      Keep [.rax, .rsi, .rdx, .rcx, .r8] s t := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (pointer_ok hs hdi hZ a.pointer ha) fun u ⟨hua, hum, hku⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rsi] (Q := fun v => v.gpr .rsi = pointerValue s.mem B a.pointer ∧ v.mem = u.mem)
    (by xrun [hua]) rfl) fun v ⟨⟨hvsi, hvm⟩, hkv⟩ => ?_
  have hks := hku.trans hkv
  rw [WP.block_append_iff]
  refine WP.mono (pointer_ok (hs.congr hks.2.2) ((hks.gpr (by decide)).trans hdi) hZ b.pointer hb)
    fun z ⟨hza, hzm, hkz⟩ => ?_
  rw [hvm, hum] at hza
  have hzsi := (hkz.gpr (show Reg.rsi ∉ [Reg.rax] by decide)).trans hvsi
  have hksz := hks.trans hkz
  have hzdi := (hksz.gpr (show Reg.rdi ∉ _ by decide)).trans hdi
  have hzlen : word z.mem B a.length.offset = word s.mem B a.length.offset := by rw [hzm, hvm, hum]
  refine WP.mono (WP.keep [.rdx, .rcx, .r8] (Q := fun t =>
    t.gpr .rdx = pointerValue s.mem B b.pointer ∧ t.gpr .rcx = word s.mem B a.length.offset ∧
    t.gpr .r8 = 0 ∧ t.mem = z.mem) ?_ rfl) fun t ⟨⟨htd, htc, ht8, htm⟩, hkt⟩ =>
      ⟨(hkt.gpr (by decide)).trans hzsi, htd, htc, ht8, htm.trans (hzm.trans (hvm.trans hum)),
        (hksz.trans hkt).mono (by decide)⟩
  xrun [hza, State.ea, Core.field, hzdi, fieldAddress, hzlen,
    (hs.congr hksz.2.2).ld (Nat.le_trans (VG.Proof.Dsa.field_bounds a.length).2 hZ)]

end VG.Proof.Dsa.X86_64
