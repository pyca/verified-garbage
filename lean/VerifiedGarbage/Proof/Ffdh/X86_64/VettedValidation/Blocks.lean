module

public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.State
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! Short public controls and table-address setup for each recognition record. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.VettedValidation
open VG.Impl.Ffdh.VettedGroups

theorem header_ok {s : State} {base src : Addr} {k : Nat} {dom : List Byte}
    (h : Context base src k dom s) (g : Group) (fit : g.len < 2 ^ 31) :
    WP isa (.block (header g)) s fun t =>
      t.zf = some (decide (g.len = k)) ∧ t.gpr .rdx = 1 ∧
      t.mem = s.mem ∧ Keep clobbers s t := by
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t =>
    t.zf = some (decide (g.len = k)) ∧ t.gpr .rdx = 1 ∧ t.mem = s.mem) ?_ rfl) ?_
  · xrun [header, ea_at, h.baseReg, h.readWidth, h.width, sx_ofNat fit,
      VG.Proof.Bignum.X86_64.ofNat_sub_beq (j := k) (N := g.len) (by have := h.upper; omega) (by omega)]
    simp only [eq_comm]
  · rintro t ⟨⟨zero, value, mem⟩, rest⟩
    exact ⟨zero, value, mem, rest.mono (by decide)⟩

theorem args_ok {s : State} {base src table : Addr} {k offset : Nat} {dom : List Byte}
    (h : Context base src k dom s) (sym : s.syms tableSym = table)
    (fit : offset + 8 < 2 ^ 31) :
    WP isa (.block (compareArgs offset)) s fun t =>
      t.gpr .rsi = table + BitVec.ofNat 64 (offset + 8) ∧
      t.gpr .rcx = BitVec.ofNat 64 dom.length ∧ t.mem = s.mem ∧ Keep clobbers s t := by
  refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun t =>
    t.gpr .rsi = table + BitVec.ofNat 64 (offset + 8) ∧
    t.gpr .rcx = BitVec.ofNat 64 dom.length ∧ t.mem = s.mem) ?_ rfl) ?_
  · xrun [compareArgs, sym, sx_ofNat fit, ea_at, h.baseReg, h.readLength, h.length]
  · rintro t ⟨⟨ptr, length, mem⟩, rest⟩
    exact ⟨ptr, length, mem, rest.mono (by decide)⟩

theorem test_ok (s : State) :
    WP isa (.block [.alu .test .rdx (.reg .rdx)]) s fun t =>
      t.zf = some (s.gpr .rdx == 0) ∧ t.mem = s.mem ∧ Keep clobbers s t := by
  refine WP.mono (WP.keep [.rdx] (Q := fun t =>
    t.zf = some (s.gpr .rdx == 0) ∧ t.mem = s.mem) (by xrun [BitVec.and_self]) rfl) ?_
  rintro t ⟨⟨zero, mem⟩, rest⟩
  exact ⟨zero, mem, rest.mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.VettedValidation
