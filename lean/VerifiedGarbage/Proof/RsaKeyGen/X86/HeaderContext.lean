module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderFrame
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderRead
import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderLayout
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext

/-! # The public header prepares the native callable Miller–Rabin context -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Header
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86

theorem low_word (m : Mem) (base : Addr) (d : Nat) : w32 m base d = (word m base d).toNat % 2 ^ 32 := by
  rw [word_eq_w32, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (m.readW (off base d) 32).isLt]

theorem context_ok {g : Geometry} (v : g.Valid) {s : State} (scratch : Scr s g.W g.L) :
    WP isa (.block (VG.Impl.RsaKeyGen.X86.Header.code g.w)) s fun t =>
      Context g t ∧ Outs g.W ranges s.mem t.mem ∧ Keeps [.eax, .edx] s t ∧
      t.mem = headerMemory g.W (s.gpr .edi) g.w s.mem := by
  refine WP.mono (code_ok scratch v.headerFit) fun t ⟨M, K⟩ => ?_
  have wBound : g.w < 2 ^ 32 := by have := v.maxWidth; omega
  have strideBound : VG.Impl.Bignum.X86.PublicContext.stride g.w < 2 ^ 32 := by
    have := v.maxWidth
    unfold VG.Impl.Bignum.X86.PublicContext.stride
    omega
  have baseBound : g.W.toNat < 2 ^ 32 := by have := scratch.nowrap; have := v.headerFit; omega
  refine ⟨⟨⟨K.2.2 ▸ scratch.wr, scratch.nowrap⟩, ?_, ?_, ?_, ?_⟩, M ▸ header_frame, K, M⟩
  · rw [PtrAt, K.1 .edi (by decide), scratch.edi_toNat, Nat.add_zero, Nat.mod_eq_of_lt baseBound]
  · rw [M, low_word, VG.Proof.Mont.word, header_width, zeroHigh, BitVec.toNat_setWidth_of_le (by decide),
      BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_eq_of_lt wBound]
  · rw [M, low_word, VG.Proof.Mont.word, header_stride, zeroHigh, BitVec.toNat_setWidth_of_le (by decide),
      BitVec.toNat_ofNat, Nat.mod_mod, Nat.mod_eq_of_lt strideBound]
    rfl
  · intro j index
    rw [M, low_word, VG.Proof.Mont.word, header_pointer index, zeroHigh, BitVec.toNat_setWidth_of_le (by decide),
      Nat.mod_eq_of_lt (s.gpr .edi + BitVec.ofNat 32 (VG.Impl.Bignum.X86.PublicContext.slot g.w j)).isLt,
      BitVec.toNat_add, BitVec.toNat_ofNat, scratch.edi_toNat, Prepared.slot_eq]
    omega

end VG.Proof.RsaKeyGen.X86.Header
