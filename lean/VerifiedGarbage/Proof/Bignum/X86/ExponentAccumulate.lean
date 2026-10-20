module

public import VerifiedGarbage.Impl.Bignum.X86.ExponentCheck
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Bignum.X86.ByteOps
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Native-word effects of the public-exponent accumulation step -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86

theorem rotate_mask_byte (x : BitVec 32) :
    x.rotateRight 24 &&& 0xffffff00 = x <<< 8 := by
  change x.rotateRight (32 - 8) &&& (BitVec.allOnes 32 <<< 8) = x <<< 8
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_allOnes, BitVec.getLsbD_rotateRight]
  simp only [hp, decide_true, Bool.true_and]
  by_cases h : p < 8
  · simp [h]
  · simp only [h, decide_false, Bool.not_false, Bool.true_and,
      ↓reduceIte,
      decide_eq_true (show p - 8 < 32 by omega), Bool.and_true]

theorem exponentAccumulate_ok (s : State) {p : Addr}
    (ptr : s.ea ⟨.esi, 0⟩ = p) (read : InRegions (s.rd ++ s.wr) p 1) :
    WP isa (.block exponentAccumulate) s fun t =>
      t.gpr .ebx = (s.gpr .ebx <<< 8) + (s.mem p).setWidth 32 ∧
      t.gpr .edx = (s.gpr .edx <<< 8) + (s.gpr .ebx >>> 24) ∧
      t.zf = some (((((s.gpr .edx <<< 8) + (s.gpr .ebx >>> 24)) >>> 1)) == 0) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .edx, .ebp] s t := by
  unfold exponentAccumulate
  refine wp_loadByte ptr read fun s1 u1 => ?_
  refine wp_movS rfl fun s2 u2 _ => ?_
  refine wp_shr (by decide) fun s3 u3 _ => ?_
  refine wp_ror (by decide) fun s4 u4 => ?_
  refine wp_logicS (.inl rfl) rfl fun s5 u5 => ?_
  refine wp_addS rfl fun s6 u6 _ => ?_
  refine wp_ror (by decide) fun s7 u7 => ?_
  refine wp_logicS (.inl rfl) rfl fun s8 u8 => ?_
  refine wp_addS rfl fun s9 u9 _ => ?_
  refine wp_movS rfl fun s10 u10 _ => ?_
  refine wp_shr (by decide) fun s11 u11 _ => ?_
  refine wp_cmpS rfl fun t ft zt => WP.block_nil ?_
  have high : s6.gpr .edx = (s.gpr .edx <<< 8) + (s.gpr .ebx >>> 24) := by
    rw [u6.gpr, u5.gpr, u4.gpr, u3.other .edx (by decide), u2.other .edx (by decide),
      u1.other .edx (by decide), u5.other .ebp (by decide),
      u4.other .ebp (by decide), u3.gpr, u2.gpr, u1.other .ebx (by decide)]
    simp only [ite_true, BitVec.ofNat_eq_ofNat]
    exact congrArg (fun v => v + (s.gpr .ebx >>> 24)) (rotate_mask_byte (s.gpr .edx))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [ft.gpr, u11.other .ebx (by decide), u10.other .ebx (by decide), u9.gpr,
      u8.gpr, u7.gpr, u6.other .ebx (by decide), u5.other .ebx (by decide),
      u4.other .ebx (by decide), u3.other .ebx (by decide), u2.other .ebx (by decide),
      u1.other .ebx (by decide), u8.other .eax (by decide),
      u7.other .eax (by decide), u6.other .eax (by decide), u5.other .eax (by decide),
      u4.other .eax (by decide), u3.other .eax (by decide), u2.other .eax (by decide), u1.gpr]
    simp only [ite_true, BitVec.ofNat_eq_ofNat]
    exact congrArg (fun v => v + (s.mem p).setWidth 32) (rotate_mask_byte (s.gpr .ebx))
  · rw [ft.gpr, u11.other .edx (by decide), u10.other .edx (by decide),
      u9.other .edx (by decide), u8.other .edx (by decide), u7.other .edx (by decide), high]
  · rw [zt, u11.gpr, u10.gpr, u9.other .edx (by decide),
      u8.other .edx (by decide), u7.other .edx (by decide), high]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero]
  · rw [ft.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem,
      u4.mem, u3.mem, u2.mem, u1.mem]
  · exact (((((((((((u1.keeps.mono (by decide)).widen u2.keeps).widen u3.keeps).widen
      u4.keeps).widen u5.keeps).widen u6.keeps).widen u7.keeps).widen u8.keeps).widen
      u9.keeps).widen u10.keeps).widen u11.keeps).trans (ft.keeps _)

end VG.Proof.Bignum.X86
