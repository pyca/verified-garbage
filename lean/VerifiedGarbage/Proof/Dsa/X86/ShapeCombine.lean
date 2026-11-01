module
public import VerifiedGarbage.Impl.Dsa.X86.Shape
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Weierstrass.PointContract

/-! # Execution of the supported-domain mask combination -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86
open VG.Impl.Mont.X86

abbrev shapeWord (s : State) (base : Addr) (offset : Nat) : BitVec 32 :=
  s.mem.readW (off base offset) 32

theorem shapeCombine_ok {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hz : 8256 ≤ size) :
    WP isa (.block Shape.combine) s fun t =>
      shapeWord t base (Layout.field .mask) =
        ((shapeWord s base 32 &&& shapeWord s base 44) |||
          ((shapeWord s base 48 ||| shapeWord s base 44 ||| shapeWord s base 52) &&& shapeWord s base 36) |||
          (shapeWord s base 40 &&& shapeWord s base 52)) &&& shapeWord s base 56 ∧
      Keeps [.eax, .ebx] s t ∧ Outside base (Layout.field .mask) 4 s.mem t.mem := by
  unfold Shape.combine
  refine wp_movS (readSrc_sc hs (d := 32) (by omega)) fun s1 u1 _ => ?_
  have hs1 := hs.of_keeps u1.keeps (by decide)
  refine wp_logicS (.inl rfl) (readSrc_sc hs1 (d := 44) (by omega)) fun s2 u2 => ?_
  have hs2 := hs1.of_keeps u2.keeps (by decide)
  refine wp_movS (readSrc_sc hs2 (d := 48) (by omega)) fun s3 u3 _ => ?_
  have hs3 := hs2.of_keeps u3.keeps (by decide)
  refine wp_orS (readSrc_sc hs3 (d := 44) (by omega)) fun s3a u3a => ?_
  have hs3a := hs3.of_keeps u3a.keeps (by decide)
  refine wp_orS (readSrc_sc hs3a (d := 52) (by omega)) fun s4 u4 => ?_
  have hs4 := hs3a.of_keeps u4.keeps (by decide)
  refine wp_logicS (.inl rfl) (readSrc_sc hs4 (d := 36) (by omega)) fun s5 u5 => ?_
  have hs5 := hs4.of_keeps u5.keeps (by decide)
  refine wp_orS rfl fun s6 u6 => ?_
  have hs6 := hs5.of_keeps u6.keeps (by decide)
  refine wp_movS (readSrc_sc hs6 (d := 40) (by omega)) fun s7 u7 _ => ?_
  have hs7 := hs6.of_keeps u7.keeps (by decide)
  refine wp_logicS (.inl rfl) (readSrc_sc hs7 (d := 52) (by omega)) fun s8 u8 => ?_
  have hs8 := hs7.of_keeps u8.keeps (by decide)
  refine wp_orS rfl fun s9 u9 => ?_
  have hs9 := hs8.of_keeps u9.keeps (by decide)
  refine wp_logicS (.inl rfl) (readSrc_sc hs9 (d := 56) (by omega)) fun s10 u10 => ?_
  have hs10 := hs9.of_keeps u10.keeps (by decide)
  refine wp_storeS (hs10.ea (d := Layout.field .mask) (by change 8244 < size; omega))
    (hs10.write (d := Layout.field .mask) (n := 4) (by change 8248 ≤ size; omega)) fun t mt => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [shapeWord, mt.mem, Mem.readW_writeW_self32, u10.gpr, u9.gpr,
      u8.other .eax (by decide), u7.other .eax (by decide), u6.gpr,
      u5.other .eax (by decide), u4.other .eax (by decide), u3a.other .eax (by decide), u3.other .eax (by decide),
      u2.gpr, u1.gpr, u5.gpr, u4.gpr, u3a.gpr, u3.gpr, u8.gpr, u7.gpr]
    simp only [ite_true, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3a.mem, u3.mem, u2.mem, u1.mem, shapeWord]
  · exact (((((((((((u1.keeps.mono (by decide)).widen u2.keeps).widen u3.keeps).widen u3a.keeps).widen u4.keeps).widen
      u5.keeps).widen u6.keeps).widen u7.keeps).widen u8.keeps).widen u9.keeps).widen u10.keeps).trans (mt.keeps _)
  · rw [mt.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3a.mem, u3.mem, u2.mem, u1.mem]
    exact writeW32_outside _ _ _ (by change 8248 ≤ 2 ^ 64; decide)

end VG.Proof.Dsa.X86
