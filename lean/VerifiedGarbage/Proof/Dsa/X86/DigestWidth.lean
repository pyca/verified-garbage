module

public import VerifiedGarbage.Proof.Dsa.X86.ShapeCombine
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # Selecting the digest width from mutually exclusive subgroup masks -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86
open VG.Impl.Mont.X86 VG.Proof.Ecdsa.X86

theorem digestWidth_value {qBits : Nat} (hq : qBits = 160 ∨ qBits = 224 ∨ qBits = 256) :
    ((mask32 (qBits = 224) &&& 28) ||| (mask32 (qBits = 160) &&& 20) |||
      (mask32 (qBits = 256) &&& 32)).toNat = qBits / 8 := by
  rcases hq with rfl | rfl | rfl <;> decide

theorem digestWidth_ok {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hz : 64 ≤ size) :
    WP isa (.block Shape.prefixWidth) s fun t =>
      t.gpr .edx = ((shapeWord s base 48 &&& 28) ||| (shapeWord s base 44 &&& 20) |||
        (shapeWord s base 52 &&& 32)) ∧ Keeps [.eax, .edx] s t ∧ t.mem = s.mem := by
  unfold Shape.prefixWidth
  refine wp_movS (readSrc_sc hs (d := 44) (by omega)) fun s1 u1 _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s2 u2 => ?_
  have hs2 := (hs.of_keeps u1.keeps (by decide)).of_keeps u2.keeps (by decide)
  refine wp_movS (readSrc_sc hs2 (d := 48) (by omega)) fun s3 u3 _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s4 u4 => ?_
  refine wp_orS rfl fun s5 u5 => ?_
  have hs5 := ((hs2.of_keeps u3.keeps (by decide)).of_keeps u4.keeps (by decide)).of_keeps u5.keeps (by decide)
  refine wp_movS (readSrc_sc hs5 (d := 52) (by omega)) fun s6 u6 _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s7 u7 => ?_
  refine wp_orS rfl fun t u8 => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [u8.gpr, u7.other .edx (by decide), u6.other .edx (by decide), u5.gpr,
      u4.gpr, u3.gpr, u4.other .eax (by decide), u3.other .eax (by decide),
      u2.gpr, u1.gpr, u7.gpr, u6.gpr]
    simp only [ite_true, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, shapeWord]
  · exact (((((((u1.keeps.mono (by decide)).widen u2.keeps).widen u3.keeps).widen u4.keeps).widen
      u5.keeps).widen u6.keeps).widen u7.keeps).widen u8.keeps
  · rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]

end VG.Proof.Dsa.X86
