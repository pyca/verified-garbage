module

public import VerifiedGarbage.Proof.Dsa.X86.ShapeCombine
import VerifiedGarbage.Proof.Ecdsa.X86.Flags
import VerifiedGarbage.Proof.Mont.X86.Csub
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # Branch-free clamping to the actual subgroup byte width -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86
open VG.Impl.Mont.X86 VG.Proof.Ecdsa.X86

theorem digestClamp_ok {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hz : 8256 ≤ size) :
    WP isa (.block Shape.digestClamp) s fun t =>
      (shapeWord t base (Layout.field .digestPrefixLen)).toNat =
        min (shapeWord s base (Layout.field .digestLen)).toNat (s.gpr .edx).toNat ∧
      Keeps [.eax, .ebx, .edx] s t ∧ Outside base (Layout.field .digestPrefixLen) 4 s.mem t.mem := by
  unfold Shape.digestClamp
  refine wp_movS (readSrc_sc hs (d := Layout.field .digestLen) (by change 8240 ≤ size; omega)) fun s1 u1 _ => ?_
  refine wp_cmp fun s2 u2 cf2 _ => ?_
  refine wp_sbbS rfl cf2 fun s3 u3 _ => ?_
  refine wp_logicS (.inr rfl) rfl fun s4 u4 => ?_
  refine wp_logicS (.inl rfl) rfl fun s5 u5 => ?_
  refine wp_logicS (.inr rfl) rfl fun s6 u6 => ?_
  have K : Keeps [.eax, .ebx, .edx] s s6 :=
    (((((u1.keeps.mono (by decide)).widen (u2.keeps [])).widen u3.keeps).widen u4.keeps).widen u5.keeps).widen u6.keeps
  have hs6 := hs.of_keeps K (by decide)
  refine wp_storeS (hs6.ea (d := Layout.field .digestPrefixLen) (by change 8240 < size; omega))
    (hs6.write (d := Layout.field .digestPrefixLen) (n := 4) (by change 8244 ≤ size; omega)) fun t mt =>
    WP.block_nil ⟨?_, K.trans (mt.keeps _), ?_⟩
  · rw [shapeWord, mt.mem, Mem.readW_writeW_self32, u6.gpr, u5.other .edx (by decide),
      u4.other .edx (by decide), u3.other .edx (by decide), u2.gpr, u1.other .edx (by decide),
      u5.gpr, u4.gpr, u4.other .ebx (by decide), u3.gpr, sbb_mask,
      u3.other .eax (by decide), u3.other .edx (by decide), u2.gpr,
      u1.gpr, u1.other .edx (by decide)]
    simp only [reduceCtorEq, ite_false, ite_true, mask32, decide_eq_true_eq]
    have E := select_val (s.gpr .edx) (shapeWord s base (Layout.field .digestLen))
      (decide ((shapeWord s base (Layout.field .digestLen)).toNat < (s.gpr .edx).toNat))
    simp only [decide_eq_true_eq] at E
    rw [E]
    split <;> simp only [Nat.min_def] <;> split <;> omega
  · rw [mt.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    exact writeW32_outside _ _ _ (by change 8244 ≤ 2 ^ 64; decide)

end VG.Proof.Dsa.X86
