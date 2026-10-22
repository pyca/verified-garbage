module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ReductionTransfers
public import VerifiedGarbage.Proof.Dsa.X86.Generation.LoadNumber
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PreparationReads
import VerifiedGarbage.Proof.Bignum.OctetFrame
import VerifiedGarbage.Proof.Mont.OutsFrame
import VerifiedGarbage.Proof.Mont.Words32Offset
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Framework.Offset

/-! Stage the shaped modulus input and saved subgroup through the existing loaders and copies. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem parent_preparation_frame {s t : State} {base : Addr} {d size : Nat}
    (O : Outside base d size s.mem t.mem) (fit : d + size ≤ montgomeryBytes) :
    PreparationFrame base (s.gpr .esp) s t := by
  apply (O.frameAt (Nat.lt_of_le_of_lt fit (by decide))).sub
  intro region hr
  rw [List.mem_singleton.mp hr]
  exact ⟨⟨base, montgomeryBytes⟩, by simp, Offset.sub_base base fit⟩

theorem stage_reduction {s : State} {base : Addr} {bytes n qLen x q : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (lower : 4 ≤ n) (upper : n ≤ 48)
    (qLower : 4 ≤ qLen) (qLength : qLen ≤ 8 * n) (qAligned : qLen % 4 = 0)
    (candidate : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off base Layout.shaped) (8 * n)) = x)
    (subgroup : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off base Layout.q) qLen) = q) :
    WP isa (stageReduction n qLen) s fun t =>
      VG.Proof.Rsa.X86.Keys.num t.mem (off base Layout.arithmetic) (2 * n) 0 = x ∧
      VG.Proof.Rsa.X86.Keys.num t.mem (off base Layout.arithmetic) (2 * n) 2 = q ∧
      PreparationFrame base (s.gpr .esp) s t ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have parentFit (i : Nat) (hi : i < 9) : slot n i + 8 * n ≤ montgomeryBytes := by
    have := slot_bound (n := n) hi
    simp only [contextBytes, slot, stride, montgomeryBytes] at *
    omega
  unfold stageReduction
  refine WP.seq (WP.mono (load_number scr capacity upper (by omega : 4 ≤ 8 * n) (Nat.le_refl _) (by omega)
    (by decide : 16384 ≤ Layout.shaped) (by unfold Layout.shaped; omega)
    (by unfold contextBytes slot stride; omega)) fun a ⟨xa, OA, KA⟩ => ?_)
  have Sa := scr.of_keeps KA (by decide)
  refine WP.seq (WP.mono (load_number Sa capacity upper qLower qLength qAligned (by decide : 16384 ≤ Layout.q)
    (by unfold Layout.q; omega) (by have := slot_bound (n := n) (i := 2) (by decide); unfold stride at *; omega))
    fun b ⟨qb, OB, KB⟩ => ?_)
  have xb : val32 b.mem base (slot n 0) (2 * n) = x := by
    rw [OB.val32 (d := slot n 0) (k := 2 * n)
      (.inl (by unfold slot stride; omega)) (by have := parentFit 0 (by decide); unfold montgomeryBytes at *; omega),
      ← wordsVal_eq_val32]
    exact xa.trans candidate
  have qbValue : val32 b.mem base (slot n 2) (2 * n) = q := by
    rw [← wordsVal_eq_val32, qb, OA.bytesAt (offset := Layout.q) (len := qLen)
      (.inr (by have := parentFit 0 (by decide); unfold montgomeryBytes Layout.q at *; omega))
      (by unfold Layout.q; omega)]
    exact subgroup
  have Sb := Sa.of_keeps KB (by decide)
  refine WP.mono (transfer_words Sb ((reduction_input_plan upper).mono capacity)) fun t ⟨values, O, KT⟩ => ?_
  have v0 := values ⟨2 * n, Layout.arithmetic + VG.Impl.Rsa.X86.Keys.slot (2 * n) 0, slot n 0⟩
    (by simp [reductionInputTransfers])
  have v2 := values ⟨2 * n, Layout.arithmetic + VG.Impl.Rsa.X86.Keys.slot (2 * n) 2, slot n 2⟩
    (by simp [reductionInputTransfers])
  refine ⟨?_, ?_, ?_, ((KA.mono (by decide)).trans (KB.mono (by decide))).trans (KT.mono (by decide))⟩
  · change val32 t.mem (off base Layout.arithmetic) (VG.Impl.Rsa.X86.Keys.slot (2 * n) 0) (2 * n) = x
    rw [val32_off, v0, xb]
  · change val32 t.mem (off base Layout.arithmetic) (VG.Impl.Rsa.X86.Keys.slot (2 * n) 2) (2 * n) = q
    rw [val32_off, v2, qbValue]
  · have first := parent_preparation_frame OA (parentFit 0 (by decide))
    have middle := parent_preparation_frame OB (parentFit 2 (by decide))
    rw [KA.1 .esp (by decide)] at middle
    apply (first.trans middle).trans
    have arithmetic : Outside base Layout.arithmetic Layout.arithmeticBytes b.mem t.mem := O.enclose (by
      intro r hr
      simp only [transferRanges, reductionInputTransfers, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        simp only [VG.Impl.Rsa.X86.Keys.slot, VG.Impl.Rsa.X86.Keys.hdr, VG.Impl.Rsa.X86.Keys.stride,
          Layout.arithmeticBytes] <;> omega)
    exact (arithmetic.frameAt (by decide)).mono (by simp)

end VG.Proof.Dsa.X86.Generation
