module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.StageReduction
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ReduceAt
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SaveReduction
import VerifiedGarbage.Proof.Dsa.Generation.PReduction

/-! Complete native modulus reduction and serialization reuse the shared arithmetic implementations. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86

def PReductionFrame (base : Addr) (sp : BitVec 32) (n : Nat) (s t : State) : Prop :=
  Frame [⟨base, montgomeryBytes⟩, ⟨off base Layout.arithmetic, Layout.arithmeticBytes⟩,
    ⟨off base Layout.p, 8 * n⟩, ⟨off base Layout.exponent, 8 * n⟩, below sp 40] s.mem t.mem

theorem p_reduce {s : State} {base : Addr} {bytes n qLen x q : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (room : CallRoom (s.gpr .esp) base bytes) (stack : StkOk (s.gpr .esp - 16#32) base bytes)
    (lower : 4 ≤ n) (upper : n ≤ 48) (qLower : 4 ≤ qLen) (qLength : qLen ≤ 8 * n) (qAligned : qLen % 4 = 0)
    (candidate : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off base Layout.shaped) (8 * n)) = x)
    (subgroup : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off base Layout.q) qLen) = q)
    (positive : 0 < q) (bound : 2 * q < 2 ^ (64 * n)) :
    WP isa (pReduce n qLen) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base Layout.p) (8 * n) = Spec.Dsa.encodeBE (8 * n) (x + 1 - x % (2 * q)) ∧
      Spec.Rsa.bytesAt t.mem (off base Layout.exponent) (8 * n) =
        Spec.Dsa.encodeBE (8 * n) ((x + 1 - x % (2 * q) - 1) / q) ∧
      PReductionFrame base (s.gpr .esp) n s t ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold pReduce
  refine WP.seq (WP.mono (stage_reduction scr capacity lower upper qLower qLength qAligned candidate subgroup)
    fun a ⟨xa, qa, FA, KA⟩ => ?_)
  have Sa := scr.of_keeps KA (by decide)
  have Ra : CallRoom (a.gpr .esp) base bytes := by rw [KA.1 .esp (by decide)]; exact room
  have stackA : StkOk (a.gpr .esp - 16#32) base bytes := by rw [KA.1 .esp (by decide)]; exact stack
  refine WP.seq (WP.mono (reduce_at Sa capacity Ra stackA lower upper xa qa positive bound)
    fun b ⟨p, e, FB, KB⟩ => ?_)
  refine WP.mono (save_reduction (Sa.of_keeps KB (by decide)) capacity lower upper p e)
    fun t ⟨pBytes, eBytes, FT, KT⟩ => ?_
  rw [← VG.Proof.Dsa.Generation.pReduction_generatorExponent x positive] at eBytes
  refine ⟨pBytes, eBytes, ?_, (KA.trans KB).trans KT⟩
  have first : PReductionFrame base (s.gpr .esp) n s a := FA.mono (by simp)
  have middle : PReductionFrame base (s.gpr .esp) n a b := by
    rw [KA.1 .esp (by decide)] at FB
    apply FB.sub
    intro region hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨off base Layout.arithmetic, Layout.arithmeticBytes⟩, by simp, fun _ h => h⟩
    · exact ⟨below (s.gpr .esp) 40, by simp, below_sub (by decide) room.low⟩
  exact (first.trans middle).trans (FT.mono (by simp))

end VG.Proof.Dsa.X86.Generation
