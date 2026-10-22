module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.TransferValues
public import VerifiedGarbage.Proof.MillerRabin.Words
import VerifiedGarbage.Proof.Mont.Words32Offset
import VerifiedGarbage.Proof.Mont.Words32Parts
import VerifiedGarbage.Proof.Bignum.ByteWords

/-! Read the transferred numbers through the shared Miller–Rabin representation. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation

theorem compact_num_val32 (m : Mem) (base : Addr) (n j : Nat) :
    Spec.Rsa.Mont.numAt m (off base Layout.arithmetic) n j =
      val32 m base (Layout.arithmetic + Spec.Rsa.Mont.arrAt n j) (2 * n) := by
  rw [VG.Proof.MillerRabin.montNum_val32, val32_off]

theorem compact_numbers_shared {s : State} {base : Addr} {n bytes : Nat}
    (scr : Scr s base bytes) (hn : n ≤ 48) (capacity : 40960 ≤ bytes) :
    WP isa (transferWords (compactTransfers n)) s fun t =>
      (∀ j ∈ [(0, 0), (5, 3), (7, 4), (9, 6), (10, 7), (27, 8)],
        Spec.Rsa.Mont.numAt t.mem (off base Layout.arithmetic) n j.1 =
          wordsVal s.mem base (slot n j.2) n) ∧
      word t.mem (off base Layout.arithmetic) (Spec.Rsa.Mont.arrAt n 27 + 8 * n) =
        word s.mem base (slot n 8 + 8 * n) ∧
      Outs base (transferRanges (compactTransfers n)) s.mem t.mem ∧ Keeps [.eax] s t := by
  refine WP.mono (compact_numbers scr hn capacity) fun t ⟨values, exp, tail, F, K⟩ => ⟨?_, ?_, F, K⟩
  · intro j hj
    rw [compact_num_val32, wordsVal_eq_val32]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact values (0, 0) (by simp)
    · exact values (5, 3) (by simp)
    · exact values (7, 4) (by simp)
    · exact values (9, 6) (by simp)
    · exact values (10, 7) (by simp)
    · exact exp
  · apply BitVec.eq_of_toNat_eq
    rw [word_toNat_val32, val32_off, word_toNat_val32]
    rw [show Layout.arithmetic + (Spec.Rsa.Mont.arrAt n 27 + 8 * n) =
      Layout.arithmetic + Spec.Rsa.Mont.arrAt n 27 + 8 * n by omega]
    exact tail

end VG.Proof.Dsa.X86.Generation
