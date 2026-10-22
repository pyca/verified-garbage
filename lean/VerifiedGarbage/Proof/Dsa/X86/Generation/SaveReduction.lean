module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ReductionTransfers
public import VerifiedGarbage.Proof.Dsa.X86.CoreStore
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Proof.Bignum.OctetFrame
import VerifiedGarbage.Proof.Mont.OutsFrame
import VerifiedGarbage.Proof.Mont.Words32Offset
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! Serialize the reduced modulus and generator exponent with the existing DSA stores. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Rsa.X86.Keys (num)

def SaveReductionFrame (base : Addr) (n : Nat) (s t : State) : Prop :=
  Frame [⟨base, montgomeryBytes⟩, ⟨off base Layout.p, 8 * n⟩,
    ⟨off base Layout.exponent, 8 * n⟩] s.mem t.mem

theorem save_reduction {s : State} {base : Addr} {bytes n p exponent : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (lower : 4 ≤ n) (upper : n ≤ 48)
    (candidate : num s.mem (off base Layout.arithmetic) (2 * n) 5 = p)
    (power : num s.mem (off base Layout.arithmetic) (2 * n) 0 = exponent) :
    WP isa (saveReduction n) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base Layout.p) (8 * n) = Spec.Dsa.encodeBE (8 * n) p ∧
      Spec.Rsa.bytesAt t.mem (off base Layout.exponent) (8 * n) = Spec.Dsa.encodeBE (8 * n) exponent ∧
      SaveReductionFrame base n s t ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have parentFit (i : Nat) (hi : i < 9) : slot n i + 8 * n ≤ montgomeryBytes := by
    have := slot_bound (n := n) hi
    simp only [contextBytes, slot, stride, montgomeryBytes] at *
    omega
  unfold saveReduction
  refine WP.seq (WP.mono (transfer_words scr ((reduction_output_plan upper).mono capacity)) fun a ⟨values, O, K⟩ => ?_)
  have vp := values ⟨2 * n, slot n 6, Layout.arithmetic + VG.Impl.Rsa.X86.Keys.slot (2 * n) 5⟩
    (by simp [reductionOutputTransfers])
  have ve := values ⟨2 * n, slot n 8, Layout.arithmetic + VG.Impl.Rsa.X86.Keys.slot (2 * n) 0⟩
    (by simp [reductionOutputTransfers])
  change val32 s.mem (off base Layout.arithmetic) (VG.Impl.Rsa.X86.Keys.slot (2 * n) 5) (2 * n) = p at candidate
  change val32 s.mem (off base Layout.arithmetic) (VG.Impl.Rsa.X86.Keys.slot (2 * n) 0) (2 * n) = exponent at power
  rw [val32_off] at candidate power
  have pA : wordsVal a.mem base (slot n 6) n = p := by rw [wordsVal_eq_val32, vp, candidate]
  have eA : wordsVal a.mem base (slot n 8) n = exponent := by rw [wordsVal_eq_val32, ve, power]
  have Sa := scr.of_keeps K (by decide)
  refine WP.seq (WP.mono (VG.Proof.Dsa.X86.coreStore_ok Sa (by unfold VG.Impl.Dsa.X86.Layout.saved; omega)
    (by omega : (8 * n + 7) / 8 = n) (Nat.le_trans (parentFit 6 (by decide)) (by unfold montgomeryBytes; omega))
    (by omega) (Nat.le_refl _) (by omega) (by unfold Layout.p; omega)
    (.inl (by have := parentFit 6 (by decide); unfold montgomeryBytes Layout.p at *; omega)))
    fun b ⟨pBytes, KP, OP⟩ => ?_)
  rw [pA] at pBytes
  have Sb := Sa.of_keeps KP (by decide)
  have eB : wordsVal b.mem base (slot n 8) n = exponent := by
    rw [wordsVal_eq_val32, OP.val32 (d := slot n 8) (k := 2 * n)
      (.inl (by have := parentFit 8 (by decide); unfold montgomeryBytes Layout.p at *; omega))
      (by have := parentFit 8 (by decide); unfold montgomeryBytes at *; omega), ← wordsVal_eq_val32]
    exact eA
  refine WP.mono (VG.Proof.Dsa.X86.coreStoreAt_ok Sb (by unfold VG.Impl.Dsa.X86.Layout.saved; omega)
    (Nat.le_trans (parentFit 8 (by decide)) (by unfold montgomeryBytes; omega))
    (by omega : 4 ≤ 8 * n) (Nat.le_refl _) (by omega) (by unfold Layout.exponent; omega)
    (.inl (by have := parentFit 8 (by decide); unfold montgomeryBytes Layout.exponent at *; omega)))
    fun t ⟨eBytes, KE, OE⟩ => ?_
  rw [eB] at eBytes
  refine ⟨?_, eBytes, ?_, ((K.mono (by decide)).trans (KP.mono (by decide))).trans (KE.mono (by decide))⟩
  · rw [OE.bytesAt (offset := Layout.p) (len := 8 * n) (.inl (by unfold Layout.p Layout.exponent; omega))
      (by unfold Layout.p; omega)]
    exact pBytes
  · have parent : Outside base 0 montgomeryBytes s.mem a.mem := O.enclose (by
      intro region hr
      simp only [transferRanges, reductionOutputTransfers, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        simp only [slot, stride, montgomeryBytes] <;> omega)
    have first : SaveReductionFrame base n s a := by
      have F := parent.frameAt (by decide)
      simp only [off, BitVec.add_zero] at F
      exact F.mono (by simp)
    exact (first.trans ((OP.frameAt (by unfold Layout.p; omega)).mono (by simp))).trans
      ((OE.frameAt (by unfold Layout.exponent; omega)).mono (by simp))

end VG.Proof.Dsa.X86.Generation
