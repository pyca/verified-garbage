module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.WitnessContext
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ParentProduct
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CompactNumbers
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PreparationFrame
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.OutsFrame
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! Encode each sampled witness with the retained R-squared and the optimized kernel. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

def WitnessFrame (base : Addr) (sp : BitVec 32) (n : Nat) (s t : State) : Prop :=
  Frame [⟨off base (slot n 5), 8 * n⟩,
    ⟨off base montgomeryScratch, Spec.Rsa.MontMul.scratchBytes n⟩,
    ⟨off base (Layout.arithmetic + Spec.Rsa.Mont.arrAt n 5), 8 * n⟩,
    below sp 40] s.mem t.mem

private theorem witness_transfer_fit {n : Nat} (upper : n ≤ 48) :
    TransferFits 40960 (compactNumberTransfer n 5 5) := by
  simp only [TransferFits, compactNumberTransfer, Layout.arithmetic, Spec.Rsa.Mont.arrAt,
    Spec.Rsa.Mont.hdrBytes, slot, stride]
  omega

theorem encode_witness {s : State} {base : Addr} {bytes n candidate x : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (room : CallRoom (s.gpr .esp) base bytes)
    (C : WitnessContext base n candidate s) (positive : 0 < n) (upper : n ≤ 48)
    (odd : candidate % 2 = 1) (input : val32 s.mem base (slot n 5) (2 * n) = x) :
    WP isa (encodeWitness n) s fun t =>
      WitnessContext base n candidate t ∧
      Spec.Rsa.Mont.numAt t.mem (off base Layout.arithmetic) n 5 = x * 2 ^ (64 * n) % candidate ∧
      Spec.Rsa.Mont.numAt t.mem (off base Layout.arithmetic) n 5 < candidate ∧
      WitnessFrame base (s.gpr .esp) n s t ∧ Keeps [.eax, .ecx, .edx] s t := by
  have parentCapacity : montgomeryBytes ≤ bytes := by unfold montgomeryBytes; omega
  have rr : val32 s.mem base (slot n 4) (2 * n) = 2 ^ (64 * n) * 2 ^ (64 * n) % candidate := by
    rw [← wordsVal_eq_val32]; exact C.square
  unfold encodeWitness
  refine WP.seq (WP.mono (parent_product scr parentCapacity room C.parent positive upper
    (show 5 < 9 by decide) (show 5 < 9 by decide) (show 4 < 9 by decide) (by decide)
    (by rw [rr]; exact Nat.mod_lt _ (by have := C.parent.gt_one; omega)))
    fun u ⟨Pu, bound, value, Fsu, Ksu⟩ => ?_)
  rw [input, rr] at value
  have encoded := VG.Proof.Bignum.mont_encode (VG.Proof.Bignum.coprime_pow2 odd _) value
  rw [Nat.mod_eq_of_lt bound] at encoded
  have parentRoom : CallRoom ((parentState base s).gpr .esp) base montgomeryBytes :=
    ⟨room.low, room.apart.sub_right (Region.sub_prefix parentCapacity)⟩
  have same : ∀ j, j = 1 ∨ j = 3 ∨ j = 4 →
      wordsVal u.mem base (slot n j) n = wordsVal s.mem base (slot n j) n := by
    intro j hj
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact montgomery_slot_keep (s := parentState base s) C.parent.scr parentRoom Fsu positive upper (by decide) (by decide)
      (by omega) (by omega)
  have Cu : WitnessContext base n candidate u := ⟨Pu,
    (same 3 (.inr (.inl rfl))).trans C.ordinary, (same 4 (.inr (.inr rfl))).trans C.square,
    (same 1 (.inl rfl)).trans C.ceiling⟩
  have SU := scr.of_keeps Ksu (by decide)
  have fit := witness_transfer_fit upper
  have fit' : TransferFits bytes (compactNumberTransfer n 5 5) :=
    ⟨Nat.le_trans fit.1 capacity, Nat.le_trans fit.2.1 capacity, fit.2.2⟩
  refine WP.mono (word_transfer SU fit') fun t ⟨copy, Kt, Fcopy⟩ => ?_
  have copyFrame := Fcopy.frameAt (by
    have := fit.1; unfold compactNumberTransfer at this ⊢; omega)
  have arithmeticFrame : Frame [⟨off base Layout.arithmetic, Layout.arithmeticBytes⟩] u.mem t.mem :=
    copyFrame.sub (by
      intro r hr; rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_singleton_self _, Offset.sub base (by
        simp only [compactNumberTransfer, Spec.Rsa.Mont.arrAt, Spec.Rsa.Mont.hdrBytes]; omega)
        (by exact fit.1)⟩)
  have Ct := Cu.frame_keep Kt (by decide) (by decide) arithmeticFrame (by
    intro r hr; rw [List.mem_singleton.mp hr]; exact parent_arithmetic_apart base (Nat.le_refl _))
  have output : Spec.Rsa.Mont.numAt t.mem (off base Layout.arithmetic) n 5 =
      val32 u.mem base (slot n 5) (2 * n) := by
    rw [compact_num_val32]
    exact copy
  refine ⟨Ct, output.trans encoded, by rw [output]; exact bound, ?_, Ksu.trans (Kt.mono (by decide))⟩
  apply Frame.trans (Fsu.sub ?_) (copyFrame.sub ?_)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · intro r hr; rw [List.mem_singleton.mp hr]
    exact ⟨_, by simp [compactNumberTransfer, show 4 * (2 * n) = 8 * n by omega], fun _ h => h⟩

end VG.Proof.Dsa.X86.Generation
