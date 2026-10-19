module

public import VerifiedGarbage.Proof.Bignum.X86.CrtValidate
public import VerifiedGarbage.Proof.Bignum.X86.CrtComputeFrame

/-! # Validation and private arithmetic preserve a common acceptance decision -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86.Crt VG.Proof.Ecdsa.X86

def checkedRanges (n : Nat) : List (Nat × Nat) := validationRanges n ++ computeRanges n

/-- The validation's changes lie within the working space. -/
theorem validation_outside {n bytes : Nat} {base : Addr} {m m' : Mem}
    (O : Outs base (validationRanges n) m m') (hz : size n ≤ bytes) : Outside base 0 bytes m m' := by
  have := slot_bound (n := n) (show productSlot < 20 by decide)
  refine Outs.outside O ?_
  intro r hr
  simp only [validationRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  unfold stride at this
  rcases hr with rfl | rfl | rfl <;> simp only [multiplierOffset, acceptanceOffset, size, slot, stride] at * <;> omega

theorem checkedCompute_ok {s : State} {base : Addr} {bytes n : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hn32 : 128 * n < 2 ^ 32) (hz : size n ≤ bytes)
    (modulus : wordsVal s.mem base (slot n modulusSlot) n = wordsVal s.mem base (slot n modulusSlot) (2 * n))
    (args : PowerArgs base bytes n s) :
    WP isa (.seq (validate n) (compute n)) s fun t =>
      t.mem.readW (off base acceptanceOffset) 32 = mask32
        ((wordsVal s.mem base (slot n pSlot) n * wordsVal s.mem base (slot n qSlot) n =
          wordsVal s.mem base (slot n modulusSlot) n) ∧
          wordsVal s.mem base (slot n inputSlot) n < wordsVal s.mem base (slot n modulusSlot) n ∧
          wordsVal s.mem base (slot n inverseSlot) n < wordsVal s.mem base (slot n pSlot) n) ∧
      wordsVal t.mem base (slot n resultSlot) (2 * n) =
        resultValue (wordsVal s.mem base (slot n pSlot) n) (wordsVal s.mem base (slot n qSlot) n)
          (wordsVal s.mem base (slot n dpSlot) n) (wordsVal s.mem base (slot n dqSlot) n)
          (wordsVal s.mem base (slot n inverseSlot) n) (wordsVal s.mem base (slot n inputSlot) n) % 2 ^ (128 * n) ∧
      Outs base (checkedRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  have fit : size n ≤ 2 ^ 64 := by have := hs.nowrap; omega
  refine WP.seq (WP.mono (validate_ok hs hn hz modulus) fun u ⟨A, O, K⟩ => ?_)
  have args' := args.keep K (by decide) (validation_outside O hz)
    (validation_value O (i := pSlot) (by decide) (by omega) fit)
    (validation_value O (i := dpSlot) (by decide) (by omega) fit)
    (validation_value O (i := qSlot) (by decide) (by omega) fit)
    (validation_value O (i := dqSlot) (by decide) (by omega) fit)
  refine WP.mono (compute_ok (hs.of_keeps K (by decide)) hn hn32 hz args') fun t ⟨V, Ot, Kt⟩ => ?_
  refine ⟨(compute_header Ot (by decide) (by decide)).trans A, ?_, ?_, (K.mono (by decide)).trans Kt⟩
  · rw [V, validation_value O (i := pSlot) (by decide) (by omega) fit,
      validation_value O (i := qSlot) (by decide) (by omega) fit,
      validation_value O (i := dpSlot) (by decide) (by omega) fit,
      validation_value O (i := dqSlot) (by decide) (by omega) fit,
      validation_value O (i := inverseSlot) (by decide) (by omega) fit,
      validation_value O (i := inputSlot) (by decide) (by omega) fit]
  · exact (O.mono (by intro r hr; exact List.mem_append_left _ hr)).trans
      (Ot.mono (by intro r hr; exact List.mem_append_right _ hr))

end VG.Proof.Bignum.X86.Crt
