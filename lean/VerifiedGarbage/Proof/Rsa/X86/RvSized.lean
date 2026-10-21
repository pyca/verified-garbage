module
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw

public import VerifiedGarbage.Proof.Rsa.X86.RvResult
import VerifiedGarbage.Proof.Rsa.X86.RvFusedDispatch
import VerifiedGarbage.Proof.Rsa.X86.RvFailure
import VerifiedGarbage.Proof.Bignum.MemoryFrame

/-! # Recovery and refusal for a selected public modulus width -/

@[expose] public section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

omit rsaBatchLaw in
theorem calculated_none_skip {g : CallGeometry} {m : Mem} (skip : ¬GoOn (product g m)) :
    (calculated g m).1 = none := by
  have refused : inputValue g m 2 * inputValue g m 1 < 2 ∨
      (inputValue g m 2 * inputValue g m 1 - 1) % 2 = 1 := by
    unfold GoOn product at skip
    grind
  unfold calculated Spec.Rsa.primesKey
  dsimp only
  split
  · unfold inputValue at refused
    rw [VG.Proof.Rsa.recoverPrimes_none refused]
  · rfl

omit rsaBatchLaw in
theorem written_failure {g : CallGeometry} {m : Mem} {t : State}
    (none : (calculated g m).1 = none)
    (p : Spec.Rsa.bytesAt t.mem (g.buffer 0).base (g.buffer 0).len = List.replicate (g.buffer 0).len 0)
    (q : Spec.Rsa.bytesAt t.mem (g.buffer 2).base (g.buffer 2).len = List.replicate (g.buffer 2).len 0)
    (zero : t.gpr .eax = 0) : Written g m t := by
  unfold Written
  rw [none]
  refine ⟨zero, ?_⟩
  simp only [outputBuffers, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨p, q⟩

theorem sized_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g)
    (valid : Spec.Rsa.modulusValid (inputValue g s.mem 0) (inputBytes g s.mem 0).length = true)
    (pLen : (g.buffer 0).len = (inputBytes g s.mem 0).length)
    (qLen : (g.buffer 2).len = (inputBytes g s.mem 0).length) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.sized s fun t => Inputs g t ∧ Written g s.mem t ∧
      Frame (bodyWrites g) s.mem t.mem ∧ Keeps opRegs s t := by
  have bound : inputValue g s.mem 0 < 2 ^ (64 * g.n) := by
    apply Nat.lt_of_lt_of_le (inputValue_lt g s.mem 0)
    apply Nat.pow_le_pow_right (by decide)
    have := h.inputBound 0
    omega
  have facts := valid
  simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at facts
  have odd : inputValue g s.mem 0 % 2 = 1 := facts.1.1.1
  have large : 101 < inputValue g s.mem 0 := by
    have lower := facts.1.1.2
    have small : 101 < 2 ^ 7 := by decide
    have power (k : Nat) (hk : 7 ≤ k) : 128 ≤ 2 ^ k :=
      Nat.pow_le_pow_right (n := 2) (by decide) hk
    have bigger := power 511 (by decide)
    omega
  unfold VG.Impl.Rsa.X86.RecoverRt.sized
  refine WP.seq (WP.mono (numbers_ok h len) fun u ⟨hu, zt⟩ => ?_)
  refine WP.ite (decide (GoOn (product g s.mem))) (by exact zt) ?_ ?_
  · intro yes
    have go : GoOn (product g s.mem) := of_decide_eq_true yes
    refine WP.mono (selectedRest_ok h len hu go bound odd large) fun t result => ?_
    have written := written_rest result valid pLen qLen
    obtain ⟨_, _, _, ⟨ht, _, _, _, frame, rest⟩, _, _, _⟩ := result
    exact ⟨ht, written, frame, rest⟩
  · intro no
    have skip : ¬GoOn (product g s.mem) := of_decide_eq_false no
    have iu := h.of_KS hu
    refine WP.mono (failure_ok iu) fun t ⟨ht, p, q, zero, frame, rest⟩ => ?_
    have before : Frame (bodyWrites g) s.mem u.mem := hu.frame.sub fun r hr => ⟨r, by
      simp only [stageR, VG.Proof.Bignum.X86.CrtRt.frameR, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [bodyWrites], fun _ h => h⟩
    exact ⟨ht, written_failure (calculated_none_skip skip) p q zero,
      before.trans frame, hu.rest.trans (rest.mono (by decide))⟩

end VG.Proof.Rsa.X86.Recover
