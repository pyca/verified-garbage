module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivTail
import VerifiedGarbage.Proof.Rsa.Arm.PrivArgsCT
public import VerifiedGarbage.Proof.Rsa.Arm.PrivReleaseTailCT
import VerifiedGarbage.Proof.Bignum.Arm.CompareBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
import VerifiedGarbage.Proof.Bignum.Arm.CompareBuffer

/-! # Fault checking and private release reveal no secret-dependent trace -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm

structure CompareReady (dst tmp xp : BitVec 32) (k : Nat) (s : State) : Prop where
  input : TailInput dst tmp xp k s
  first : s.gpr .r0 = dst
  second : s.gpr .r1 = xp
  count : s.gpr .lr = BitVec.ofNat 32 k
  zero : s.gpr .r2 = 0
  good : s.gpr .r4 = 0 ∨ s.gpr .r4 = 1

theorem cmpArgs_ready (s : State) {dst tmp xp : BitVec 32} {k : Nat} (h : TailInput dst tmp xp k s) :
    WP isa (.block cmpArgs) s (CompareReady dst tmp xp k) := by
  refine WP.mono (cmpArgs_ok s h.workspace) ?_
  rintro t ⟨first, second, count, zero, good, mem, rest⟩
  refine ⟨h.of_mem mem rest, first.trans h.release.output, second.trans h.input, count.trans h.release.count, zero, ?_⟩
  rw [good]; exact successBits_cases _ _ _

theorem comparison_ready (s : State) {dst tmp xp : BitVec 32} {k : Nat} (h : CompareReady dst tmp xp k s) :
    WP isa VG.Impl.Bignum.Arm.compareBytes s (fun t => ∃ a e, ReleaseState dst tmp k a e t) := by
  have outRead : InRegions (s.rd ++ s.wr) (State.addr dst) k := by
    obtain ⟨r, hr, hc⟩ := h.input.release.outputWrite
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (compareBuffer_ok s h.input.release.positive h.input.release.countFit h.input.release.outputFit
    h.input.inputFit outRead h.input.inputRead h.first h.second h.count h.zero) ?_
  rintro t ⟨equal, mem, rest⟩
  let a := decide (s.gpr .r4 = 1)
  let e := decide (Spec.Rsa.bytesAt s.mem (State.addr dst) k = Spec.Rsa.bytesAt s.mem (State.addr xp) k)
  refine ⟨a, e, h.input.release.of_mem mem rest, ?_, ?_⟩
  · rw [rest.gpr .r4 (by simp)]
    rcases h.good with hz | ho
    · simp only [a, hz]; rfl
    · simp only [a, ho]; rfl
  · simpa only [e, decide_eq_true_eq] using equal

theorem tail_ct {dst tmp xp : BitVec 32} {k : Nat} :
    RelCT isa (fun s t => TailInput dst tmp xp k s ∧ TailInput dst tmp xp k t ∧ s.sp = t.sp)
      tail (fun _ _ => True) := by
  have compare : RelCT isa (fun s t => CompareReady dst tmp xp k s ∧ CompareReady dst tmp xp k t ∧ s.sp = t.sp)
      VG.Impl.Bignum.Arm.compareBytes (fun _ _ => True) := by
    intro s t tr1 tr2 u v h run1 run2
    exact ⟨compareBytes_ct s t tr1 tr2 u v trivial trivial
      ⟨h.1.first.trans h.2.1.first.symm, h.1.second.trans h.2.1.second.symm,
        h.1.count.trans h.2.1.count.symm⟩ run1 run2, trivial⟩
  have release : RelCT isa (fun s t => (∃ a e, ReleaseState dst tmp k a e s) ∧
      (∃ a e, ReleaseState dst tmp k a e t) ∧ s.sp = t.sp) releaseTail (fun _ _ => True) := by
    intro s t tr1 tr2 u v h run1 run2
    obtain ⟨a1, e1, hs⟩ := h.1
    obtain ⟨a2, e2, ht⟩ := h.2.1
    exact releaseTail_ct s t tr1 tr2 u v ⟨hs, ht, h.2.2⟩ run1 run2
  exact crt_seq_ct (cmpArgs_ct.mono (fun _ _ h => h.2.2) (fun _ _ _ => trivial))
    (fun s h => cmpArgs_ready s h) (fun s h => cmpArgs_ready s h)
    (crt_seq_ct compare (fun s h => comparison_ready s h) (fun s h => comparison_ready s h) release)
end VG.Proof.Rsa.Arm
