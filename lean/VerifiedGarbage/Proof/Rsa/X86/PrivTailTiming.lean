module

public import VerifiedGarbage.Proof.Rsa.X86.PrivTail
public import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseTiming

/-! # Fault checking and private release reveal no secret-dependent trace -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Dsa.X86

structure CompareReady (dst tmp xp : BitVec 32) (k : Nat) (s : State) : Prop where
  input : TailInput dst tmp xp k s
  first : s.gpr .esi = dst
  second : s.gpr .edi = xp
  count : s.gpr .ecx = BitVec.ofNat 32 k
  zero : s.gpr .ebp = 0
  good : s.gpr .ebx = 0 ∨ s.gpr .ebx = 1

theorem compareArgs_ready (s : State) {dst tmp xp : BitVec 32} {k : Nat} (h : TailInput dst tmp xp k s) :
    WP isa (.block compareArgs) s (CompareReady dst tmp xp k) := by
  refine WP.mono (compareArgs_ok s h.args) ?_
  rintro t ⟨first, second, count, zero, good, mem, rest⟩
  refine ⟨h.of_mem mem rest (rest.1 .esp (by decide)), first.trans h.release.output, second.trans h.input, count.trans h.release.count, zero, ?_⟩
  rw [good]; exact successBits_cases _ _ _

theorem comparison_ready (s : State) {dst tmp xp : BitVec 32} {k : Nat} (h : CompareReady dst tmp xp k s) :
    WP isa compareBytes s (ReleaseState dst tmp k) := by
  have outRead : InRegions (s.rd ++ s.wr) (byteAddr dst) k := by
    obtain ⟨r, hr, hc⟩ := h.input.release.outputWrite
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (compareBuffer_ok s h.input.release.positive h.input.release.countFit h.input.release.outputFit
    h.input.inputFit outRead h.input.inputRead h.first h.second h.count h.zero) ?_
  rintro t ⟨equal, mem, rest⟩
  let a := decide (s.gpr .ebx = 1)
  let e := decide (Spec.Rsa.bytesAt s.mem (byteAddr dst) k = Spec.Rsa.bytesAt s.mem (byteAddr xp) k)
  refine ⟨h.input.release.of_mem mem rest (rest.1 .esp (by decide)), a, e, ?_, ?_⟩
  · rw [rest.1 .ebx (by decide)]
    rcases h.good with hz | ho
    · simp only [a, hz]; rfl
    · simp only [a, ho]; rfl
  · simpa only [e, decide_eq_true_eq] using equal

theorem compareArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block compareArgs)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem tail_relCT {dst tmp xp : BitVec 32} {k : Nat} :
    RelCT isa (fun s t => TailInput dst tmp xp k s ∧ TailInput dst tmp xp k t ∧ s.gpr .esp = t.gpr .esp)
      tail (fun _ _ => True) := by
  intro s t tr ur sf tf H E F
  rcases H with ⟨hs, ht, sp⟩
  cases E with
  | seq E1 E2 =>
    cases F with
    | seq F1 F2 =>
      obtain ⟨T1, A⟩ := compareArgs_relCT _ _ _ _ _ _ (sp_agree sp) E1 F1
      have us := wp_result (compareArgs_ready s hs) E1
      have ut := wp_result (compareArgs_ready t ht) F1
      have B := loop_agree (A.rf.1 .esp (by decide))
        (us.first.trans ut.first.symm) (us.second.trans ut.second.symm) (us.count.trans ut.count.symm)
      cases E2 with
      | seq E3 E4 =>
        cases F2 with
        | seq F3 F4 =>
          obtain ⟨T2, C⟩ := compareBytes_relCT _ _ _ _ _ _ B E3 F3
          have vs := wp_result (comparison_ready _ us) E3
          have vt := wp_result (comparison_ready _ ut) F3
          have T3 := (release_relCT _ _ _ _ _ _ ⟨vs, vt, C.rf.1 .esp (by decide)⟩ E4 F4).1
          exact ⟨by rw [T1, T2, T3], trivial⟩

end VG.Proof.Rsa.X86.PrivChecked
