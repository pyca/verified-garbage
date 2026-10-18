module

public import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseTail
public import VerifiedGarbage.Proof.Rsa.X86.PrivLoopTiming

/-! # Masking and erasure traces do not depend on the private acceptance decision -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Mont.X86 VG.Proof.Dsa.X86

structure ReleaseState (dst tmp : BitVec 32) (k : Nat) (s : State) : Prop where
  input : ReleaseInput dst tmp k s
  decision : ∃ accepted equal : Bool, s.gpr .ebx = BitVec.ofNat 32 accepted.toNat ∧
    ((s.gpr .ebp = 0) ↔ equal = true)

theorem releaseArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block releaseArgs)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem return_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block [.mov .eax (.reg .ebx)])
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem sp_agree {s t : State} (h : s.gpr .esp = t.gpr .esp) :
    VG.X86.Taint.Agree (τr [.esp]) s t :=
  agree_regs (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact h)

theorem loop_agree {s t : State} (sp : s.gpr .esp = t.gpr .esp)
    (src : s.gpr .esi = t.gpr .esi) (dst : s.gpr .edi = t.gpr .edi)
    (count : s.gpr .ecx = t.gpr .ecx) : VG.X86.Taint.Agree loopTaint s t := by
  apply agree_regs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact sp
  · exact src
  · exact dst
  · exact count

theorem release_relCT {dst tmp : BitVec 32} {k : Nat} :
    RelCT isa (fun s t => ReleaseState dst tmp k s ∧ ReleaseState dst tmp k t ∧ s.gpr .esp = t.gpr .esp)
      release (fun _ _ => True) := by
  intro s t tr ur sf tf H E F
  rcases H with ⟨hs, ht, sp⟩
  obtain ⟨as, es, gs, qs⟩ := hs.decision
  obtain ⟨atb, et, gt, qt⟩ := ht.decision
  cases E with
  | seq E1 E2 =>
    cases F with
    | seq F1 F2 =>
      have T1 := (masks_relCT _ _ _ _ _ _ (sp_agree sp) E1 F1).1
      obtain ⟨_, _, Ms, Ks⟩ := wp_result (masks_ok s as es gs qs) E1
      obtain ⟨_, _, Mt, Kt⟩ := wp_result (masks_ok t atb et gt qt) F1
      have us := hs.input.of_mem Ms Ks (Ks.1 .esp (by decide))
      have ut := ht.input.of_mem Mt Kt (Kt.1 .esp (by decide))
      have sp1 := (Ks.1 .esp (by decide)).trans (sp.trans (Kt.1 .esp (by decide)).symm)
      cases E2 with
      | seq E3 E4 =>
        cases F2 with
        | seq F3 F4 =>
          have T2 := (releaseArgs_relCT _ _ _ _ _ _ (sp_agree sp1) E3 F3).1
          obtain ⟨Ds, Ss, Cs, _, Ls⟩ := wp_result (releaseArgs_ok _ us.outRead us.countRead) E3
          obtain ⟨Dt, St, Ct, _, Lt⟩ := wp_result (releaseArgs_ok _ ut.outRead ut.countRead) F3
          have sp2 := (Ls.1 .esp (by decide)).trans (sp1.trans (Lt.1 .esp (by decide)).symm)
          have A := loop_agree sp2
            ((Ss.trans us.temp).trans (St.trans ut.temp).symm)
            ((Ds.trans us.output).trans (Dt.trans ut.output).symm)
            ((Cs.trans us.count).trans (Ct.trans ut.count).symm)
          cases E4 with
          | seq E5 E6 =>
            cases F4 with
            | seq F5 F6 =>
              obtain ⟨T3, B⟩ := releaseLoop_relCT _ _ _ _ _ _ A E5 F5
              have T4 := (return_relCT _ _ _ _ _ _ (sp_agree (B.rf.1 .esp (by decide))) E6 F6).1
              exact ⟨by rw [T1, T2, T3, T4], trivial⟩

end VG.Proof.Rsa.X86.PrivChecked
