module

public import VerifiedGarbage.Proof.Bignum.X86.PublicDataTiming
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
public import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # Reloading public pointer and length pairs from the caller's stack -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Mont.X86

def argumentTaint : VG.X86.Taint.T :=
  { regs := .ofList [.edi, .esp], flags := false }

theorem argumentLoad_check (d : Reg) (i : Nat) (de : d ≠ .esp) :
    taint.checkBlock stackTaint [.mov d (.mem (PublicFn.argument i))] = some stackTaint := by
  have H : VG.X86.Taint.loadPubK stackTaint (.mem (PublicFn.argument i)) = false := by
    rw [VG.X86.Taint.loadPubK_eq]
    change VG.X86.Taint.argPub stackTaint (PublicFn.argument i) 4 = false
    simp [VG.X86.Taint.argPub, stackTaint, PublicFn.argument, at_, VG.X86.Taint.depth]
  have MB : VG.X86.Taint.movBasesK stackTaint d (.mem (PublicFn.argument i)) = [] := by
    rw [VG.X86.Taint.movBasesK_eq]
    simp [VG.X86.Taint.movBases, VG.X86.Taint.loadBases, VG.X86.Taint.addrOf,
      VG.X86.Taint.kill, stackTaint]
  simp only [VG.Taint.checkBlock, taint, VG.X86.Taint.stepKD, VG.X86.Taint.stepKDFn]
  rw [H, MB]
  simp only [VG.X86.Taint.srcOkK, VG.X86.Taint.srcPub, PublicFn.argument, at_]
  cases d <;> first | contradiction | rfl

theorem argumentPair_trace (d : Reg) (i j : Nat) (de : d ≠ .esp) :
    RelCT isa (VG.X86.Taint.Agree argumentTaint)
      (.block [.mov d (.mem (PublicFn.argument i)), .mov .ecx (.mem (PublicFn.argument j))])
      (fun _ _ => True) := by
  apply RelCT.taint (A := taint) stackTaint
    (fun _ _ h => agree_regs (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact h.rf.1 _ (by decide)))
    (hc := .block [])
  change (taint.checkBlock stackTaint
    ([.mov d (.mem (PublicFn.argument i))] ++ [.mov .ecx (.mem (PublicFn.argument j))])).isSome = true
  rw [VG.Proof.Mont.X86.Dynamic.check_append taint stackTaint, argumentLoad_check d i de]
  change (taint.checkBlock stackTaint [.mov .ecx (.mem (PublicFn.argument j))]).isSome = true
  rw [argumentLoad_check .ecx j (by decide)]
  rfl

theorem loadArguments_relCT (i j : Nat) (p c : BitVec 32) :
    RelCT isa (fun s t => VG.X86.Taint.Agree argumentTaint s t ∧
      readSrc s (.mem (PublicFn.argument i)) = some p ∧
      readSrc t (.mem (PublicFn.argument i)) = some p ∧
      readSrc s (.mem (PublicFn.argument j)) = some c ∧
      readSrc t (.mem (PublicFn.argument j)) = some c)
      (.block [.mov .esi (.mem (PublicFn.argument i)), .mov .ecx (.mem (PublicFn.argument j))])
      (VG.X86.Taint.Agree loadTaint) := by
  intro s t tr ur sf tf ⟨A, P, Q, C, D⟩ E F
  have T := (argumentPair_trace .esi i j (by decide) _ _ _ _ _ _ A E F).1
  obtain ⟨Ps, Cs, _, Ks⟩ := wp_result (argumentPair_ok (by decide) (by decide) P C) E
  obtain ⟨Pt, Ct, _, Kt⟩ := wp_result (argumentPair_ok (by decide) (by decide) Q D) F
  refine ⟨T, agree_regs (rs := [.edi, .esp, .esi, .ecx]) ?_⟩
  intro reg hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [Ks.1 _ (by decide), Kt.1 _ (by decide)]; exact A.rf.1 _ (by decide)
  · rw [Ks.1 _ (by decide), Kt.1 _ (by decide)]; exact A.rf.1 _ (by decide)
  · exact Ps.trans Pt.symm
  · exact Cs.trans Ct.symm

theorem storeArguments_relCT (i j : Nat) (p c : BitVec 32) :
    RelCT isa (fun s t => VG.X86.Taint.Agree argumentTaint s t ∧
      readSrc s (.mem (PublicFn.argument i)) = some p ∧
      readSrc t (.mem (PublicFn.argument i)) = some p ∧
      readSrc s (.mem (PublicFn.argument j)) = some c ∧
      readSrc t (.mem (PublicFn.argument j)) = some c)
      (.block [.mov .ebx (.mem (PublicFn.argument i)), .mov .ecx (.mem (PublicFn.argument j))])
      (VG.X86.Taint.Agree storeTaint) := by
  intro s t tr ur sf tf ⟨A, P, Q, C, D⟩ E F
  have T := (argumentPair_trace .ebx i j (by decide) _ _ _ _ _ _ A E F).1
  obtain ⟨Ps, Cs, _, Ks⟩ := wp_result (argumentPair_ok (by decide) (by decide) P C) E
  obtain ⟨Pt, Ct, _, Kt⟩ := wp_result (argumentPair_ok (by decide) (by decide) Q D) F
  refine ⟨T, agree_regs (rs := [.edi, .esp, .ebx, .ecx]) ?_⟩
  intro reg hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [Ks.1 _ (by decide), Kt.1 _ (by decide)]; exact A.rf.1 _ (by decide)
  · rw [Ks.1 _ (by decide), Kt.1 _ (by decide)]; exact A.rf.1 _ (by decide)
  · exact Ps.trans Pt.symm
  · exact Cs.trans Ct.symm

end VG.Proof.Bignum.X86
