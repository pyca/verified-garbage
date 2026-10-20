module
public import VerifiedGarbage.Proof.Dsa.X86.RandomContext
import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialState
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialBody

/-! # The trial-divisor helper restores its small stack frame -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem trialCheckBody_noSp (len entries : Nat) : NoSp (trialCheckBody len entries) := by
  apply NoSp.of_all
  simp [trialCheckBody, trialCheckEntry, trialCheckStep, trialCheckArgs, trialReduce,
    trialChunk, smallRemainder, trialCheckReject, trialCheckNext, Code.allInstrs, Taint.clobbers, Taint.dst]

theorem trialCheck_ok {s : State} {base : Addr} {input table : BitVec 32} {len entries : Nat}
    (sp : 16 ≤ (s.gpr .esp).toNat)
    (R : TrialInputs (allocated 16 s) base input table len entries)
    (si : s.gpr .esi = input) (di : s.gpr .edi = table) :
    WP isa (trialCheck len entries) s fun u =>
      u.gpr .eax = trialStatus entries (trialValue s input len) ∧
      Frame [⟨base, 16⟩] s.mem u.mem ∧ Keeps trialRegs s u := by
  unfold trialCheck
  refine WP.alloc ⟨by decide, by decide, by decide⟩ sp (trialCheckBody_noSp len entries) ?_
  refine WP.mono (trialCheckBody_ok R (by rw [allocated_gpr _ _ (by decide)]; exact si)
    (by rw [allocated_gpr _ _ (by decide)]; exact di)) fun t ⟨C, ax⟩ => ?_
  refine ⟨by rw [freed_gpr _ _ (by decide), ax]; rfl, C.mem, ?_⟩
  refine ⟨?_, C.keeps.2.1, ?_⟩
  · intro r hr
    have eq : r = .esp := by cases r <;> simp_all [trialRegs]
    subst r
    rw [freed_esp, C.keeps.1 .esp (by decide), allocated_esp, BitVec.sub_add_cancel]
  · change t.wr.tail = s.wr
    rw [C.keeps.2.2, allocated_wr]; rfl
end VG.Proof.Dsa.X86.Generation
