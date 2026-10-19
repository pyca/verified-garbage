module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivReleaseTail
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Rsa.Arm.PrivReleaseCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
import VerifiedGarbage.Proof.Rsa.Arm.PrivMask
import VerifiedGarbage.Proof.Rsa.Arm.PrivReleaseArgs
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivReleaseTail
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivReleaseCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
meta import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivMask
meta import VerifiedGarbage.Proof.Rsa.Arm.PrivReleaseArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate

/-! # Private release and fault status have no secret-dependent leakage -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm

structure ReleaseState (dst tmp : BitVec 32) (k : Nat) (accepted equal : Bool) (s : State) : Prop where
  input : ReleaseInput dst tmp k s
  good : s.gpr .r4 = BitVec.ofNat 32 accepted.toNat
  equal : (s.gpr .r2 = 0) ↔ equal = true

theorem releaseArgs_ct : RelCT isa (fun s t => s.sp = t.sp) (.block releaseArgs) (fun _ _ => True) := by
  have addr : RelCT isa (fun s t => s.sp = t.sp) (.block [.addSp .r1 oM]) (fun s t => s.sp = t.sp) := by
    apply relCT_keep_sp (sp := fun _ _ h => h)
    apply single_ct (fun _ _ _ => rfl)
    intros; trivial
  have zero : RelCT isa (fun s t => s.sp = t.sp) (.block [.mov .r12 (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact RelCT.block_append ((loadStack_ct .r0 oOut).seq
    (RelCT.block_append (addr.seq (RelCT.block_append ((loadStack_ct .lr oK).seq zero)))))

theorem releaseTail_ct {dst tmp : BitVec 32} {k : Nat} {a1 a2 e1 e2 : Bool} :
    RelCT isa (fun s t => ReleaseState dst tmp k a1 e1 s ∧ ReleaseState dst tmp k a2 e2 t ∧ s.sp = t.sp)
      releaseTail (fun _ _ => True) := by
  have mask : RelCT isa (fun s t => ReleaseState dst tmp k a1 e1 s ∧ ReleaseState dst tmp k a2 e2 t ∧ s.sp = t.sp)
      (.block maskCore) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have wp (s : State) {a e : Bool} (h : ReleaseState dst tmp k a e s) :
      WP isa (.block maskCore) s (ReleaseInput dst tmp k) := by
    refine WP.mono (maskCore_ok s h.good h.equal) ?_
    rintro t ⟨_, _, mem, rest⟩
    exact h.input.of_mem mem rest
  let Q := fun s : State => s.gpr .r0 = dst ∧ s.gpr .r1 = tmp ∧ s.gpr .lr = BitVec.ofNat 32 k
  have argsWp (s : State) (h : ReleaseInput dst tmp k s) : WP isa (.block releaseArgs) s Q := by
    refine WP.mono (releaseArgs_ok s h.stackFit h.outRead h.countRead) ?_
    rintro t ⟨out, temp, count, _⟩
    exact ⟨out.trans h.output, temp.trans h.temp, count.trans h.count⟩
  have args := (releaseArgs_ct.mono
    (P' := fun (s t : State) => ReleaseInput dst tmp k s ∧ ReleaseInput dst tmp k t ∧ s.sp = t.sp)
    (fun _ _ h => h.2.2) (fun _ _ _ => trivial)).wp
    (fun s t h => ⟨argsWp s h.1, argsWp t h.2.1⟩)
  have loop : RelCT isa (fun s t => True ∧ Q s ∧ Q t) release (fun _ _ => True) := by
    intro s t tr1 tr2 u v h run1 run2
    exact ⟨release_ct s t tr1 tr2 u v trivial trivial
      ⟨h.2.1.1.trans h.2.2.1.symm, h.2.1.2.1.trans h.2.2.2.1.symm, h.2.1.2.2.trans h.2.2.2.2.symm⟩ run1 run2, trivial⟩
  have ret : RelCT isa (fun _ _ => True) (.block [.mov .r0 (.reg .r4)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact crt_seq_ct mask (fun s h => wp s h) (fun s h => wp s h) (args.seq (loop.seq ret))
end VG.Proof.Rsa.Arm
