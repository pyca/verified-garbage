module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.MontgomeryCall
public import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Impl.Dsa.X86.Generation.Montgomery
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! The adapter and the shared Montgomery call have secret-independent traces. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86.RtCall

private def argsHint : VG.Taint.Hint VG.X86.Taint.T :=
  VG.Taint.hintOf taint (τr [.esp, .edi]) (.block (montgomeryArgs 4 4 4 4))

private theorem argsCheck :
    (VG.Taint.check taint (τr [.esp, .edi]) (.block (montgomeryArgs 4 4 4 4)) argsHint).map
      (taint.le (τr [.esp, .edi])) = some true := by taint_decide

theorem montgomery_arguments_ct (n o a b : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block (montgomeryArgs n o a b))
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  VG.Proof.Dsa.X86.erased_relCT _ (.block (montgomeryArgs 4 4 4 4)) argsHint
    (by kernel_rfl) (by decide +kernel) (by decide +kernel) argsCheck

theorem montgomery_ct {base : Addr} {sp : BitVec 32} {n o a b : Nat}
    (hn : 0 < n) (hn' : n ≤ 48) (ho : o < 9) (ha : a < 9) (hb : b < 9) (ho0 : o ≠ 0) :
    RelCT isa (fun s t => MontgomeryInput base sp n b s ∧ MontgomeryInput base sp n b t)
      (montgomery n o a b) (fun _ _ => True) := by
  unfold montgomery
  refine RelCT.frameAlloc (R := fun _ _ => True) ?_
  let P := fun f g => ∃ s t,
    (MontgomeryInput base sp n b s ∧ MontgomeryInput base sp n b t) ∧
      f = allocFrame 36 s ∧ g = allocFrame 36 t
  have argsCT : RelCT isa P (.block (montgomeryArgs n o a b)) (fun _ _ => True) :=
    (montgomery_arguments_ct n o a b).mono (fun _ _ ⟨s, t, ⟨hs, ht⟩, fs, gt⟩ => by
      subst fs gt
      apply agree_regs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [allocFrame_esp, allocFrame_esp, hs.stack, ht.stack]
      · rw [allocFrame_gpr _ _ (by decide), allocFrame_gpr _ _ (by decide)]
        apply BitVec.eq_of_toNat_eq
        rw [hs.scr.edi_toNat, ht.scr.edi_toNat]) (fun _ _ _ => trivial)
  have ready := argsCT.wp
    (F₁ := CallState base montgomeryBytes sp (montgomeryValues base n o a b))
    (F₂ := CallState base montgomeryBytes sp (montgomeryValues base n o a b))
    (fun _ _ ⟨s, t, ⟨hs, ht⟩, fs, gt⟩ => by
      subst fs gt
      exact ⟨montgomery_call_setup hs hn hn' ho ha hb ho0,
        montgomery_call_setup ht hn hn' ho ha hb ho0⟩)
  exact RelCT.seq ready (call_ct.mono (fun _ _ ⟨_, hs, ht⟩ => ⟨hs, ht⟩)
    (fun _ _ _ => trivial))

end VG.Proof.Dsa.X86.Generation
