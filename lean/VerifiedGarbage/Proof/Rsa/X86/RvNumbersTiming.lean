module
public import VerifiedGarbage.Proof.Rsa.X86.RvHelperTiming
public import VerifiedGarbage.Proof.Rsa.X86.RvPair

import VerifiedGarbage.Proof.Rsa.X86.RvLoadsTiming
import VerifiedGarbage.Proof.Rsa.X86.RvProductTiming
import VerifiedGarbage.Proof.Rsa.X86.RvLoads
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Product computation and its refusal test have a public trace -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover

theorem skipBits_workspace (n : Nat) : WorkspacePublic (.block (skipBits n)) := by
  let reference := Code.erase (.block (skipBits 1))
  let out := (VG.Taint.check taint (workspaceTaint false) reference (.block [])).getD (workspaceTaint false)
  refine ⟨.block [], out, ?_, by decide +kernel⟩
  exact (check_of_erase_eq (.block (skipBits n)) reference (workspaceTaint false) (.block []) rfl rfl rfl).trans (by rfl)

theorem skipTest_workspace : WorkspacePublic (.block skipTest) :=
  ⟨.block [], workspaceTaint false, rfl, rfl⟩

theorem numbers_relCT (g : CallGeometry) : RelCT isa (Pair g) (numbers g.n) (fun _ _ => True) := by
  intro s t tr ur sf tf pair es et
  cases es with
  | @seq _ _ _ u _ _ _ e1 er =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 fr =>
      obtain ⟨eq1, pair1⟩ := loads_relCT g _ _ _ _ _ _ pair e1 f1
      have cs := wp_result (loads_ok pair.left) e1
      have ct := wp_result (loads_ok pair.right) f1
      cases er with
      | @seq _ _ _ x _ _ _ e2 e3 =>
        cases fr with
        | @seq _ _ _ y _ _ _ f2 f3 =>
          obtain ⟨eq2, common⟩ := prod_relCT g s t _ _ _ _ _ _ _ _ _ _ _ _
            _ _ _ _ _ _ ⟨pair1, cs, ct⟩ e2 f2
          have tail := (skipBits_workspace g.n).seq ((sub3_workspace (wide g.n) wT wZ wM).seq skipTest_workspace)
          have eq3 := (tail.trace _ _ _ _ _ _ common e3 f3).1
          exact ⟨by rw [eq1, eq2, eq3], trivial⟩

end VG.Proof.Rsa.X86.Recover
