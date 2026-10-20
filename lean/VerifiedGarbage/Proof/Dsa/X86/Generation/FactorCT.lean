module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Impl.Dsa.X86.Generation.Factor
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.FactorLoopCT
public meta import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Factor
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FactorCTState
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.FactorLoopCT

/-! # Factoring the public predecessor has no dependence on uninitialized workspace -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

def FactorEntryAt (n : Nat) (p : FactorPublic) (s : State) : Prop :=
  Scr s p.base p.size ∧ 0 < p.value ∧ p.value % 2 = 0 ∧
    slot n 8 + 8 * n ≤ p.size ∧ val32 s.mem p.base (slot n 8) (2 * n) = p.value

theorem factor_ct (n : Nat) (positive : 0 < n) :
    RelCT isa (Two (FactorEntryAt n)) (factor n) (fun _ _ => True) := by
  unfold factor
  refine RelCT.seq (two_piece (Ψ := fun (p : FactorPublic) => FactorAt n {p with count := 0}) []
    (by intro _ _ _ _ _ r hr; cases hr) (by taint_decide) ?_) (RelCT.seq
      (two_map (fun p : FactorPublic => {p with count := 0}) (fun _ _ h => h) (factorLoop_ct n positive)) ?_)
  · intro p s R
    exact wp_movS rfl fun t st _ => WP.block_nil
      ⟨R.1.of_keeps st.keeps (by decide), R.2.1, R.2.2.1, R.2.2.2.1, by rw [st.mem]; exact R.2.2.2.2, st.gpr⟩
  · refine two_taint [.edi] ?_ (by taint_decide)
    intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact BitVec.eq_of_toNat_eq (hs.edi_toNat.trans ht.edi_toNat.symm)
end VG.Proof.Dsa.X86.Generation
