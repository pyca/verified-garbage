module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialTable
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Impl.Dsa.X86.Generation.TrialTable
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialTable

/-! # One-time divisor-table initialization has a fixed public access sequence -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont.X86 VG.Impl.Dsa.X86.Generation

private theorem tableBlock_check (a b : BitVec 32) (x y : Nat) :
    (VG.Taint.check taint (τr [.edi]) (.block [.mov .eax (.imm a),
      .store (VG.Impl.Mont.X86.sc x) .eax, .mov .eax (.imm b),
      .store (VG.Impl.Mont.X86.sc y) .eax]) (.block [])).isSome = true := by
  exact (congrArg Option.isSome (VG.Proof.Mont.X86.Dynamic.check_of_erase_eq
    (.block [.mov .eax (.imm a), .store (VG.Impl.Mont.X86.sc x) .eax,
      .mov .eax (.imm b), .store (VG.Impl.Mont.X86.sc y) .eax])
    (.block [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc 0) .eax,
      .mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc 0) .eax])
    (τr [.edi]) (.block []) rfl rfl rfl)).trans (by rfl)

theorem trialTableEntry_ct (i : Nat) (bound : i < 1024) :
    RelCT isa (Two fun base s => Scr s base 8192) (.block (trialTableEntry i))
      (Two fun base s => Scr s base 8192) := by
  refine two_piece [.edi] ?_ (hc := .block []) ?_ ?_
  · intro base s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact BitVec.eq_of_toNat_eq (hs.edi_toNat.trans ht.edi_toNat.symm)
  · exact tableBlock_check _ _ _ _
  · intro base s R
    exact WP.mono (trialTableEntry_ok R bound) fun _ ⟨_, K⟩ => R.of_keeps K (by decide)

theorem trialTable_ct (n : Nat) (bound : n ≤ 1024) :
    RelCT isa (Two fun base s => Scr s base 8192) (trialTable n)
      (Two fun base s => Scr s base 8192) := by
  induction n with
  | zero => exact RelCT.nil (fun _ _ h => h)
  | succ n ih => exact RelCT.seq (ih (by omega)) (trialTableEntry_ct n (by omega))
end VG.Proof.Dsa.X86.Generation
