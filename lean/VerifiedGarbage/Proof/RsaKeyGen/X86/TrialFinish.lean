module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Trial
import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialFinishMath
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Execute the branch-free small-prime divisibility test -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Trial
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Trial

theorem finish_ok {s : State} (positive : 0 < (s.gpr .ebx).toNat) :
    WP isa (.block finish) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decide ((s.gpr .ebp).toNat = 0 ∨ (s.gpr .ebp).toNat = (s.gpr .ebx).toNat)).toNat ∧
      t.mem = s.mem ∧ Keeps [.eax, .edx, .ebp] s t := by
  unfold finish
  refine wp_movS rfl fun a A _ => wp_movS rfl fun b B _ => wp_subS rfl fun c C cf => ?_
  refine wp_adcS rfl cf fun d D _ => wp_subS rfl fun e E _ => wp_subS rfl fun f F cfF => ?_
  refine wp_adcS rfl cfF fun t T _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [T.gpr, F.other .eax (by decide), E.other .eax (by decide), D.gpr,
      C.other .eax (by decide), B.other .eax (by decide), A.gpr,
      B.gpr, A.other .ebp (by decide),
      E.gpr, D.other .ebp (by decide), C.other .ebp (by decide), B.other .ebp (by decide),
      A.other .ebp (by decide), D.other .ebx (by decide), C.other .ebx (by decide),
      B.other .ebx (by decide), A.other .ebx (by decide)]
    exact finish_bits _ _ positive
  · rw [T.mem, F.mem, E.mem, D.mem, C.mem, B.mem, A.mem]
  · exact ((((((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps).widen D.keeps).widen E.keeps).widen F.keeps).widen T.keeps

end VG.Proof.RsaKeyGen.X86.Trial
