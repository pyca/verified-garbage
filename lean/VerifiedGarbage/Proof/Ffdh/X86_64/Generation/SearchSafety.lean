module

public import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Search
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Safety
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Depth

/-! # The complete generation controller's instruction safety and stack bound -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate
open VG.Impl.Ffdh.X86_64.Generation.Search

def searchCode (v : RoundImpl) : Prog isa := code (candidateCode v)

private theorem controller_all (p : Instr → Bool) (c : Prog isa)
    (hp : (code (.block [])).all p = true) (hc : c.all p = true) : (code c).all p = true := by
  unfold code iteration candidateRun at hp ⊢
  simp only [seqs, Code.all, List.all_nil, hc, Bool.and_true] at hp ⊢
  exact hp

private theorem controller_instrs (p : Instr → Bool) (c : Prog isa)
    (hp : (code (.block [])).allInstrs p = true) (hc : c.allInstrs p = true) :
    (code c).allInstrs p = true := by
  unfold code iteration candidateRun at hp ⊢
  simp only [seqs, Code.allInstrs, hc, Bool.and_true] at hp ⊢
  exact hp

theorem searchCode_sp (v : RoundImpl) : (searchCode v).all (fun i => !isa.writesSp i) = true := by
  exact controller_all _ _ (by decide +kernel) (candidateCode_sp v)

theorem searchCode_mx (v : RoundImpl) : (searchCode v).allInstrs (fun i => !loadsMxcsr i) = true := by
  exact controller_instrs _ _ (by decide +kernel) (candidateCode_mx v)

theorem searchCode_depth (v : RoundImpl) : (searchCode v).x86_64Depth ≤ 160 := by
  have he : exhausted.x86_64Depth = 0 := rfl
  have hc : classify.x86_64Depth = 0 := rfl
  unfold searchCode code iteration candidateRun
  simp only [seqs, Code.x86_64Depth, Instr.frameBytes, he, hc, Nat.zero_max, Nat.max_zero]
  exact Nat.add_le_add_right (candidateCode_depth v) 32

end VG.Proof.Ffdh.X86_64.Generation
