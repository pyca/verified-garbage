module

public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Attempt
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Contract
public import VerifiedGarbage.Impl.Ffdh.X86_64.KeyGeneration.Search
import VerifiedGarbage.Proof.Bignum.X86_64.Template

/-! # The key search's instructions and the stack it uses -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Ffdh.X86_64.GenerateKey (generateCode generateCode_sp generateCode_inline generateInline_mx)
open VG.Proof.Bignum.X86_64 (allInstrs_inline)
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

/-- The key search, calling the backend's `vg_ffdh_generate_key`. -/
def keyCode (v : RoundImpl) : Prog isa := code (attemptCall v)

private theorem controller_all (p : Instr → Bool) (c : Prog isa)
    (hp : (code (.block [])).all p = true) (hc : c.all p = true) : (code c).all p = true := by
  unfold code iteration attemptOrRequest attemptRun at hp ⊢
  simp only [seqs, Code.all, List.all_nil, hc, Bool.and_true] at hp ⊢
  exact hp

private theorem controller_instrs (p : Instr → Bool) (c : Prog isa)
    (hp : (code (.block [])).allInstrs p = true) (hc : c.allInstrs p = true) :
    (code c).allInstrs p = true := by
  unfold code iteration attemptOrRequest attemptRun at hp ⊢
  simp only [seqs, Code.allInstrs, hc, Bool.and_true] at hp ⊢
  exact hp

theorem keyCode_sp (v : RoundImpl) : (keyCode v).all (fun i => !isa.writesSp i) = true :=
  controller_all _ _ (by decide +kernel) (generateCode_sp v)

theorem keyCode_mx (v : RoundImpl) : (keyCode v).allInstrs (fun i => !loadsMxcsr i) = true := by
  refine controller_instrs _ _ (by decide +kernel) ?_
  change (generateCode v).allInstrs _ = true
  rw [← allInstrs_inline, generateCode_inline]
  exact generateInline_mx v

theorem keyCode_depth (v : RoundImpl) : (keyCode v).x86_64Depth ≤ stackUse := by
  have he : exhausted.x86_64Depth = 0 := rfl
  have hr : request.x86_64Depth = 0 := rfl
  have hc : classify.x86_64Depth = 0 := rfl
  have ha := attemptCall_depth v
  unfold keyCode code iteration attemptOrRequest attemptRun
  simp only [seqs, Code.x86_64Depth, Instr.frameBytes, he, hr, hc, Nat.zero_max, Nat.max_zero,
    stackUse]
  exact Nat.add_le_add_right ha 40

end VG.Proof.Ffdh.X86_64.KeyGeneration
