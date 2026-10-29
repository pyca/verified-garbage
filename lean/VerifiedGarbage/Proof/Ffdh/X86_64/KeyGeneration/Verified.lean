module

public import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Attempt
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Contract
public import VerifiedGarbage.Impl.Ffdh.X86_64.KeyGeneration.Search

import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.CT
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Implies
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Correct
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.Template
/-! # The verified key search, for every arithmetic backend -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/KeyGeneration/Safety.lean`, which only this module imported.
section

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
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

private theorem key_return_address (v : RoundImpl) {s t : State} {tr : List Leak}
    (h : keyPre s) (he : Exec isa (keyCode v) s tr t) :
    t.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  obtain ⟨-, -, -, hwr, -, -, -, hstk, -⟩ := h
  have hd : (keyCode v).x86_64Depth ≤ 56 := keyCode_depth v
  have hf := Exec.stackFrame (SpSafe.of_all (keyCode_sp v)) he (by omega)
  refine hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · rw [hwr] at hr
    exact (hstk r (List.mem_append_left _ hr)).1
  · obtain rfl := List.mem_singleton.mp hr
    exact Offset.base_disjoint_below _ (by omega)

theorem key_correct (v : RoundImpl) (s : State) (h : keyContract.pre s) :
    ∃ tr t, Exec isa (keyCode v) s tr t ∧ abiPreserved s t ∧ keyContract.post s t := by
  obtain ⟨tr, t, he, hp, hg, _, _⟩ := key_correct_ok v h
  exact ⟨tr, t, he, abiPreserved_of_exec (keyCode_mx v) he ⟨hg, key_return_address v h he⟩, hp⟩

theorem key_verified (v : RoundImpl) :
    Verified target (keyCode v) (Spec.Ffdh.keySearchContract abi stackUse) :=
  Verified.of_correct (key_correct v) (key_constantTime v) key_implies

end VG.Proof.Ffdh.X86_64.KeyGeneration
