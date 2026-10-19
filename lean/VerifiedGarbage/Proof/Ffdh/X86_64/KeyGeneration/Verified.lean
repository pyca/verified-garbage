module

import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.CT
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Safety
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Spec.Ffdh.KeyGenerationContract
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Implies
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Correct
import VerifiedGarbage.Proof.Framework.Offset

/-! # The verified key search, for every arithmetic backend -/

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
