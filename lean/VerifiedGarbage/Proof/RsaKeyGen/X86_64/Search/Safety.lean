module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Correct
import VerifiedGarbage.Proof.Framework.Offset

/-! # The search's instructions, the stack it uses, and its calling convention -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Search

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Impl.RsaKeyGen.X86_64.Search

private theorem controller_all (p : Instr → Bool) (c : Prog isa)
    (hp : (code (.block [])).all p = true) (hc : c.all p = true) : (code c).all p = true := by
  unfold code iteration candidateRun at hp ⊢
  simp only [VG.Impl.Bignum.X86_64.seqs, Code.all, List.all_nil, hc, Bool.and_true] at hp ⊢
  exact hp

private theorem controller_instrs (p : Instr → Bool) (c : Prog isa)
    (hp : (code (.block [])).allInstrs p = true) (hc : c.allInstrs p = true) :
    (code c).allInstrs p = true := by
  unfold code iteration candidateRun at hp ⊢
  simp only [VG.Impl.Bignum.X86_64.seqs, Code.allInstrs, hc, Bool.and_true] at hp ⊢
  exact hp

theorem candidateCall_sp (v : RoundImpl) : (candidateCall v).all (fun i => !isa.writesSp i) = true :=
  sharedCandidate_sp v

theorem searchCode_sp (v : RoundImpl) : (searchCode v).all (fun i => !isa.writesSp i) = true :=
  controller_all _ _ (by decide +kernel) (candidateCall_sp v)

theorem searchCode_mx (v : RoundImpl) : (searchCode v).allInstrs (fun i => !loadsMxcsr i) = true :=
  controller_instrs _ _ (by decide +kernel) (sharedCandidate_mx v)

theorem searchCode_depth (v : RoundImpl) : (searchCode v).x86_64Depth ≤ stackUse := by
  have hc := sharedCandidate_depth v
  have he : exhausted.x86_64Depth = 0 := rfl
  have hk : classify.x86_64Depth = 0 := rfl
  unfold searchCode code iteration candidateRun candidateCall
  simp only [VG.Impl.Bignum.X86_64.seqs, Code.x86_64Depth, Instr.frameBytes, he, hk, Nat.zero_max,
    Nat.max_zero, stackUse, frameBytes]
  omega

theorem search_return_address (v : RoundImpl) {s t : State} {tr : List Leak}
    (h : searchPre s) (he : Exec isa (searchCode v) s tr t) :
    t.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  obtain ⟨-, -, -, hwr, -, -, -, hstk, -⟩ := h
  have hd : (searchCode v).x86_64Depth ≤ 336 := searchCode_depth v
  have hf := Exec.stackFrame (SpSafe.of_all (searchCode_sp v)) he (by omega)
  refine hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · rw [hwr] at hr
    exact (hstk r (List.mem_append_left _ hr)).1
  · obtain rfl := List.mem_singleton.mp hr
    exact Offset.base_disjoint_below _ (by omega)

theorem search_correct (v : RoundImpl) (s : State) (h : searchContract.pre s) :
    ∃ tr t, Exec isa (searchCode v) s tr t ∧ abiPreserved s t ∧ searchContract.post s t := by
  obtain ⟨tr, t, he, hp, hg⟩ := search_correct_ok v h
  exact ⟨tr, t, he, abiPreserved_of_exec (searchCode_mx v) he ⟨hg, search_return_address v h he⟩, hp⟩

end VG.Proof.RsaKeyGen.X86_64.Search
