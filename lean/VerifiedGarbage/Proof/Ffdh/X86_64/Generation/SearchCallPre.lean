module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchArguments
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.OutgoingPre
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.CandidatePre

/-! # The verified candidate contract holds for every internal invocation -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate

def callReads (p : SearchPublic) (used : Nat) : List Region :=
  [⟨off p.c.rp used, p.c.rand.length - used⟩, ⟨p.c.sp - 32 + 8, 24⟩]

def callWrites (p : SearchPublic) : List Region :=
  [⟨p.c.op, p.c.k⟩, ⟨p.c.up, 8⟩, ⟨p.c.B, p.c.Z⟩]

theorem searchCallValues_bound (p : SearchPublic) (used : Nat) :
    ∀ e ∈ searchCallValues p used, e.1 < 16 := by
  simp only [searchCallValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide

theorem search_call_args {p : SearchPublic} {s t : State} {used : Nat}
    (hsp : t.gpr .rsp = s.gpr .rsp - 32)
    (hm : t.mem = writeController s.mem (s.gpr .rsp - 32) (searchCallValues p used))
    (j : Nat) (hj : j < 3) :
    stackArg t j = match j with
      | 0 => BitVec.ofNat 64 (p.c.rand.length - used)
      | 1 => p.c.B
      | _ => BitVec.ofNat 64 (p.c.Z / 8) := by
  change word t.mem (t.gpr .rsp) (8 * (j + 1)) = _
  rw [hsp, hm, writeController_word _ _ _ (searchCallValues_bound p used) _ (by omega_using [hj])]
  have he : j = 0 ∨ j = 1 ∨ j = 2 := by omega_using [hj]
  rcases he with rfl | rfl | rfl <;>
    simp only [searchCallValues, controllerValue, List.foldl_cons, List.foldl_nil,
      Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]

theorem search_call_pre {p : SearchPublic} {original s t : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (ha : SearchArgs p used t)
    (hm : t.mem = writeController s.mem (s.gpr .rsp - 32) (searchCallValues p used))
    (k : Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11] (allocated 32 s) t) :
    pcPre (t.withRegions (callReads p used) (callWrites p)) := by
  have hsp : t.gpr .rsp = s.gpr .rsp - 32 := k.gpr (by decide)
  have ha0 : stackArg t 0 = BitVec.ofNat 64 (p.c.rand.length - used) :=
    search_call_args hsp hm 0 (by decide)
  have ha1 : stackArg t 1 = p.c.B := search_call_args hsp hm 1 (by decide)
  have ha2 : stackArg t 2 = BitVec.ofNat 64 (p.c.Z / 8) := search_call_args hsp hm 2 (by decide)
  have hargs (j : Nat) : stackArg (t.withRegions (callReads p used) (callWrites p)) j = stackArg t j := rfl
  have hin := h.input
  cases hin.2
  have hu : used ≤ (stackArg original 0).toNat := by
    simpa only [searchOfState, SearchPublic.c, candidateOfState, pcRand,
      Spec.Rsa.bytesAt, List.length_map, List.length_range] using h.used_le
  have hsp' : s.gpr .rsp = original.gpr .rsp := h.rsp
  obtain ⟨hdi, hsi, hdx, hcx, hgen, hrand⟩ := ha
  refine candidate_pre_suffix (outgoing_pre hin.1) (used := used) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals try simp only [State.withRegions_gpr, hargs]
  · simpa only [reference_arg original 0 (by decide)] using hu
  · exact hsp.trans (congrArg (fun sp => sp - 32) hsp')
  · exact hdi
  · simpa only [searchOfState, SearchPublic.c, candidateOfState, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      reference_reg original .rsi (by decide)]
      using hsi
  · exact hdx
  · simpa only [searchOfState, SearchPublic.c, candidateOfState, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      reference_reg original .rcx (by decide)]
      using hcx
  · rw [hgen]
    simp only [searchOfState, SearchPublic.c, candidateOfState, reference_reg original .r8 (by decide),
      BitVec.ofNat_toNat]
    exact BitVec.setWidth_setWidth_of_le _ (by decide)
  · exact hrand
  · simpa only [searchOfState, SearchPublic.c, candidateOfState, pcRand, Spec.Rsa.bytesAt,
      List.length_map, List.length_range, reference_arg original 0 (by decide)] using ha0
  · simpa only [searchOfState, SearchPublic.c, candidateOfState, reference_arg original 1 (by decide)]
      using ha1
  · simpa only [searchOfState, SearchPublic.c, candidateOfState, Nat.mul_div_cancel _ (by decide : 0 < 8),
      BitVec.ofNat_toNat, BitVec.setWidth_eq, reference_arg original 2 (by decide)] using ha2
  · change callReads _ used = _
    simp only [callReads, hrand, ha0, stackArgAddr, State.withRegions_gpr, hsp, hsp',
      searchOfState, SearchPublic.c, candidateOfState, pcRand, Spec.Rsa.bytesAt,
      List.length_map, List.length_range, Nat.zero_add, Nat.mul_one, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_using [(stackArg original 0).isLt])]
    rfl
  · change callWrites _ = _
    simp only [callWrites, hdi, hsi, hdx, ha1, ha2,
      searchOfState, SearchPublic.c, candidateOfState, Nat.mul_div_cancel _ (by decide : 0 < 8),
      BitVec.ofNat_toNat, BitVec.setWidth_eq]

end VG.Proof.Ffdh.X86_64.Generation
