module
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchDone

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRequest
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchDoneUpdate

/-! # Native entropy requests return the remaining budget and consumed prefix -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem search_request_done {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s)
    (ha : s.gpr .rax = BitVec.ofNat 64 (p.c.rand.length - used))
    (hout : Spec.Rsa.bytesAt s.mem p.c.op p.c.k = List.replicate p.c.k 0) :
    WP isa (.block request) s (SearchDone p original
      (.entropy remaining (Spec.Ffdh.parameterRequest p.c.bits (p.c.rand.length - used)) used)) := by
  refine WP.mono (request_ok h ha) fun t ⟨_, hm, k⟩ => ?_
  let values : List (Nat × BitVec 64) :=
    [(3, BitVec.ofNat 64 (Spec.Ffdh.parameterRequest p.c.bits (p.c.rand.length - used))), (14, 0)]
  have hb : ∀ e ∈ values, e.1 < 16 := by
    simp only [values, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl) <;> dsimp only <;> decide
  have hkeep : ∀ j ∈ [4, 5, 7], ∀ e ∈ values, j ≠ e.1 := by
    intro j hj e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    simp only [values, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases hj with rfl | rfl | rfl <;> rcases he with rfl | rfl <;> dsimp only <;> decide
  have h0 : word s.mem p.control 0 = BitVec.ofNat 64 remaining :=
    h.headers (0, BitVec.ofNat 64 remaining) (by simp [SearchPublic.headers])
  have h1 : word s.mem p.control 8 = BitVec.ofNat 64 p.c.k :=
    h.headers (1, BitVec.ofNat 64 p.c.k) (by simp [SearchPublic.headers])
  have h2 : word s.mem p.control 16 = BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits) :=
    h.headers (2, BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits)) (by simp [SearchPublic.headers])
  have h12 : word s.mem p.control 96 = BitVec.ofNat 64 used :=
    h.headers (12, BitVec.ofNat 64 used) (by simp [SearchPublic.headers])
  refine done_update h values hb hkeep hm k.2.1 k.2.2
    (fun reg hr => k.gpr (by cases reg <;> simp_all [calleeSaved])) ?_ ?_ ?_ hout
  · rw [hm]
    change word (writeController s.mem p.control values) p.control (8 * 12) = _
    rw [writeController_word _ _ _ hb 12 (by decide)]
    simp only [values, controllerValue, List.foldl_cons, List.foldl_nil,
      Nat.reduceEqDiff, ite_false, h12]
    rfl
  · rw [hm]
    change word (writeController s.mem p.control values) p.control (8 * 14) = _
    rw [writeController_word _ _ _ hb 14 (by decide)]
    rfl
  · rw [hm, writeController_policy _ _ _ hb]
    simp only [values, controllerValue, List.foldl_cons, List.foldl_nil,
      Nat.reduceEqDiff, ite_false, ite_true, h0, h1, h2]
    rfl

end VG.Proof.Ffdh.X86_64.Generation
