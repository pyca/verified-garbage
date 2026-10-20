module
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchDone

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchAccept
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchDoneUpdate

/-! # Successful candidates finish the complete native parameter search -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem search_accept_done {p : SearchPublic} {original s : State} {used remaining n prime : Nat}
    (h : SearchLive p original used remaining s)
    (hu : s.mem.readW p.c.up 64 = BitVec.ofNat 64 n)
    (hout : Spec.Rsa.bytesAt s.mem p.c.op p.c.k = Spec.Rsa.i2osp prime p.c.k) :
    WP isa (.block accept) s (SearchDone p original (.accepted prime (used + n))) := by
  refine WP.mono (accept_ok h (BitVec.ofNat 64 n) hu) fun t ⟨_, hm, k⟩ => ?_
  let values := [(12, BitVec.ofNat 64 used + BitVec.ofNat 64 n)] ++ terminalValues 1
  have hb : ∀ e ∈ values, e.1 < 16 := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · obtain rfl := List.mem_singleton.mp he
      dsimp only
      decide
    · exact terminalValues_bound 1 e he
  have hkeep : ∀ j ∈ [4, 5, 7], ∀ e ∈ values, j ≠ e.1 := by
    intro j hj e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    simp only [values, terminalValues, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at he
    rcases hj with rfl | rfl | rfl <;> rcases he with rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  have h1 : word s.mem p.control 8 = BitVec.ofNat 64 p.c.k :=
    h.headers (1, BitVec.ofNat 64 p.c.k) (by simp [SearchPublic.headers])
  have h2 : word s.mem p.control 16 = BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits) :=
    h.headers (2, BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits)) (by simp [SearchPublic.headers])
  refine done_update h values hb hkeep hm k.2.1 k.2.2
    (fun reg hr => k.gpr (by cases reg <;> simp_all [calleeSaved])) ?_ ?_ ?_ hout
  · rw [hm]
    change word (writeController s.mem p.control values) p.control (8 * 12) = _
    rw [writeController_word _ _ _ hb 12 (by decide)]
    simp only [values, terminalValues, controllerValue, List.foldl_append, List.foldl_cons,
      List.foldl_nil, Nat.reduceEqDiff, ite_false, ite_true, ← BitVec.ofNat_add]
    rfl
  · rw [hm]
    change word (writeController s.mem p.control values) p.control (8 * 14) = _
    rw [writeController_word _ _ _ hb 14 (by decide)]
    rfl
  · rw [hm, writeController_policy _ _ _ hb]
    simp only [values, terminalValues, controllerValue, List.foldl_append, List.foldl_cons,
      List.foldl_nil, Nat.reduceEqDiff, ite_false, ite_true, h1, h2]
    rfl

end VG.Proof.Ffdh.X86_64.Generation
