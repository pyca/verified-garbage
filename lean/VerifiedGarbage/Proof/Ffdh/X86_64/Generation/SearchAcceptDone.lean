module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchDone

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchDoneUpdate
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchMemory
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchTerminal
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchData
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout
/-! # Successful candidates finish the complete native parameter search -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Generation/SearchAccept.lean`, which only this module imported.
section

/-! # Record final candidate consumption and finish native parameter search -/

section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem accept_prefix {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (consumed : BitVec 64)
    (hu : s.mem.readW p.c.up 64 = consumed) :
    WP isa (.block [
      .mov .rax (.mem (field 7)), .mov .rcx (.mem { base := .rax }),
      .mov .rax (.mem (field 12)), .alu .add .rax (.reg .rcx), .store (field 12) .rax]) s fun t =>
      t.mem = writeController s.mem p.control [(12, BitVec.ofNat 64 used + consumed)] ∧
      Keep [.rax, .rcx] s t := by
  have scr := h.input.control_scr h.wr
  have hs : InRegions s.wr (p.control + BitVec.ofNat 64 96) 8 := scr.st (by decide)
  have hl7 : InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 56) 8 := scr.ld (by decide)
  have hl12 : InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 96) 8 := scr.ld (by decide)
  have hup : InRegions (s.rd ++ s.wr) p.c.up 8 := by
    simpa only [off, BitVec.add_zero] using (h.input.used_memory h.wr).ld (d := 0) (by decide)
  have hv7 : s.mem.readW (p.control + BitVec.ofNat 64 56) 64 = p.c.up :=
    h.headers (7, p.c.up) (by simp [SearchPublic.headers])
  have hv12 : s.mem.readW (p.control + BitVec.ofNat 64 96) 64 = BitVec.ofNat 64 used :=
    h.headers (12, BitVec.ofNat 64 used) (by simp [SearchPublic.headers])
  refine WP.keep [.rax, .rcx] ?_ rfl
  unfold writeController
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, h.r12, hs, hl7, hl12, hup, hu, hv7, hv12,
    BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero]

theorem accept_ok {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (consumed : BitVec 64)
    (hu : s.mem.readW p.c.up 64 = consumed) :
    WP isa (.block accept) s fun t =>
      t.gpr .rax = 1 ∧
      t.mem = writeController s.mem p.control
        ([(12, BitVec.ofNat 64 used + consumed)] ++ terminalValues 1) ∧ Keep [.rax, .rcx] s t := by
  rw [accept, WP.block_append_iff]
  refine WP.mono (accept_prefix h consumed hu) fun u ⟨hm, k⟩ => ?_
  refine WP.mono (terminal_ok (h.input.control_scr (k.2.2.trans h.wr))
    ((k.gpr (by decide)).trans h.r12) 1) fun t ⟨hr, ht, kt⟩ => ?_
  exact ⟨hr, by rw [ht, hm, writeController_append], (k.trans kt).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.Generation
end

end

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
