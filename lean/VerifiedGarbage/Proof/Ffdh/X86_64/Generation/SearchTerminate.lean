module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchTerminal
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchData
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchUpdate
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout

/-! # Terminal transitions clear the attempt and entropy-request policy -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Ffdh.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem terminal_headers {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (status : Nat) :
    Slots (writeController s.mem p.control (terminalValues status)) p.control (p.headers used 0) := by
  have hh := h.headers
  simp only [Slots, SearchPublic.headers, List.forall_mem_cons] at hh
  obtain ⟨_, h1, h2, h5, h6, h7, h8, h9, h10, h11, h12, h13, h15, _⟩ := hh
  intro e he
  simp only [SearchPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [writeController_word _ _ _ (terminalValues_bound status) _ (by dsimp only; decide)] <;>
    simp only [terminalValues, controllerValue, List.foldl_cons, List.foldl_nil,
      Nat.reduceEqDiff, ite_false, ite_true, h1, h2, h5, h6, h7, h8, h9, h10, h11, h12, h13, h15]
  rfl

theorem search_terminal {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (status : Nat) :
    WP isa (.block (terminal status)) s fun t =>
      SearchLive p original used 0 t ∧ word t.mem p.control 24 = 0 ∧
      word t.mem p.control 112 = (BitVec.ofNat 32 status).setWidth 64 := by
  refine WP.mono (terminal_ok (h.input.control_scr h.wr) h.r12 status) fun t ⟨_, hm, k⟩ => ?_
  have h4 : ∀ e ∈ terminalValues status, 4 ≠ e.1 := by
    simp only [terminalValues, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide
  refine ⟨h.control_update h.used_le (Nat.zero_le _) (terminalValues status) (terminalValues_bound status)
    h4 hm k.2.1 k.2.2 (fun reg hr => k.gpr (by cases reg <;> simp_all [calleeSaved]))
    (by rw [hm]; exact terminal_headers h status), ?_, ?_⟩
  · rw [hm]
    change word (writeController s.mem p.control (terminalValues status)) p.control (8 * 3) = _
    rw [writeController_word _ _ _ (terminalValues_bound status) 3 (by decide)]
    rfl
  · rw [hm]
    change word (writeController s.mem p.control (terminalValues status)) p.control (8 * 14) = _
    rw [writeController_word _ _ _ (terminalValues_bound status) 14 (by decide)]
    rfl

end VG.Proof.Ffdh.X86_64.Generation
