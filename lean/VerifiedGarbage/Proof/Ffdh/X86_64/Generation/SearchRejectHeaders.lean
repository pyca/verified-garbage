module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchReject
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchMemory

/-! # A rejected candidate advances the native search invariant -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Ffdh.X86_64
open VG.Proof.MlKem.X86_64

theorem rejectValues_bound (p : SearchPublic) (used remaining : Nat) (n : BitVec 64) :
    ∀ e ∈ rejectValues p used remaining n, e.1 < 16 := by
  simp only [rejectValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem reject_headers {p : SearchPublic} {original s : State} {used remaining n : Nat}
    (h : SearchLive p original used remaining s) (hn : n ≤ p.c.rand.length - used)
    (hr : 0 < remaining) :
    Slots (writeController s.mem p.control (rejectValues p used remaining (BitVec.ofNat 64 n)))
      p.control (p.headers (used + n) (remaining - 1)) := by
  have ht := h.input.tape_lt
  have hr64 : remaining < 2 ^ 64 := by
    have hb : p.remaining < 2 ^ 64 := by
      cases h.input.2
      exact (original.mem.readW (stackArg original 3) 64).isLt
    omega_using [h.remaining_le, hb]
  have hn64 : n < 2 ^ 64 := by omega_using [hn, ht]
  have hh := h.headers
  simp only [Slots, SearchPublic.headers, List.forall_mem_cons] at hh
  obtain ⟨h0, h1, h2, h5, h6, h7, h8, h9, h10, h11, h12, h13, h15, _⟩ := hh
  have hd : BitVec.ofNat 64 (p.c.rand.length - used) - BitVec.ofNat 64 n =
      BitVec.ofNat 64 (p.c.rand.length - (used + n)) := by
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ hn64 hn]
    congr 1
    omega
  intro e he
  simp only [SearchPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [writeController_word _ _ _ (rejectValues_bound p used remaining _) _ (by dsimp only; decide)] <;>
    simp only [rejectValues, controllerValue, List.foldl_cons, List.foldl_nil,
      Nat.reduceEqDiff, ite_true, ite_false, h0, h1, h2, h5, h6, h7, h8, h9, h10, h11, h12, h13, h15,
      hd, ofNat64_pred hr hr64, off, BitVec.ofNat_add, BitVec.add_assoc]

end VG.Proof.Ffdh.X86_64.Generation
