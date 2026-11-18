module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout
public import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Search
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ControlMemory
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! ### `Ffdh.X86_64.Generation.SearchUpdate`, which this module and modules that import it used -/

section

/-! # Preserve the search invariant across native controller updates -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Ffdh.X86_64

theorem SearchLive.control_update {p : SearchPublic} {original s t : State} {used remaining u r : Nat}
    (h : SearchLive p original used remaining s) (hu : u ≤ p.c.rand.length) (hr : r ≤ p.remaining)
    (values : List (Nat × BitVec 64)) (hb : ∀ e ∈ values, e.1 < 16)
    (h4 : ∀ e ∈ values, 4 ≠ e.1)
    (hm : t.mem = writeController s.mem p.control values)
    (hread : t.rd = s.rd) (hwrite : t.wr = s.wr)
    (hg : ∀ reg ∈ calleeSaved, t.gpr reg = s.gpr reg)
    (hh : Slots t.mem p.control (p.headers u r)) : SearchLive p original u r t := by
  refine ⟨h.input, hu, hr, hread.trans h.rd, hwrite.trans h.wr,
    (hg .rsp (by decide)).trans h.rsp, (hg .r12 (by decide)).trans h.r12,
    fun reg hreg hne => (hg reg hreg).trans (h.saved reg hreg hne), ?_, ?_, hh⟩
  · rw [hm]
    change word (writeController s.mem p.control values) p.control (8 * 4) = _
    rw [writeController_word _ _ _ hb 4 (by decide), controllerValue_unchanged _ _ _ h4]
    exact h.savedR12
  · have hf : Frame (original.wr ++ [below (original.gpr .rsp) 160]) s.mem t.mem := by
      rw [hm]
      apply (writeController_frame s.mem p.control values hb).sub
      intro region hregion
      obtain rfl := List.mem_singleton.mp hregion
      refine ⟨inputControl original, List.mem_append_left _ ?_, ?_⟩
      · rw [h.input.1.2.2.2.1]
        simp
      · cases h.input.2
        exact fun _ hi => hi
    exact (h.input.random_frame hf).trans h.random

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! ### `Ffdh.X86_64.Generation.SearchTerminal`, which this module and modules that import it used -/

section

/-! # Native terminal policy transitions -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

def terminalValues (status : Nat) : List (Nat × BitVec 64) :=
  [(0, 0), (3, 0), (14, (BitVec.ofNat 32 status).setWidth 64)]

theorem terminal_ok {s : State} {B : Addr} (scr : Scr s B 128) (hb : s.gpr .r12 = B)
    (status : Nat) :
    WP isa (.block (terminal status)) s fun t =>
      t.gpr .rax = (BitVec.ofNat 32 status).setWidth 64 ∧
      t.mem = writeController s.mem B (terminalValues status) ∧ Keep [.rax] s t := by
  have hs : ∀ d, d + 8 ≤ 128 → InRegions s.wr (B + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hs0 : InRegions s.wr B 8 := by simpa only [BitVec.add_zero] using hs 0 (by decide)
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.gpr .rax = (BitVec.ofNat 32 status).setWidth 64 ∧
    t.mem = writeController s.mem B (terminalValues status)) ?_ rfl)
    fun _ ⟨⟨hr, hm⟩, k⟩ => ⟨hr, hm, k⟩
  unfold terminal writeController terminalValues
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, hb, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    hs0, hs 24 (by decide), hs 112 (by decide)]
  rfl

theorem terminalValues_bound (status : Nat) : ∀ e ∈ terminalValues status, e.1 < 16 := by
  simp only [terminalValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide

end VG.Proof.Ffdh.X86_64.Generation

end

end

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
