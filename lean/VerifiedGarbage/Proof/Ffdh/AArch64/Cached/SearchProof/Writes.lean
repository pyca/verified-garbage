module
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Search
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Data
public import VerifiedGarbage.Proof.Ffdh.ControlMemory

import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Outputs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Live
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Entry

/-! # The key-generation controller's writes of its own words (AArch64)

The terminal statuses, the request for entropy, the rejections, and the
octets an attempt consumes; the exits without a key (`key_exhausted`,
`key_request`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.AArch64 (Slots)
open VG.Proof.Ffdh.Control (writeController writeController_word writeController_frame
  controllerValue controllerValue_unchanged)
open VG.Impl.Ffdh.AArch64.KeyGeneration.Search (ldf stf terminal zeroOut zeroOutputs exhausted advance rejectedScalar rejectedPublic test classify request room entry arguments finish)
open VG.Impl.Ffdh.AArch64.Cached.Search
open VG.Impl.Bignum.AArch64 (movi)

/-- The controller's words after writes of `values`. -/
theorem headers_after {p : KeyPublic} {s t : State} (values : List (Nat × BitVec 64))
    (hb : ∀ e ∈ values, e.1 < 16) (hm : t.mem = writeController s.mem p.control values)
    {used' keys' scalars' : Nat}
    (hv : ∀ e ∈ p.headers used' keys' scalars',
      controllerValue values e.1 (word s.mem p.control (8 * e.1)) = e.2) :
    Slots t.mem p.control (p.headers used' keys' scalars') := by
  intro e he
  rw [hm, writeController_word _ _ _ hb e.1 (KeyPublic.headers_index he)]
  exact hv e he

/-- The loads and stores of a controller's block, at its words. -/
structure CtlAccess (s : State) (B : Addr) : Prop where
  ld : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 8
  st : ∀ d, d + 8 ≤ 128 → InRegions s.wr (B + BitVec.ofNat 64 d) 8
  ld0 : InRegions (s.rd ++ s.wr) B 8
  st0 : InRegions s.wr B 8

theorem KeyLive.access {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) : CtlAccess s p.control := by
  have scr := h.input.control_scr (t := s) h.wr
  exact ⟨fun _ hd => scr.ld hd, fun _ hd => scr.st hd,
    by simpa only [off, BitVec.add_zero] using scr.ld (d := 0) (by decide),
    by simpa only [off, BitVec.add_zero] using scr.st (d := 0) (by decide)⟩

/-! ## Terminal statuses -/

def terminalValues (status : Nat) : List (Nat × BitVec 64) :=
  [(0, 0), (1, 0), (3, 0), (14, BitVec.ofNat 64 status)]

theorem terminalValues_bound (status : Nat) : ∀ e ∈ terminalValues status, e.1 < 16 := by
  simp only [terminalValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem key_terminal_ok {s : State} {B : Addr} (a : CtlAccess s B) (hb : s.gpr .x19 = B)
    {status : Nat} (hst : status = 1 ∨ status = 3) :
    WP isa (.block (terminal status)) s fun t =>
      t.mem = writeController s.mem B (terminalValues status) ∧ Keep [.x10, .x11] s t := by
  rcases hst with rfl | rfl <;>
  refine WP.keep [.x10, .x11] ?_ (by decide) (by decide) (by decide +kernel) <;>
  unfold terminal writeController terminalValues <;>
  simp only [List.foldl_cons, List.foldl_nil]
  all_goals
    brun [ldf, stf, hb, imm64 (show 0 < 65536 by decide), imm64 (show 1 < 65536 by decide),
      imm64 (show 3 < 65536 by decide), a.st0, a.st 0 (by decide), a.st 8 (by decide),
      a.st 24 (by decide), a.st 112 (by decide)]
    rfl

/-- A terminal status written over a loop state, with no budgets left. -/
theorem key_terminal_live {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) {status : Nat} (hst : status = 1 ∨ status = 3) :
    WP isa (.block (terminal status)) s fun t =>
      KeyLive p original used 0 0 t ∧ t.mem = writeController s.mem p.control (terminalValues status) := by
  refine WP.mono (key_terminal_ok h.access h.x19 hst) fun t ⟨hm, k⟩ => ?_
  have hh : Slots t.mem p.control (p.headers used 0 0) := by
    refine headers_after _ (terminalValues_bound status) hm ?_
    intro e he
    simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false] <;>
      first | rfl | exact h.header (by simp [KeyPublic.headers])
  refine ⟨h.update (u := used) (k := 0) (c := 0) h.used_le (by decide) (by decide) _
    (terminalValues_bound status) (by
      simp only [terminalValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide) hm k.mono hh, hm⟩

theorem key_exhausted {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa exhausted s (KeyDone p original ⟨.exhausted, used, []⟩) := by
  unfold exhausted
  refine WP.seq (WP.mono (key_terminal_live h (status := 3) (.inr rfl)) fun t ⟨ht, hm⟩ => ?_)
  refine WP.mono (key_zero_outputs ht) fun u ⟨hu, hx, hy, hc⟩ => ?_
  have hw (j : Nat) (hj : j < 16) (v : BitVec 64) (hv : controllerValue (terminalValues 3) j
      (word s.mem p.control (8 * j)) = v) : word u.mem p.control (8 * j) = v := by
    rw [hc j hj, hm, writeController_word _ _ _ (terminalValues_bound 3) j hj, hv]
  refine hu.done rfl (hw 14 (by decide) _ (by
    simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_true, ite_false]; rfl)) ?_ ⟨hx, hy⟩
  change [word u.mem p.control (8 * 0), word u.mem p.control (8 * 1), word u.mem p.control (8 * 2),
    word u.mem p.control (8 * 3)] = _
  rw [hw 0 (by decide) 0 (by
      simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false]),
    hw 1 (by decide) 0 (by
      simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false]),
    hw 3 (by decide) 0 (by
      simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false]),
    hc 2 (by decide), hm, writeController_word _ _ _ (terminalValues_bound 3) 2 (by decide)]
  simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
    ite_false]
  rw [h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])]
  rfl

/-! ## A request for entropy -/

def requestValues (p : KeyPublic) : List (Nat × BitVec 64) := [(3, BitVec.ofNat 64 p.len), (14, 0)]

theorem requestValues_bound (p : KeyPublic) : ∀ e ∈ requestValues p, e.1 < 16 := by
  simp only [requestValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl) <;> dsimp only <;> decide

theorem key_request_live {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block [ldf .x10 2, movi .x11 0, stf .x10 3, stf .x11 14]) s fun t =>
      KeyLive p original used keys scalars t ∧ t.mem = writeController s.mem p.control (requestValues p) := by
  have a := h.access
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv2
  refine WP.mono (WP.keep [.x10, .x11] (Q := fun t =>
    t.mem = writeController s.mem p.control (requestValues p)) ?_ (by decide) (by decide)
      (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
  · unfold writeController requestValues
    simp only [List.foldl_cons, List.foldl_nil]
    brun [ldf, stf, h.x19, imm64 (show 0 < 65536 by decide), hv2, a.ld 16 (by decide),
      a.st 24 (by decide), a.st 112 (by decide)]
    rfl
  have hh : Slots t.mem p.control (p.headers used keys scalars) := by
    refine headers_after _ (requestValues_bound p) hm ?_
    intro e he
    rw [controllerValue_unchanged _ _ _ (by
      intro x hx
      simp only [requestValues, List.mem_cons, List.not_mem_nil, or_false] at hx
      simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases hx with rfl | rfl <;>
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        dsimp only <;> decide)]
    exact h.headers e he
  refine ⟨h.update h.used_le h.keys_le h.scalars_le _ (requestValues_bound p) (by
      simp only [requestValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl) <;> dsimp only <;> decide) hm k.mono hh, hm⟩

theorem key_request {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa request s (KeyDone p original ⟨.entropy ⟨keys, scalars⟩, used, []⟩) := by
  unfold request
  refine WP.seq (WP.mono (key_request_live h) fun t ⟨ht, hm⟩ => ?_)
  refine WP.mono (key_zero_outputs ht) fun u ⟨hu, hx, hy, hc⟩ => ?_
  have hw (j : Nat) (hj : j < 16) : word u.mem p.control (8 * j) =
      controllerValue (requestValues p) j (word s.mem p.control (8 * j)) := by
    rw [hc j hj, hm, writeController_word _ _ _ (requestValues_bound p) j hj]
  refine hu.done rfl (by
    rw [show (112 : Nat) = 8 * 14 from rfl, hw 14 (by decide)]
    simp only [controllerValue, requestValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
      ite_true, ite_false]; rfl) ?_ ⟨hx, hy⟩
  change [word u.mem p.control (8 * 0), word u.mem p.control (8 * 1), word u.mem p.control (8 * 2),
    word u.mem p.control (8 * 3)] = _
  rw [hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide)]
  simp only [controllerValue, requestValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
    ite_true, ite_false]
  rw [h.header (j := 0) (v := BitVec.ofNat 64 keys) (by simp [KeyPublic.headers]),
    h.header (j := 1) (v := BitVec.ofNat 64 scalars) (by simp [KeyPublic.headers]),
    h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])]
  rfl

/-! ## Rejections -/

def scalarValues (scalars : Nat) : List (Nat × BitVec 64) :=
  [(1, BitVec.ofNat 64 (scalars - 1)), (14, 4)]

def publicValues (keys : Nat) : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 (keys - 1)), (1, 128), (14, 4)]

theorem scalarValues_bound (scalars : Nat) : ∀ e ∈ scalarValues scalars, e.1 < 16 := by
  simp only [scalarValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl) <;> dsimp only <;> decide

theorem publicValues_bound (keys : Nat) : ∀ e ∈ publicValues keys, e.1 < 16 := by
  simp only [publicValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide

theorem ofNat_pred {n : Nat} (h0 : 0 < n) (h : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by
    simp only [BitVec.le_def, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt h]; omega)]
  simp only [BitVec.toNat_ofNat]
  omega

theorem key_rejected_scalar {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hs : 0 < scalars) :
    WP isa (.block rejectedScalar) s fun t =>
      KeyLive p original used keys (scalars - 1) t ∧ word t.mem p.control 112 = 4 := by
  have a := h.access
  have hv1 := h.header (j := 1) (v := BitVec.ofNat 64 scalars) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv1
  have e1 := ofNat_pred hs (by have := h.scalars_le; omega)
  refine WP.mono (WP.keep [.x10, .x11] (Q := fun t =>
    t.mem = writeController s.mem p.control (scalarValues scalars)) ?_ (by decide) (by decide)
      (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
  · unfold rejectedScalar writeController scalarValues
    simp only [List.foldl_cons, List.foldl_nil]
    brun [ldf, stf, h.x19, imm64 (show 4 < 65536 by decide), hv1, e1, a.ld 8 (by decide),
      a.st 8 (by decide), a.st 112 (by decide)]
    rfl
  have hh : Slots t.mem p.control (p.headers used keys (scalars - 1)) := by
    refine headers_after _ (scalarValues_bound scalars) hm ?_
    intro e he
    simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [controllerValue, scalarValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false] <;>
      first | rfl | exact h.header (by simp [KeyPublic.headers])
  refine ⟨h.update h.used_le h.keys_le (by have := h.scalars_le; omega) _ (scalarValues_bound scalars)
    (by simp only [scalarValues, List.mem_cons, List.not_mem_nil, or_false]
        rintro _ (rfl | rfl) <;> dsimp only <;> decide) hm k.mono hh, ?_⟩
  rw [show (112 : Nat) = 8 * 14 from rfl, hm, writeController_word _ _ _ (scalarValues_bound scalars) 14 (by decide)]
  simp only [controllerValue, scalarValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
    ite_true, ite_false]

theorem key_rejected_public {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hk : 0 < keys) :
    WP isa (.block rejectedPublic) s fun t =>
      KeyLive p original used (keys - 1) 128 t ∧ word t.mem p.control 112 = 4 := by
  have a := h.access
  have hv0 := h.header (j := 0) (v := BitVec.ofNat 64 keys) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off] at hv0
  have e0 := ofNat_pred hk (by have := h.keys_le; omega)
  refine WP.mono (WP.keep [.x10, .x11, .x12] (Q := fun t =>
    t.mem = writeController s.mem p.control (publicValues keys)) ?_ (by decide) (by decide)
      (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
  · unfold rejectedPublic writeController publicValues
    simp only [List.foldl_cons, List.foldl_nil]
    brun [ldf, stf, h.x19, imm64 (show 4 < 65536 by decide), imm64 (show 128 < 65536 by decide),
      hv0, e0, a.ld0, a.st0, a.ld 0 (by decide), a.st 0 (by decide), a.st 8 (by decide), a.st 112 (by decide)]
    rfl
  have hh : Slots t.mem p.control (p.headers used (keys - 1) 128) := by
    refine headers_after _ (publicValues_bound keys) hm ?_
    intro e he
    simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [controllerValue, publicValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false] <;>
      first | rfl | exact h.header (by simp [KeyPublic.headers])
  refine ⟨h.update h.used_le (by have := h.keys_le; omega) (by decide) _ (publicValues_bound keys)
    (by simp only [publicValues, List.mem_cons, List.not_mem_nil, or_false]
        rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide) hm k.mono hh, ?_⟩
  rw [show (112 : Nat) = 8 * 14 from rfl, hm, writeController_word _ _ _ (publicValues_bound keys) 14 (by decide)]
  simp only [controllerValue, publicValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
    ite_true, ite_false]

end VG.Proof.Ffdh.AArch64.Cached.SearchProof
