module

public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Writes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Outputs
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Live
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ZeroOut
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Start

/-! # The key-generation controller's exits without a key: exhausted, or short -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.Ffdh.X86_64 (Slots)
open VG.Proof.Ffdh.X86_64.Generation (writeController writeController_word controllerValue
  controllerValue_unchanged controller_zero_out)
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

theorem KeyLive.done {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) {r : Spec.Ffdh.KeySearchResult} (hu : r.used = used)
    (hs : word s.mem p.control 112 = BitVec.ofNat 64 r.status)
    (hp : Spec.Rsa.wordsAt s.mem p.control 4 = p.policy r)
    (ho : KeyOutput p r s.mem) : KeyDone p original r s :=
  ⟨h.input, h.rd, h.wr, h.rsp, h.r12, h.saved, h.savedR12,
    h.header (j := 15) (by simp [KeyPublic.headers]),
    by rw [hu]; exact h.header (j := 11) (by simp [KeyPublic.headers]), hs, hp, ho⟩

/-- Zeros at `x` and `y`, which keeps the controller's words. -/
theorem key_zero_outputs {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa zeroOutputs s fun t =>
      KeyLive p original used keys scalars t ∧
      Spec.Rsa.bytesAt t.mem p.xp p.len = List.replicate p.len 0 ∧
      Spec.Rsa.bytesAt t.mem p.yp p.len = List.replicate p.len 0 ∧
      (∀ j < 16, word t.mem p.control (8 * j) = word s.mem p.control (8 * j)) := by
  have hk := h.input.len_bounds
  have hxw := h.input.x_mem
  have hyw := h.input.y_mem
  have hxc := h.input.x_ne_ctl
  have hyc := h.input.y_ne_ctl
  unfold zeroOutputs
  refine WP.seq (WP.mono (WP.keep [.rdi] (Q := fun u => u.gpr .rdi = p.control ∧ u.mem = s.mem)
    (by xrun [h.r12]) rfl) fun u ⟨⟨hdi, hmu⟩, ku⟩ => ?_)
  have hu := h.keep ku hmu (by decide)
  have scr := h.input.control_scr (t := u) hu.wr
  refine WP.seq (WP.mono (controller_zero_out scr hdi (by decide) (sPtr := 5) (sLen := 2) (by decide)
    (by decide) (hu.header (by simp [KeyPublic.headers])) (hu.header (by simp [KeyPublic.headers]))
    (by omega) (by omega) (h.input.output_x hu.wr)) fun v ⟨hv, hfv, kv⟩ => ?_)
  have hvl := zero_live hu hxw hxc hfv kv
  have hdv : v.gpr .rdi = p.control := (kv.gpr (by decide)).trans hdi
  have scr' := h.input.control_scr (t := v) hvl.wr
  refine WP.mono (controller_zero_out scr' hdv (by decide) (sPtr := 6) (sLen := 2) (by decide)
    (by decide) (hvl.header (by simp [KeyPublic.headers])) (hvl.header (by simp [KeyPublic.headers]))
    (by omega) (by omega) (h.input.output_y hvl.wr)) fun t ⟨ht, hft, kt⟩ => ?_
  have htl := zero_live hvl hyw hyc hft kt
  have hxy := h.input.xy_disjoint
  have hk64 : p.len < 2 ^ 64 := by omega
  refine ⟨htl, ?_, ?_, ?_⟩
  · refine List.eq_replicate_iff.mpr ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range], ?_⟩
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    have hi' := List.mem_range.mp hi
    rw [hft _ (fun j hj he => hxy _ (contains_byte _ hi' (by omega)) (by
      rw [he]; exact contains_byte _ hj (by omega)))]
    exact hv i hi'
  · refine List.eq_replicate_iff.mpr ⟨by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range], ?_⟩
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ht i (List.mem_range.mp hi)
  · intro j hj
    have hf := (zero_frame h.input hxw hxc hfv).trans (zero_frame h.input hyw hyc hft)
    rw [h.input.control_frame hf j hj, hmu]

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

/-- A terminal status written over a loop state, with no budgets left. -/
theorem key_terminal_live {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (status : Nat) :
    WP isa (.block (terminal status)) s fun t =>
      KeyLive p original used 0 0 t ∧ t.mem = writeController s.mem p.control (terminalValues status) := by
  have scr := h.input.control_scr (t := s) h.wr
  refine WP.mono (key_terminal_ok scr h.r12 status) fun t ⟨_, hm, k⟩ => ?_
  have hh : Slots t.mem p.control (p.headers used 0 0) := by
    refine headers_after _ (terminalValues_bound status) hm ?_
    intro e he
    simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [controllerValue, terminalValues, List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff,
        ite_true, ite_false] <;>
      first | rfl | exact h.header (by simp [KeyPublic.headers])
  have ht := h.update (u := used) (k := 0) (c := 0) h.used_le (by decide) (by decide) _
    (terminalValues_bound status) (by
      simp only [terminalValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide) hm k.2.1 k.2.2
    (fun r hr => k.gpr (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) hh
  exact ⟨ht, hm⟩

theorem key_exhausted {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa exhausted s (KeyDone p original ⟨.exhausted, used, []⟩) := by
  unfold exhausted
  refine WP.seq (WP.mono (key_terminal_live h 3) fun t ⟨ht, hm⟩ => ?_)
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

def requestValues (p : KeyPublic) : List (Nat × BitVec 64) := [(3, BitVec.ofNat 64 p.len), (14, 0)]

theorem requestValues_bound (p : KeyPublic) : ∀ e ∈ requestValues p, e.1 < 16 := by
  simp only [requestValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl) <;> dsimp only <;> decide

theorem key_request_words {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block [.mov .rax (.mem (field 2)), .store (field 3) .rax, .mov32 .rax (.imm 0),
      .store (field 14) .rax]) s fun t =>
      t.mem = writeController s.mem p.control (requestValues p) ∧ Keep [.rax] s t := by
  have scr := h.input.control_scr (t := s) h.wr
  have hs : ∀ d, d + 8 ≤ 128 → InRegions s.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hv2 := h.header (j := 2) (v := BitVec.ofNat 64 p.len) (by simp [KeyPublic.headers])
  simp only [Bignum.word, off] at hv2
  refine WP.keep [.rax] ?_ rfl
  unfold writeController requestValues
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, h.r12, BitVec.ofInt_natCast, Nat.reduceMul, hv2,
    hl 16 (by decide), hs 24 (by decide), hs 112 (by decide)]
  rfl

theorem key_request_live {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa (.block [.mov .rax (.mem (field 2)), .store (field 3) .rax, .mov32 .rax (.imm 0),
      .store (field 14) .rax]) s fun t =>
      KeyLive p original used keys scalars t ∧ t.mem = writeController s.mem p.control (requestValues p) := by
  refine WP.mono (key_request_words h) fun t ⟨hm, k⟩ => ?_
  have hh : Slots t.mem p.control (p.headers used keys scalars) := by
    refine headers_after _ (requestValues_bound p) hm ?_
    intro e he
    have hj := KeyPublic.headers_index he
    rw [controllerValue_unchanged _ _ _ (by
      intro x hx
      simp only [requestValues, List.mem_cons, List.not_mem_nil, or_false] at hx
      simp only [KeyPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases hx with rfl | rfl <;>
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        dsimp only <;> decide)]
    exact h.headers e he
  have ht := h.update (u := used) (k := keys) (c := scalars) h.used_le h.keys_le h.scalars_le _
    (requestValues_bound p) (by
      simp only [requestValues, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl) <;> dsimp only <;> decide) hm k.2.1 k.2.2
    (fun r hr => k.gpr (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) hh
  exact ⟨ht, hm⟩

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
    rw [hw 14 (by decide)]
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

end VG.Proof.Ffdh.X86_64.KeyGeneration
