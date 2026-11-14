module

import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Live
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.AttemptPost
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Compare
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Memory
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Fields
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Exit
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Regions
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Outputs
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Policy

/-! ### `Ffdh.Arm.KeySearch.Update`, which only this module used -/

section

/-! ### `Ffdh.Arm.KeySearch.Advance`, which only this module used -/

section

/-! Each attempt consumes exactly the public domain width from the entropy
tape, independent of its secret acceptance status. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

def advanceValues (m : Mem) (base : BitVec 32) : List (Nat × BitVec 32) :=
  [(9, lowWord m base 9 + lowWord m base 2),
    (10, lowWord m base 10 - lowWord m base 2),
    (11, lowWord m base 11 + lowWord m base 2)]

theorem advanceLoads_ok (s : State) {base : BitVec 32} (h : Controller base s) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.advanceLoads) s fun t =>
      (t.gpr .r9 = s.gpr .r0 ∧ t.gpr .r10 = lowWord s.mem base 2 ∧
        t.gpr .r11 = lowWord s.mem base 9 ∧ t.gpr .r12 = lowWord s.mem base 10 ∧
        t.gpr .r3 = lowWord s.mem base 11 ∧ t.mem = s.mem) ∧ Rest [.r3, .r9, .r10, .r11, .r12] s t := by
  refine withRest_all [.r3, .r9, .r10, .r11, .r12] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.KeySearch.advanceLoads VG.Impl.Ffdh.Arm.KeySearch.ldf lowWord
  ffrun [h.addr (by decide : 2 < 16), h.addr (by decide : 9 < 16), h.addr (by decide : 10 < 16), h.addr (by decide : 11 < 16),
    h.read (by decide : 2 < 16), h.read (by decide : 9 < 16), h.read (by decide : 10 < 16), h.read (by decide : 11 < 16)]

theorem advance_ok (s : State) {base : BitVec 32} (h : Controller base s) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.advance) s fun t =>
      (t.gpr .r9 = s.gpr .r0 ∧ t.mem = writeLow s.mem base (advanceValues s.mem base)) ∧
      Rest [.r3, .r9, .r10, .r11, .r12] s t := by
  refine withRest_all [.r3, .r9, .r10, .r11, .r12] ?_ (by rfl) (by rfl)
  rw [VG.Impl.Ffdh.Arm.KeySearch.advance, WP.block_append_iff]
  refine WP.mono (advanceLoads_ok s h) ?_
  rintro u ⟨⟨status, width, ptr, length, used, mem⟩, rest⟩
  have context : Controller base u := ⟨h.space.congr rest.wr, (rest.gpr .r4 (by simp)).trans h.ptr⟩
  unfold VG.Impl.Ffdh.Arm.KeySearch.advanceUpdate VG.Impl.Ffdh.Arm.KeySearch.stf writeLow advanceValues
  simp only [List.foldl_cons, List.foldl_nil]
  ffrun [status, width, ptr, length, used, mem,
    context.addr (by decide : 9 < 16), context.addr (by decide : 10 < 16), context.addr (by decide : 11 < 16),
    context.write (by decide : 9 < 16), context.write (by decide : 10 < 16), context.write (by decide : 11 < 16)]

def scalarValues (m : Mem) (base : BitVec 32) : List (Nat × BitVec 32) :=
  [(1, lowWord m base 1 - 1), (14, 4)]

def publicValues (m : Mem) (base : BitVec 32) : List (Nat × BitVec 32) :=
  [(0, lowWord m base 0 - 1), (1, 128), (14, 4)]

theorem rejectedScalar_ok (s : State) {base : BitVec 32} (h : Controller base s) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.rejectedScalar) s fun t =>
      t.mem = writeLow s.mem base (scalarValues s.mem base) ∧ Rest [.r10, .r11] s t := by
  refine withRest_all [.r10, .r11] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.KeySearch.rejectedScalar VG.Impl.Ffdh.Arm.KeySearch.ldf VG.Impl.Ffdh.Arm.KeySearch.stf
    writeLow scalarValues lowWord
  simp only [List.foldl_cons, List.foldl_nil]
  ffrun [h.addr (by decide : 1 < 16), h.addr (by decide : 14 < 16), h.read (by decide : 1 < 16),
    h.write (by decide : 1 < 16), h.write (by decide : 14 < 16)]

theorem rejectedPublic_ok (s : State) {base : BitVec 32} (h : Controller base s) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.rejectedPublic) s fun t =>
      t.mem = writeLow s.mem base (publicValues s.mem base) ∧ Rest [.r10, .r11, .r12] s t := by
  refine withRest_all [.r10, .r11, .r12] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.KeySearch.rejectedPublic VG.Impl.Ffdh.Arm.KeySearch.ldf VG.Impl.Ffdh.Arm.KeySearch.stf
    writeLow publicValues lowWord
  simp only [List.foldl_cons, List.foldl_nil]
  ffrun [h.addr (by decide : 0 < 16), h.addr (by decide : 1 < 16), h.addr (by decide : 14 < 16),
    h.read (by decide : 0 < 16), h.write (by decide : 0 < 16), h.write (by decide : 1 < 16), h.write (by decide : 14 < 16)]

end VG.Proof.Ffdh.Arm.KeySearch

end

end


/-! The retry controller consumes one scalar width per attempt, then updates
exactly the rejection budget corresponding to its returned status. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

theorem KeyLive.advance_fields {p : KeyPublic sampling} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (room : used + p.len ≤ p.randLen) :
    Slots (writeLow s.mem p.control (advanceValues s.mem p.control)) p.control
      (p.headers (used + p.len) keys scalars) := by
  have w2 := h.field (j := 2) (by simp [headerIndices])
  have w9 := h.field (j := 9) (by simp [headerIndices])
  have w10 := h.field (j := 10) (by simp [headerIndices])
  have w11 := h.field (j := 11) (by simp [headerIndices])
  have rem : BitVec.ofNat 32 (p.randLen - used) - BitVec.ofNat 32 p.len =
      BitVec.ofNat 32 (p.randLen - (used + p.len)) := by
    rw [Offset.ofNat_sub_ofNat (by omega_using [room] : p.len ≤ p.randLen - used), Nat.sub_sub]
  apply (slots_fields _ _ _ _ _ _).mpr
  intro j hj
  rw [lowWord_writeLow _ _ _ (by simp [advanceValues]) j (headerIndices_bound hj), h.field hj]
  simp only [KeyPublic.field] at w2 w9 w10 w11
  simp only [headerIndices, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [lowValue, advanceValues, KeyPublic.field, w2, w9, w10, w11,
    BitVec.add_assoc, ← BitVec.ofNat_add, rem]

theorem KeyLive.advance {p : KeyPublic sampling} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (room : used + p.len ≤ p.randLen) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.advance) s fun t =>
      KeyLive p original (used + p.len) keys scalars t ∧ t.gpr .r9 = s.gpr .r0 ∧
        Frame [⟨State.addr p.control, 128⟩] s.mem t.mem := by
  refine WP.mono_syms (advance_ok s h.controller) ?_
  rintro t ⟨⟨status, mem⟩, rest⟩ syms
  refine ⟨h.update rest syms (by decide) (advanceValues s.mem p.control) (by simp [advanceValues]) (by simp [advanceValues])
    mem room h.keys_le h.scalars_le ?_, status, ?_⟩
  · rw [mem]; exact h.advance_fields room
  · rw [mem]; exact writeLow_frame _ _ _ (by simp [advanceValues])

theorem KeyLive.scalar_fields {p : KeyPublic sampling} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (positive : 0 < scalars) :
    Slots (writeLow s.mem p.control (scalarValues s.mem p.control)) p.control
      (p.headers used keys (scalars - 1)) := by
  have w1 := h.field (j := 1) (by simp [headerIndices])
  simp only [KeyPublic.field] at w1
  apply (slots_fields _ _ _ _ _ _).mpr
  intro j hj
  rw [lowWord_writeLow _ _ _ (by simp [scalarValues]) j (headerIndices_bound hj), h.field hj]
  have sub : BitVec.ofNat 32 scalars - 1#32 = BitVec.ofNat 32 (scalars - 1) :=
    Offset.ofNat_sub_ofNat (by omega_using [positive] : 1 ≤ scalars)
  simp only [headerIndices, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [lowValue, scalarValues, KeyPublic.field, w1, sub]

theorem KeyLive.reject_scalar {p : KeyPublic sampling} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (positive : 0 < scalars) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.rejectedScalar) s fun t =>
      KeyLive p original used keys (scalars - 1) t ∧ lowWord t.mem p.control 14 = 4 := by
  refine WP.mono_syms (rejectedScalar_ok s h.controller) ?_
  rintro t ⟨mem, rest⟩ syms
  refine ⟨h.update rest syms (by decide) (scalarValues s.mem p.control) (by simp [scalarValues]) (by simp [scalarValues])
    mem h.used_le h.keys_le (by have := h.scalars_le; omega_using [this]) ?_, ?_⟩
  · rw [mem]; exact h.scalar_fields positive
  · rw [mem, lowWord_writeLow _ _ _ (by simp [scalarValues]) 14 (by decide)]
    simp [scalarValues, lowValue]

theorem KeyLive.public_fields {p : KeyPublic sampling} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (positive : 0 < keys) :
    Slots (writeLow s.mem p.control (publicValues s.mem p.control)) p.control
      (p.headers used (keys - 1) 128) := by
  have w0 := h.field (j := 0) (by simp [headerIndices])
  simp only [KeyPublic.field] at w0
  apply (slots_fields _ _ _ _ _ _).mpr
  intro j hj
  rw [lowWord_writeLow _ _ _ (by simp [publicValues]) j (headerIndices_bound hj), h.field hj]
  have sub : BitVec.ofNat 32 keys - 1#32 = BitVec.ofNat 32 (keys - 1) :=
    Offset.ofNat_sub_ofNat (by omega_using [positive] : 1 ≤ keys)
  simp only [headerIndices, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [lowValue, publicValues, KeyPublic.field, w0, sub]

theorem KeyLive.reject_public {p : KeyPublic sampling} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (positive : 0 < keys) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.rejectedPublic) s fun t =>
      KeyLive p original used (keys - 1) 128 t ∧ lowWord t.mem p.control 14 = 4 := by
  refine WP.mono_syms (rejectedPublic_ok s h.controller) ?_
  rintro t ⟨mem, rest⟩ syms
  refine ⟨h.update rest syms (by decide) (publicValues s.mem p.control) (by simp [publicValues]) (by simp [publicValues])
    mem h.used_le (by have := h.keys_le; omega_using [this]) (by decide) ?_, ?_⟩
  · rw [mem]; exact h.public_fields positive
  · rw [mem, lowWord_writeLow _ _ _ (by simp [publicValues]) 14 (by decide)]
    simp [publicValues, lowValue]

end VG.Proof.Ffdh.Arm.KeySearch

end

end


/-! Composition of entropy consumption with acceptance and the two kinds of rejection. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont

abbrev KeyClassified (p : KeyPublic sampling) (original : State) (used keys scalars : Nat) (s : State) : Prop :=
  if currentStatus p original used = 1 then KeyDone p original (acceptedResult p original used) s
  else if currentStatus p original used = 2 then
    KeyLive p original (used + p.len) keys (scalars - 1) s ∧ lowWord s.mem p.control 14 = 4
  else KeyLive p original (used + p.len) (keys - 1) 128 s ∧ lowWord s.mem p.control 14 = 4

theorem classify_head {p : KeyPublic sampling} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (room : used + p.len ≤ p.randLen)
    (post : AttemptPost p original used s) :
    WP isa (.block (VG.Impl.Ffdh.Arm.KeySearch.advance ++ ([.cmp .r9 (.imm 1)] : List Instr))) s fun t =>
      KeyLive p original (used + p.len) keys scalars t ∧
      t.z = decide (currentStatus p original used = 1) ∧
      t.gpr .r9 = BitVec.ofNat 32 (currentStatus p original used) ∧
      Frame [rControl p] s.mem t.mem := by
  have bound : currentStatus p original used < 4 := by
    rcases currentStatus_cases p original used with eq | eq | eq <;> omega_using [eq]
  have native : s.gpr .r0 = BitVec.ofNat 32 (currentStatus p original used) := by
    rw [← post.status, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [WP.block_append_iff]
  refine WP.mono (h.advance room) ?_
  rintro u ⟨live, status, frame⟩
  refine WP.mono_syms (compareStatus_ok u bound (by decide : 1 < 4) (status.trans native)) ?_
  rintro t ⟨⟨flag, mem⟩, rest⟩ syms
  exact ⟨live.keep rest mem syms, flag, (rest.gpr .r9 (by simp)).trans (status.trans native), by rw [mem]; exact frame⟩

theorem classify {p : KeyPublic sampling} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (room : used + p.len ≤ p.randLen)
    (keysPositive : 0 < keys) (scalarsPositive : 0 < scalars) (post : AttemptPost p original used s) :
    WP isa VG.Impl.Ffdh.Arm.KeySearch.classify s (KeyClassified p original used keys scalars) := by
  rw [VG.Impl.Ffdh.Arm.KeySearch.classify, WP.seq_iff]
  refine WP.mono (classify_head h room post) ?_
  rintro u ⟨live, flag, status, frame⟩
  rcases currentStatus_cases p original used with h1 | h2 | h3
  · simp only [h1, decide_true] at flag
    have target : KeyClassified p original used keys scalars =
        KeyDone p original (acceptedResult p original used) := by
      funext t
      simp only [KeyClassified, h1, ite_true]
    rw [target]
    refine WP.ite true (by change some u.z = some true; rw [flag]) ?_ (by intro bad; cases bad)
    intro _
    have oldOutput : KeyOutput p (acceptedResult p original used) s.mem := by
      simpa only [h1, ite_true, KeyOutput, acceptedResult] using post.output
    have output := oldOutput.control_frame h.input frame
    refine WP.mono (live.terminal (status := 1) (.inl rfl)) ?_
    rintro t ⟨done, result, request, high, terminalFrame⟩
    apply done.done (result := acceptedResult p original used) rfl result
    · exact done.policy (request := 0) (by decide) request high
    · exact output.control_frame h.input terminalFrame
  · simp only [h2, show (2 : Nat) ≠ 1 by decide, decide_false] at flag
    have target : KeyClassified p original used keys scalars = (fun t =>
        KeyLive p original (used + p.len) keys (scalars - 1) t ∧ lowWord t.mem p.control 14 = 4) := by
      funext t
      simp only [KeyClassified, h2, show (2 : Nat) ≠ 1 by decide, ite_false, ite_true]
    rw [target]
    refine WP.ite false (by change some u.z = some false; rw [flag]) (by intro bad; cases bad) ?_
    intro _
    rw [WP.seq_iff]
    refine WP.mono_syms (compareStatus_ok u (by rw [h2]; decide) (by decide : 2 < 4) status) ?_
    rintro t ⟨⟨test, mem⟩, rest⟩ syms
    have kept := live.keep rest mem syms
    simp only [h2, decide_true] at test
    refine WP.ite true (by change some t.z = some true; rw [test]) ?_ (by intro bad; cases bad)
    intro _
    exact kept.reject_scalar scalarsPositive
  · simp only [h3, show (3 : Nat) ≠ 1 by decide, decide_false] at flag
    have target : KeyClassified p original used keys scalars = (fun t =>
        KeyLive p original (used + p.len) (keys - 1) 128 t ∧ lowWord t.mem p.control 14 = 4) := by
      funext t
      simp only [KeyClassified, h3, show (3 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 2 by decide, ite_false]
    rw [target]
    refine WP.ite false (by change some u.z = some false; rw [flag]) (by intro bad; cases bad) ?_
    intro _
    rw [WP.seq_iff]
    refine WP.mono_syms (compareStatus_ok u (by rw [h3]; decide) (by decide : 2 < 4) status) ?_
    rintro t ⟨⟨test, mem⟩, rest⟩ syms
    have kept := live.keep rest mem syms
    have statusT := (rest.gpr .r9 (by simp)).trans status
    simp only [h3, show (3 : Nat) ≠ 2 by decide, decide_false] at test
    refine WP.ite false (by change some t.z = some false; rw [test]) (by intro bad; cases bad) ?_
    intro _
    rw [WP.seq_iff]
    refine WP.mono_syms (compareStatus_ok t (by rw [h3]; decide) (by decide : 3 < 4) statusT) ?_
    rintro q ⟨⟨test3, mem3⟩, rest3⟩ syms3
    have kept3 := kept.keep rest3 mem3 syms3
    simp only [h3, decide_true] at test3
    refine WP.ite true (by change some q.z = some true; rw [test3]) ?_ (by intro bad; cases bad)
    intro _
    exact kept3.reject_public keysPositive

end VG.Proof.Ffdh.Arm.KeySearch
