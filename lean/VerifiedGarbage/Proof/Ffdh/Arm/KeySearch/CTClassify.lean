module

import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Live
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTPoint
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTPoint
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTFrames
public import VerifiedGarbage.Proof.Ffdh.CachedGenerateKeyContract
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ConstantContract
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Memory
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ArgumentWords
import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBackend
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Allocated
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.LoopState
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallPreserves
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Regions
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.Workspace
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Allocated
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Arguments
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Arguments
meta import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.AttemptPost
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTFrames
meta import VerifiedGarbage.Proof.Ffdh.CachedGenerateKeyContract
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ConstantContract
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Memory
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ArgumentWords
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeyBackend
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.LoopState
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Arm.Syms
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallPreserves
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Regions
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.CallF
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Live
meta import VerifiedGarbage.Proof.Ffdh.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.AttemptPost
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Exit
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Outputs
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Outputs
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Exit
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Fields
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.X25519.Arm.Instr
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
meta import VerifiedGarbage.Proof.Ffdh.Arm.Block
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Fields
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.X25519.Arm.Instr

/-! ### `Ffdh.Arm.KeySearch.Classify`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.KeySearch.Compare`, which this module and modules that import it used -/

section

/-! Comparisons of the three public key-attempt statuses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch

open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

theorem compareStatus_ok (s : State) {status test : Nat} (small : status < 4) (testSmall : test < 4)
    (value : s.gpr .r9 = BitVec.ofNat 32 status) :
    WP isa (.block [.cmp .r9 (.imm (BitVec.ofNat 32 test))]) s fun t =>
      (t.z = decide (status = test) ∧ t.mem = s.mem) ∧ Rest [] s t := by
  refine withRest [] ?_ (by
    intro r _ i hi
    simp only [instrs, List.mem_singleton] at hi
    subst i
    rfl) (by rfl)
  have casesStatus : status = 0 ∨ status = 1 ∨ status = 2 ∨ status = 3 := by omega_using [small]
  have casesTest : test = 0 ∨ test = 1 ∨ test = 2 ∨ test = 3 := by omega_using [testSmall]
  rcases casesStatus with rfl | rfl | rfl | rfl <;>
    rcases casesTest with rfl | rfl | rfl | rfl <;> ffrun [value]

end VG.Proof.Ffdh.Arm.KeySearch

end

end

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

end

end

/-! ### `Ffdh.Arm.KeySearch.CTLeaf`, which this module and modules that import it used -/

section

/-! Rejections and incomplete searches clear outputs on public addresses
and public-length schedules; scalar and output bytes do not affect timing. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm

def KeyZeroCT (j : Nat) (p : KeyPublic sampling) (s : State) : Prop :=
  KeyAny p s ∧ s.gpr .r0 = (if j = 5 then p.xp else p.yp) ∧ s.gpr .lr = BitVec.ofNat 32 p.len

private theorem zero_header (j : Nat) (which : j = 5 ∨ j = 6) (p : KeyPublic sampling) (s : State)
    (h : KeyAny p s) :
    WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 j, VG.Impl.Ffdh.Arm.KeySearch.ldf .lr 2,
      .mov .r2 (.imm 0)]) s (KeyZeroCT j p) := by
  obtain ⟨original, used, keys, scalars, live⟩ := h
  have pointer : lowWord s.mem p.control j = (if j = 5 then p.xp else p.yp) := by
    rcases which with rfl | rfl <;> exact live.header (by simp [KeyPublic.headers])
  have slot : j < 16 := by rcases which with rfl | rfl <;> decide
  refine WP.mono_syms (zeroOutputArgs_ok s (n := p.len) live.controller slot pointer
    (live.header (by simp [KeyPublic.headers]))) ?_
  rintro t ⟨⟨ptr, count, _, mem⟩, rest⟩ syms
  exact ⟨⟨original, _, _, _, live.keep rest mem syms⟩, ptr, count⟩

private theorem zero_ct (j : Nat) (which : j = 5 ∨ j = 6) :
    RelCT isa (Two (KeyAny (sampling := sampling))) (VG.Impl.Ffdh.Arm.KeySearch.zeroOutput j) (fun _ _ => True) := by
  rcases which with rfl | rfl <;> unfold VG.Impl.Ffdh.Arm.KeySearch.zeroOutput
  all_goals
    refine RelCT.seq (two_piece [.r4] key_any_pins (by taint_decide) (zero_header _ (by decide))) ?_
    exact two_taint [.r0, .lr] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁.2.1.trans h₂.2.1.symm
      · exact h₁.2.2.trans h₂.2.2.symm) (by taint_decide)

private theorem zero_ready (p : KeyPublic sampling) (s : State) (h : KeyAny p s) :
    WP isa (VG.Impl.Ffdh.Arm.KeySearch.zeroOutput 5) s (KeyAny p) := by
  obtain ⟨original, used, keys, scalars, live⟩ := h
  refine WP.mono_syms (zeroOutput_ok s (n := p.len) (dst := p.xp) live.controller (by decide : 5 < 16)
    (by have := live.input.bounds.minLength; omega_using [this]) (by have := live.input.bounds.maxLength; omega_using [this])
    (live.header (by simp [KeyPublic.headers])) (live.header (by simp [KeyPublic.headers])) live.x_buffer) ?_
  rintro t ⟨_, frame, rest⟩ syms
  exact ⟨original, _, _, _, live.restore rest.rd rest.wr rest.sp
    (fun r hr => rest.gpr r (by revert r hr; decide)) syms (frame.mono (by simp [callChanges]))⟩

theorem zero_outputs_ct : RelCT isa (Two (KeyAny (sampling := sampling))) VG.Impl.Ffdh.Arm.KeySearch.zeroOutputs (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.KeySearch.zeroOutputs
  exact RelCT.seq (two_post (zero_ct 5 (.inl rfl)) zero_ready) (zero_ct 6 (.inr rfl))

private theorem terminal_ready (p : KeyPublic sampling) (s : State) (h : KeyAny p s) :
    WP isa (.block (VG.Impl.Ffdh.Arm.KeySearch.terminal 3)) s (KeyAny p) := by
  obtain ⟨original, _, _, _, live⟩ := h
  exact WP.mono (live.terminal (status := 3) (.inr rfl)) fun _ ⟨ready, _⟩ => ⟨original, _, _, _, ready⟩

theorem exhausted_ct : RelCT isa (Two (KeyAny (sampling := sampling))) VG.Impl.Ffdh.Arm.KeySearch.exhausted (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.KeySearch.exhausted
  exact RelCT.seq (two_piece [.r4] key_any_pins (by taint_decide) terminal_ready) zero_outputs_ct

private theorem request_ready (p : KeyPublic sampling) (s : State) (h : KeyAny p s) :
    WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r10 2, .mov .r11 (.imm 0),
      VG.Impl.Ffdh.Arm.KeySearch.stf .r10 3, .str .r11 .r4 28,
      VG.Impl.Ffdh.Arm.KeySearch.stf .r11 14]) s (KeyAny p) := by
  obtain ⟨original, _, _, _, live⟩ := h
  exact WP.mono live.request_block fun _ ⟨ready, _⟩ => ⟨original, _, _, _, ready⟩

theorem request_ct : RelCT isa (Two (KeyAny (sampling := sampling))) VG.Impl.Ffdh.Arm.KeySearch.request (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.KeySearch.request
  exact RelCT.seq (two_piece [.r4] key_any_pins (by taint_decide) request_ready) zero_outputs_ct

theorem accepted_ct : RelCT isa (Two (KeyAny (sampling := sampling))) (.block (VG.Impl.Ffdh.Arm.KeySearch.terminal 1)) (fun _ _ => True) :=
  two_taint [.r4] key_any_pins (by taint_decide)

theorem rejected_scalar_ct : RelCT isa (Two (KeyAny (sampling := sampling))) (.block VG.Impl.Ffdh.Arm.KeySearch.rejectedScalar) (fun _ _ => True) :=
  two_taint [.r4] key_any_pins (by taint_decide)

theorem rejected_public_ct : RelCT isa (Two (KeyAny (sampling := sampling))) (.block VG.Impl.Ffdh.Arm.KeySearch.rejectedPublic) (fun _ _ => True) :=
  two_taint [.r4] key_any_pins (by taint_decide)

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! ### `Ffdh.Arm.KeySearch.CTAttempt`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.KeySearch.CTArguments`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.KeySearch.CTAttemptState`, which this module and modules that import it used -/

section

/-! Before allocation, after argument setup, and after a native key attempt,
with the disclosed attempt-status sequence retained in the proof state. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

def KeyReady (q : KeyPoint sampling) (s : State) : Prop :=
  KeyCTL q s ∧ q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen

def KeyAllocated (q : KeyPoint sampling) (u : State) : Prop := ∃ s, KeyReady q s ∧ u = allocated (GenerationPolicy.argumentBytes sampling) s

def KeyCallCT (q : KeyPoint sampling) (u : State) : Prop :=
  ∃ original s, KeyLive q.inputs original q.used q.keys q.scalars s ∧
    (q.inputs.tail (keyRand q.inputs original) q.used q.keys q.scalars).statuses = q.statuses ∧
    q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen ∧
    ArgumentContext q.inputs q.used q.keys q.scalars u ∧
    u.mem = callMem q.inputs q.used s.mem (callSp q.inputs) ∧
    Rest [.r0, .r1, .r2, .r3, .r9, .r12] (allocated (GenerationPolicy.argumentBytes sampling) s) u ∧ u.syms = s.syms

def KeyAttempted (q : KeyPoint sampling) (t : State) : Prop :=
  ∃ original, KeyLive q.inputs original q.used q.keys q.scalars t ∧
    (q.inputs.tail (keyRand q.inputs original) q.used q.keys q.scalars).statuses = q.statuses ∧
    q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen ∧
    AttemptPost q.inputs original q.used t

theorem key_allocated_pins : Pins (KeyAllocated (sampling := sampling)) [.r4] := by
  rintro q _ _ ⟨s, ⟨⟨_, h₁, _⟩, _⟩, rfl⟩ ⟨t, ⟨⟨_, h₂, _⟩, _⟩, rfl⟩ r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h₁.pointer.trans h₂.pointer.symm

theorem arguments_ready (q : KeyPoint sampling) (u : State) (h : KeyAllocated q u) :
    WP isa (.block (VG.Impl.Ffdh.Arm.KeySearch.argumentsFor sampling.cachedContext)) u (KeyCallCT q) := by
  obtain ⟨s, ⟨⟨original, live, statuses⟩, keys, scalars, room⟩, rfl⟩ := h
  obtain ⟨control, stack, separate⟩ := live.allocated_data
  have sep : (rControl q.inputs).Disjoint ⟨State.addr (allocated (GenerationPolicy.argumentBytes sampling) s).sp, sampling.argumentBytes⟩ := by
    rw [live.call_sp]; exact separate
  refine WP.mono_syms (arguments_ok (allocated (GenerationPolicy.argumentBytes sampling) s) control stack sep live.headers live.cachedSlots) ?_
  rintro t ⟨⟨args, mem⟩, rest⟩ syms
  refine ⟨original, s, live, statuses, keys, scalars, room, args, ?_, rest, syms⟩
  rw [mem, live.call_sp]
  rfl


end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! Native argument setup uses only the public controller and stack
addresses, even when loading secret scalar/output registers afterward. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Bignum.Arm

def ArgumentPins (q : KeyPoint sampling) (s : State) : Prop :=
  s.gpr .r4 = q.inputs.control ∧ s.gpr .r12 = callSp q.inputs

private theorem head_ready (q : KeyPoint sampling) (u : State) (h : KeyAllocated q u) :
    WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 5, VG.Impl.Ffdh.Arm.KeySearch.ldf .r1 2,
      VG.Impl.Ffdh.Arm.KeySearch.ldf .r2 6, VG.Impl.Ffdh.Arm.KeySearch.ldf .r3 2, .addSp .r12 0]) u (ArgumentPins q) := by
  obtain ⟨s, ⟨⟨_, live, _⟩, _⟩, rfl⟩ := h
  refine WP.mono (argumentHead_ok (allocated (GenerationPolicy.argumentBytes sampling) s) (x := q.inputs.xp) (y := q.inputs.yp) (n := q.inputs.len) live.allocated_data.1
    (live.header (by simp [KeyPublic.headers])) (live.header (by simp [KeyPublic.headers]))
    (live.header (by simp [KeyPublic.headers]))) ?_
  rintro t ⟨⟨_, _, _, _, pointer, _⟩, rest⟩
  exact ⟨(rest.gpr .r4 (by simp)).trans live.pointer, pointer.trans live.call_sp⟩

private theorem head_ct :
    RelCT isa (Two (KeyAllocated (sampling := sampling))) (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 5,
      VG.Impl.Ffdh.Arm.KeySearch.ldf .r1 2, VG.Impl.Ffdh.Arm.KeySearch.ldf .r2 6,
      VG.Impl.Ffdh.Arm.KeySearch.ldf .r3 2, .addSp .r12 0]) (fun _ _ => True) := by
  change RelCT isa _ (.block ([VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 5,
    VG.Impl.Ffdh.Arm.KeySearch.ldf .r1 2, VG.Impl.Ffdh.Arm.KeySearch.ldf .r2 6,
    VG.Impl.Ffdh.Arm.KeySearch.ldf .r3 2] ++ [.addSp .r12 0])) _
  refine RelCT.block_append (RelCT.seq
    (relCT_keep_sp (two_taint [.r4] key_allocated_pins (by taint_decide)) (fun _ _ ⟨_, _, _, sp⟩ => sp)) ?_)
  exact VG.Proof.Ffdh.Arm.stackAddr_ct.mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem arguments_ct : RelCT isa (Two (KeyAllocated (sampling := sampling)))
    (.block (VG.Impl.Ffdh.Arm.KeySearch.argumentsFor sampling.cachedContext)) (fun _ _ => True) := by
  cases sampling <;>
    change RelCT isa _ (.block ([VG.Impl.Ffdh.Arm.KeySearch.ldf .r0 5,
      VG.Impl.Ffdh.Arm.KeySearch.ldf .r1 2, VG.Impl.Ffdh.Arm.KeySearch.ldf .r2 6,
      VG.Impl.Ffdh.Arm.KeySearch.ldf .r3 2, .addSp .r12 0] ++ _)) _
  all_goals refine RelCT.block_append (RelCT.seq (two_post head_ct head_ready) ?_)
  all_goals exact two_taint [.r4, .r12] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁.1.trans h₂.1.symm
    · exact h₁.2.trans h₂.2.symm) (by taint_decide)

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! ### `Ffdh.Arm.KeySearch.Call`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.KeySearch.CallPre`, which only this module used -/

section

/-! The selected backend's shared precondition at the actual ARM call boundary. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont VG.Spec.Ffdh

theorem call_pre_legacy {p : KeyPublic sampling} {used keys scalars : Nat} {s : State} {m : Mem}
    (notcached : sampling.cachedContext = false) (facts : CallFacts p used) (h : ArgumentContext p used keys scalars s)
    (sp : s.sp = callSp p) (mem : s.mem = callMem p used m (callSp p)) :
    (GenerationPolicy.attemptContract sampling abi 176).pre (plainCallState p used s) := by
  have size : sampling.argumentBytes = 32 := by simp only [GenerationPolicy.argumentBytes, notcached, Bool.false_eq_true, ite_false]
  have plain : callRdPlain p used = [rDomain p, rTape p used, rCallArgs p] := by simp [callRdPlain, contextRegions, notcached]
  have selected : sampling.attemptContract abi 176 = sampling.legacyAttemptContract abi 176 := by cases sampling <;> simp_all only [GenerationPolicy.cachedContext, Bool.true_eq_false] <;> rfl
  have a0 := call_stackArg (j := 0) facts sp mem (by cases sampling <;> decide)
  have a1 := call_stackArg (j := 1) facts sp mem (by cases sampling <;> decide)
  have a2 := call_stackArg (j := 2) facts sp mem (by cases sampling <;> decide)
  have a3 := call_stackArg (j := 3) facts sp mem (by cases sampling <;> decide)
  have a4 := call_stackArg (j := 4) facts sp mem (by cases sampling <;> decide)
  have a5 := call_stackArg (j := 5) facts sp mem (by cases sampling <;> decide)
  have a6 := call_stackArg (j := 6) facts sp mem (by cases sampling <;> decide)
  change stackArg (plainCallState p used s) 0 = callValue p used 0 at a0
  change stackArg (plainCallState p used s) 1 = callValue p used 1 at a1
  change stackArg (plainCallState p used s) 2 = callValue p used 2 at a2
  change stackArg (plainCallState p used s) 3 = callValue p used 3 at a3
  change stackArg (plainCallState p used s) 4 = callValue p used 4 at a4
  change stackArg (plainCallState p used s) 5 = callValue p used 5 at a5
  change stackArg (plainCallState p used s) 6 = callValue p used 6 at a6
  simp only [callValue] at a0 a1 a2 a3 a4 a5 a6
  have argAddr : stackArgAddr (plainCallState p used s) 0 = State.addr (callSp p) := by
    simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
    exact congrArg State.addr sp
  have nativeLen : (BitVec.ofNat 32 p.len).toNat = p.len :=
    Nat.mod_eq_of_lt facts.lenFits
  have domainLen : (BitVec.ofNat 32 p.dlen).toNat = p.dlen :=
    Nat.mod_eq_of_lt facts.domainLenFits
  have capacity : (BitVec.ofNat 32 p.capacity).toNat = p.capacity :=
    Nat.mod_eq_of_lt facts.capacityFits
  rw [selected]
  sig_pre [GenerationPolicy.legacyAttemptContract, generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  simp only [h.x, h.xlen, h.y, h.ylen,
    a0, a1, a2, a3, a4, a5, a6, nativeLen, domainLen, capacity, argAddr, sp, plain]
  have stack (r : Region) (member : r ∈ [rX p, rY p, rDomain p, rTape p used, rScratch p, rCallArgs p]) :
      (⟨State.addr (callSp p) - 176#64, 176⟩ : Region).Disjoint r := by
    rw [← FrameStack.addr_sub' facts.stackFits]
    exact facts.stack r member
  have xa : (rX p).Disjoint ⟨State.addr (callSp p), 28⟩ := by simpa only [rCallArgs, size, Nat.reduceSub] using facts.xa
  have ya : (rY p).Disjoint ⟨State.addr (callSp p), 28⟩ := by simpa only [rCallArgs, size, Nat.reduceSub] using facts.ya
  have sa : (rScratch p).Disjoint ⟨State.addr (callSp p), 28⟩ := by simpa only [rCallArgs, size, Nat.reduceSub] using facts.sa
  refine ⟨facts.stackFits, ?_, ?_, ?_, facts.xy, facts.xd, facts.xr, facts.xs, xa,
    facts.yd, facts.yr, facts.ys, ya, facts.ds, facts.rs, sa,
    stack (rX p) (by simp), stack (rY p) (by simp), stack (rDomain p) (by simp),
    stack (rTape p used) (by simp), stack (rScratch p) (by simp), ?_, facts.xFit, facts.yFit, facts.domainFit, facts.tapeFit,
    facts.scratchFit, facts.length, facts.domainLength, trivial, trivial, trivial, facts.scratch⟩
  · have argsFit := facts.argsFit; simp only [GenerationPolicy.argumentBytes, notcached, Bool.false_eq_true, ite_false, Nat.reduceSub] at argsFit; omega_using [argsFit]
  · simp only [rCallArgs, size, Nat.reduceSub]; rfl
  · rfl
  · simpa only [rCallArgs, size, Nat.reduceSub, State.addr] using stack (rCallArgs p) (by simp)


theorem call_pre_cached {p : KeyPublic .cached} {used keys scalars : Nat} {original v s : State}
    (live : KeyLive p original used keys scalars v) (room : used + p.len ≤ p.randLen)
    (h : ArgumentContext p used keys scalars s)
    (sp : s.sp = callSp p) (mem : s.mem = callMem p used v.mem (callSp p)) :
    (GenerationPolicy.attemptContract .cached abi 176).pre (plainCallState p used s) := by
  have facts := live.input.callFacts room
  have a0 := call_stackArg (j := 0) facts sp mem (by decide)
  have a1 := call_stackArg (j := 1) facts sp mem (by decide)
  have a2 := call_stackArg (j := 2) facts sp mem (by decide)
  have a3 := call_stackArg (j := 3) facts sp mem (by decide)
  have a4 := call_stackArg (j := 4) facts sp mem (by decide)
  have a5 := call_stackArg (j := 5) facts sp mem (by decide)
  have a6 := call_stackArg (j := 6) facts sp mem (by decide)
  have a7 := call_stackArg (j := 7) facts sp mem (by decide)
  have a8 := call_stackArg (j := 8) facts sp mem (by decide)
  change stackArg (plainCallState p used s) 0 = callValue p used 0 at a0
  change stackArg (plainCallState p used s) 1 = callValue p used 1 at a1
  change stackArg (plainCallState p used s) 2 = callValue p used 2 at a2
  change stackArg (plainCallState p used s) 3 = callValue p used 3 at a3
  change stackArg (plainCallState p used s) 4 = callValue p used 4 at a4
  change stackArg (plainCallState p used s) 5 = callValue p used 5 at a5
  change stackArg (plainCallState p used s) 6 = callValue p used 6 at a6
  change stackArg (plainCallState p used s) 7 = callValue p used 7 at a7
  change stackArg (plainCallState p used s) 8 = callValue p used 8 at a8
  simp only [callValue] at a0 a1 a2 a3 a4 a5 a6 a7 a8
  have argAddr : stackArgAddr (plainCallState p used s) 0 = State.addr (callSp p) := by
    simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
    exact congrArg State.addr sp
  have nativeLen : (BitVec.ofNat 32 p.len).toNat = p.len := Nat.mod_eq_of_lt facts.lenFits
  have domainLen : (BitVec.ofNat 32 p.dlen).toNat = p.dlen := Nat.mod_eq_of_lt facts.domainLenFits
  have capacity : (BitVec.ofNat 32 p.capacity).toNat = p.capacity := Nat.mod_eq_of_lt facts.capacityFits
  have ctxFit := live.input.context_fit rfl
  have ctxLen : (BitVec.ofNat 32 p.contextWords).toNat = p.contextWords := Nat.mod_eq_of_lt (by omega_using [ctxFit])
  have read : rContext p ∈ original.rd := by rw [live.input.read_regions]; simp [contextRegions, GenerationPolicy.cachedContext]
  have sep := live.input.call_read read
  have frame : Frame (callChanges p) v.mem s.mem := by
    rw [mem]; exact (callMem_frame _ _ _ _).mono (by simp [callChanges, rArguments])
  have held := live.cachedHeld.after_frame frame (by intro _; omega_using [ctxFit]) (by intro _; exact sep)
  have canonical := held rfl
  have dom := (live.input.call_domain_frame frame).trans live.domain
  have valid := live.input.bounds.domainValid
  have xy := facts.xy
  have xd := facts.xd
  have xr := facts.xr
  have xs := facts.xs
  have xa := facts.xa
  have yd := facts.yd
  have yr := facts.yr
  have ys := facts.ys
  have ya := facts.ya
  have ds := facts.ds
  have rs := facts.rs
  have sa := facts.sa
  have xc := (sep (rX p) (by simp [callChanges])).symm
  have yc := (sep (rY p) (by simp [callChanges])).symm
  have sc := (sep (rScratch p) (by simp [callChanges])).symm
  have cs := (sep (rCallStack p) (by simp [callChanges])).symm
  have sx := facts.stack (rX p) (by simp)
  have sy := facts.stack (rY p) (by simp)
  have sd := facts.stack (rDomain p) (by simp)
  have sr := facts.stack (rTape p used) (by simp)
  have ss := facts.stack (rScratch p) (by simp)
  have saa := facts.stack (rCallArgs p) (by simp)
  have stackFit := facts.stackFits
  have argFit := facts.argsFit
  have xFit := facts.xFit
  have yFit := facts.yFit
  have dFit := facts.domainFit
  have rFit := facts.tapeFit
  have sFit := facts.scratchFit
  have length := facts.length
  have domainLength := facts.domainLength
  have scratch := facts.scratch
  sig_pre [GenerationPolicy.attemptContract, Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig,
    generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr]
  simp only [h.x, h.xlen, h.y, h.ylen, a0, a1, a2, a3, a4, a5, a6, a7, a8,
    nativeLen, domainLen, capacity, ctxLen, argAddr, sp]
  simp only [rX, rY, rDomain, rTape, rScratch, rCallArgs, rContext, rCallStack,
    GenerationPolicy.argumentBytes, GenerationPolicy.cachedContext, ite_true, Nat.reduceSub,
    FrameStack.belowA, State.addr,
    callRdPlain, callWr, contextRegions, List.cons_append, List.nil_append] at *
  have subAddr := FrameStack.addr_sub' stackFit
  simp only [State.addr] at subAddr
  rw [subAddr] at cs sx sy sd sr ss saa
  simp only [Nat.mul_comm] at *
  simp only [dom]
  sig_and_intros
  sig_close
  all_goals exact True.intro

 theorem call_pre_plain {p : KeyPublic sampling} {used keys scalars : Nat} {original v s : State}
    (live : KeyLive p original used keys scalars v) (room : used + p.len ≤ p.randLen)
    (h : ArgumentContext p used keys scalars s)
    (sp : s.sp = callSp p) (mem : s.mem = callMem p used v.mem (callSp p)) :
    (GenerationPolicy.attemptContract sampling abi 176).pre (plainCallState p used s) := by
  cases sampling with
  | full => exact call_pre_legacy rfl (live.input.callFacts room) h sp mem
  | vetted => exact call_pre_legacy rfl (live.input.callFacts room) h sp mem
  | cached => exact call_pre_cached live room h sp mem

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! ### `Ffdh.Arm.KeySearch.CallConsts`, which this module and modules that import it used -/

section

/-! The nested attempt receives the policy's preserved public constant tables. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}
open VG VG.Arm VG.Proof.Mont

 theorem strip_call {p : KeyPublic sampling} {used : Nat} {u : State} :
    stripConsts (KeyConstants.consts sampling) (callState p used u) = plainCallState p used u := by
  cases sampling <;> rfl

 theorem call_consts {p : KeyPublic sampling} {original s u : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s)
    (mem : u.mem = callMem p used s.mem (callSp p)) (sp : u.sp = callSp p) (syms : u.syms = s.syms) :
    ConstsOk (KeyConstants.consts sampling) 176 (callState p used u) := by
  have pointer : KeyConstants.tablePtr sampling (callState p used u) = p.tablePtr :=
    (KeyConstants.tablePtr_of_syms (sampling := sampling) syms).trans h.tablePtr
  have regions : constRegs (KeyConstants.consts sampling) (callState p used u) =
      KeyConstants.regions sampling p.tablePtr := by
    rw [KeyConstants.regions_eq, pointer]
  have frame : Frame [rArguments p] s.mem u.mem := by rw [mem]; exact callMem_frame _ _ _ _
  have held := KeyConstants.held_after_frame h.held frame (by
    intro table member r hr
    obtain rfl := List.mem_singleton.mp hr
    exact (h.input.constants_stack table member).sub_right (arguments_sub h.input.bounds.stackFits))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [regions]
    cases sampling <;> rfl
  · intro c member i hi
    have word := held c member i hi
    cases sampling with
    | full | cached => exact False.elim (List.not_mem_nil member)
    | vetted =>
      simp only [KeyConstants.consts, VG.Impl.Ffdh.Arm.VettedGroups.tableConsts, List.mem_singleton] at member
      subst c
      change u.mem.readW (State.addr (u.syms VG.Impl.Ffdh.Arm.VettedGroups.tableSym) + BitVec.ofNat 64 (8 * i)) 64 = _
      change u.syms VG.Impl.Ffdh.Arm.VettedGroups.tableSym = p.tablePtr at pointer
      rw [pointer]
      exact word
  · intro table member
    rw [regions] at member
    have initial : ConstsOk (KeyConstants.consts sampling) (stackUse sampling) original := h.input.2.2
    have originalMember : table ∈ constRegs (KeyConstants.consts sampling) original := by
      rw [h.input.constant_regions]; exact member
    have facts := initial.2.2.1 table originalMember
    refine ⟨facts.1, ?_, ?_⟩
    · intro r hr
      have changes : r ∈ callChanges p := by
        change r ∈ callWr p at hr
        simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [callChanges]
      exact h.input.call_read (h.input.constants_read member) r changes
    · intro r hr
      change r ∈ stackBelow (State.addr u.sp) 176 at hr
      simp only [stackBelow, List.mem_singleton] at hr
      subst r
      rw [sp]
      have fit : 176 ≤ (callSp p).toNat := by
        have enough := h.input.bounds.stackFits
        change 24 + sampling.argumentBytes + 176 ≤ p.sp.toNat at enough
        rw [callSp, FrameStack.sub_toNat' (by omega_using [enough] : 24 + sampling.argumentBytes ≤ p.sp.toNat)]
        omega_using [enough]
      rw [← FrameStack.addr_sub' fit]
      exact (h.input.constants_stack table member).sub_right (callStack_sub h.input.bounds.stackFits)
  · intro table member
    rw [regions] at member
    have initial : ConstsOk (KeyConstants.consts sampling) (stackUse sampling) original := h.input.2.2
    have originalMember : table ∈ constRegs (KeyConstants.consts sampling) original := by
      rw [h.input.constant_regions]; exact member
    exact initial.2.2.2 table originalMember

 theorem call_pre {p : KeyPublic sampling} {used keys scalars : Nat} {original s u : State}
    (live : KeyLive p original used keys scalars s) (room : used + p.len ≤ p.randLen)
    (args : ArgumentContext p used keys scalars u) (sp : u.sp = callSp p)
    (mem : u.mem = callMem p used s.mem (callSp p)) (syms : u.syms = s.syms) :
    (GenerationPolicy.attemptContract sampling (KeyConstants.abi sampling) 176).pre (callState p used u) := by
  apply selected_attempt_pre.mpr
  rw [strip_call]
  exact ⟨call_pre_plain live room args sp mem, call_consts live mem sp syms⟩

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! ### `Ffdh.Arm.KeySearch.CallPost`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.KeySearch.CallRegions`, which this module and modules that import it used -/

section

/-! The selected attempt can narrow permissions to its buffers and arguments;
its stack writes remain below the controller's saved registers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont

namespace KeyLive
variable {p : KeyPublic sampling} {original s : State} {used keys scalars : Nat}

theorem covers_writes (h : KeyLive p original used keys scalars s) {u : State}
    (wr : u.wr = (allocated sampling.argumentBytes s).wr) : Covers (callWr p) u.wr := by
  apply Covers.of_mem
  intro r hr
  rw [wr]
  apply List.mem_cons_of_mem
  rw [h.wr, h.input.write_regions]
  simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp

theorem covers_reads (h : KeyLive p original used keys scalars s) (room : used + p.len ≤ p.randLen)
    {u : State} (rd : u.rd = (allocated sampling.argumentBytes s).rd) (wr : u.wr = (allocated sampling.argumentBytes s).wr) :
    Covers (callRd p used ++ callWr p) (u.rd ++ u.wr) := by
  refine Covers.append_left ?_ (h.covers_writes wr).right
  apply Covers.of_sub
  intro r hr
  simp only [callRd, callRdPlain, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (((rfl | rfl) | context) | args) | constant
  · refine ⟨rDomain p, ?_, 0, by rw [BitVec.add_zero], by omega_using []⟩
    rw [rd]
    apply List.mem_append_left
    change rDomain p ∈ s.rd
    rw [h.rd, h.input.read_regions]
    simp
  · refine ⟨rRandom p, ?_, used, h.input.tape_addr room, room⟩
    rw [rd]
    apply List.mem_append_left
    change rRandom p ∈ s.rd
    rw [h.rd, h.input.read_regions]
    simp
  · refine ⟨r, ?_, 0, by rw [BitVec.add_zero], by omega_using []⟩
    rw [rd]
    apply List.mem_append_left
    change r ∈ s.rd
    rw [h.rd, h.input.read_regions]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inl (Or.inl (Or.inr context))
  · obtain rfl := args
    refine ⟨rArguments p, ?_, 0, by rw [BitVec.add_zero], by change 0 + (sampling.argumentBytes - 4) ≤ sampling.argumentBytes; omega_using []⟩
    rw [wr]
    apply List.mem_append_right
    change rArguments p ∈ ⟨State.addr (allocated sampling.argumentBytes s).sp, sampling.argumentBytes⟩ :: s.wr
    rw [h.call_sp]
    exact List.mem_cons_self
  · refine ⟨r, ?_, 0, by rw [BitVec.add_zero], by omega_using []⟩
    rw [rd]
    apply List.mem_append_left
    change r ∈ s.rd
    rw [h.rd]
    exact h.input.constants_read constant

theorem argument_frame (_h : KeyLive p original used keys scalars s) {u : State}
    (mem : u.mem = callMem p used s.mem (callSp p)) : Frame (callChanges p) s.mem u.mem := by
  rw [mem]
  exact (callMem_frame _ _ _ _).mono (by simp [callChanges, rArguments])

theorem attempt_frame (h : KeyLive p original used keys scalars s) {u t : State} {depth : Nat}
    (mem : u.mem = callMem p used s.mem (callSp p)) (sp : u.sp = callSp p)
    (frame : Frame (callWr p ++ [FrameStack.belowA u.sp depth]) u.mem t.mem) (limit : depth ≤ 176) :
    Frame (callChanges p) s.mem t.mem := by
  apply (h.argument_frame mem).trans
  apply frame.sub
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact ⟨r, by simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
                 rcases hr with rfl | rfl | rfl <;> simp [callChanges], fun _ hi => hi⟩
  · obtain rfl := List.mem_singleton.mp hr
    refine ⟨rCallStack p, by simp [callChanges], ?_⟩
    rw [sp]
    apply FrameStack.belowA_sub limit
    have fit := h.input.bounds.stackFits
    change 24 + sampling.argumentBytes + 176 ≤ p.sp.toNat at fit
    change 176 ≤ (p.sp - BitVec.ofNat 32 (24 + sampling.argumentBytes)).toNat
    rw [FrameStack.sub_toNat' (by omega_using [fit] : 24 + sampling.argumentBytes ≤ p.sp.toNat)]
    omega_using [fit]


end KeyLive
end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! The shared key-attempt result is exactly the controller's current
attempt status and key pair, independent of its temporary call frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont VG.Spec.Ffdh

theorem KeyLive.call_inputs {p : KeyPublic sampling} {original s u : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (room : used + p.len ≤ p.randLen)
    (mem : u.mem = callMem p used s.mem (callSp p)) :
    Spec.Rsa.bytesAt u.mem (State.addr p.dp) p.dlen = p.dom ∧
      Spec.Rsa.bytesAt u.mem (State.addr (p.rp + BitVec.ofNat 32 used)) p.len =
        ((keyRand p original).drop used).take p.len := by
  have frame := h.argument_frame mem
  refine ⟨(h.input.call_domain_frame frame).trans h.domain, ?_⟩
  have slice : ((Spec.Rsa.bytesAt u.mem (State.addr p.rp) p.randLen).drop used).take p.len =
      Spec.Rsa.bytesAt u.mem (off (State.addr p.rp) used) p.len :=
    VG.Proof.MlKem.bytesAt_slice u.mem (State.addr p.rp) room
  rw [h.input.tape_addr room, ← slice, h.input.call_random_frame frame, h.random]
  rfl

theorem call_post {p : KeyPublic sampling} {original s u t : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (room : used + p.len ≤ p.randLen)
    (args : ArgumentContext p used keys scalars u) (sp : u.sp = callSp p)
    (mem : u.mem = callMem p used s.mem (callSp p))
    (post : (GenerationPolicy.attemptContract sampling abi 176).post (callState p used u)
      (t.withRegions (callRd p used) (callWr p))) : AttemptPost p original used t := by
  have facts := h.input.callFacts room
  have a0 := call_stackArg (j := 0) facts sp mem (by cases sampling <;> decide)
  have a1 := call_stackArg (j := 1) facts sp mem (by cases sampling <;> decide)
  have a2 := call_stackArg (j := 2) facts sp mem (by cases sampling <;> decide)
  have a3 := call_stackArg (j := 3) facts sp mem (by cases sampling <;> decide)
  have a4 := call_stackArg (j := 4) facts sp mem (by cases sampling <;> decide)
  simp only [callValue] at a0 a1 a2 a3 a4
  have nativeLen : (BitVec.ofNat 32 p.len).toNat = p.len := Nat.mod_eq_of_lt facts.lenFits
  have domainLen : (BitVec.ofNat 32 p.dlen).toNat = p.dlen := Nat.mod_eq_of_lt facts.domainLenFits
  have bytes := h.call_inputs room mem
  cases sampling <;>
    sig_post [GenerationPolicy.attemptContract, GenerationPolicy.legacyAttemptContract,
      Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, generateKeySig, abi, argRegs,
      reduceClassify, Loc.val, State.addr] at post
  all_goals
    rw [BitVec.setWidth_append_eq_right] at post
    simp only [args.x, args.y, a0, a1, a2, a3, a4, nativeLen, domainLen] at post
    simp only [State.addr] at bytes
    rw [bytes.1, bytes.2] at post
    first
    | exact ⟨(post h.input.bounds.domainValid).1, (post h.input.bounds.domainValid).2⟩
    | exact ⟨post.1, post.2⟩

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! Calling any verified FFDH backend from the native key-search controller. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

theorem attemptRun_ok (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) : AttemptRunOk backend := by
  intro p original s used keys scalars h room
  have facts := h.input.callFacts room
  have rootFit : stackUse sampling ≤ p.sp.toNat := h.input.bounds.stackFits
  change 24 + sampling.argumentBytes + 176 ≤ p.sp.toNat at rootFit
  have outerFit : sampling.argumentBytes ≤ s.sp.toNat := by
    rw [h.sp, FrameStack.sub_toNat' (by omega_using [rootFit] : 24 ≤ p.sp.toNat)]
    omega_using [rootFit]
  have allocatedFit : (allocated sampling.argumentBytes s).sp.toNat + sampling.argumentBytes ≤ 2 ^ 32 := by
    change (s.sp - BitVec.ofNat 32 sampling.argumentBytes).toNat + sampling.argumentBytes ≤ 2 ^ 32
    rw [FrameStack.sub_toNat' outerFit]
    have := s.sp.isLt
    omega_using [rootFit]
  have control : Controller p.control (allocated sampling.argumentBytes s) :=
    ⟨h.input.control_space (fun _ hr => List.mem_cons_of_mem _ (by rw [h.wr]; exact List.mem_cons_of_mem _ hr)),
      h.pointer⟩
  have stack : Workspace (allocated sampling.argumentBytes s) (allocated sampling.argumentBytes s).sp sampling.argumentBytes :=
    ⟨allocatedFit, List.mem_cons_self⟩
  have separate : (rControl p).Disjoint ⟨State.addr (allocated sampling.argumentBytes s).sp, sampling.argumentBytes⟩ := by
    rw [h.call_sp]
    exact ((h.input.stack_separate (r := rControl p) (by rw [h.input.write_regions]; simp)).sub_left
      (arguments_sub h.input.bounds.stackFits)).symm
  unfold VG.Impl.Ffdh.Arm.KeySearch.attemptRunFor
  change WP isa (.frame (.alloc sampling.argumentBytes) (.seq (.block (VG.Impl.Ffdh.Arm.KeySearch.argumentsFor sampling.cachedContext)) (.call backend.keyName backend.generateKey)) (.free sampling.argumentBytes)) s _
  refine WP.alloc (by cases sampling <;> decide) outerFit ?_
  rw [WP.seq_iff]
  refine WP.mono_syms (arguments_ok (allocated sampling.argumentBytes s) control stack separate h.headers h.cachedSlots) ?_
  rintro u ⟨⟨args, mem⟩, rest⟩ symsU
  have spU : u.sp = callSp p := rest.sp.trans h.call_sp
  have memU : u.mem = callMem p used s.mem (callSp p) := by
    rw [mem, h.call_sp]
    rfl
  apply WP.of_syms
  refine FrameStack.WP.callF backend.generateKey_verified.1 (call_pre h room args spU memU symsU)
    (h.covers_reads room rest.rd rest.wr) (h.covers_writes rest.wr)
    (by rw [spU]; exact Nat.le_trans backend.keyStack facts.stackFits) ?_
  intro t rd wr sp frame kept post symsT m₀ u₀ hfl
  change Frame [⟨State.addr (allocated sampling.argumentBytes s).sp, sampling.argumentBytes⟩] t.mem m₀ at hfl
  rw [h.call_sp] at hfl
  have argSep : ∀ r ∈ [rX p, rY p], r.Disjoint (rArguments p) := by
    intro r hr
    have hw : r ∈ original.wr ++ original.rd := by
      rw [h.input.write_regions]; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
    exact ((h.input.stack_separate hw).sub_left (arguments_sub h.input.bounds.stackFits)).symm
  have fitLen : p.len ≤ 2 ^ 64 := by have := h.input.bounds.maxLength; omega_using [this]
  have xeq : Spec.Rsa.bytesAt m₀ (State.addr p.xp) p.len = Spec.Rsa.bytesAt t.mem (State.addr p.xp) p.len :=
    bytesAt_frame (r := rX p) hfl (by simpa using argSep _ (by simp)) fitLen
  have yeq : Spec.Rsa.bytesAt m₀ (State.addr p.yp) p.len = Spec.Rsa.bytesAt t.mem (State.addr p.yp) p.len :=
    bytesAt_frame (r := rY p) hfl (by simpa using argSep _ (by simp)) fitLen
  refine ⟨h.restore ?_ ?_ ?_ ?_ (symsT.trans symsU) ((h.attempt_frame memU spU frame backend.keyStack).trans
    (hfl.sub fun r hr => ⟨rArguments p, by simp only [List.mem_singleton] at hr; subst hr; simp [callChanges],
      by simp only [List.mem_singleton] at hr; subst hr; exact fun _ hc => hc⟩)), ?_⟩
  · exact rd.trans rest.rd
  · change t.wr.tail = s.wr
    rw [wr, rest.wr]
    rfl
  · change t.sp + BitVec.ofNat 32 sampling.argumentBytes = s.sp
    rw [sp, rest.sp]
    exact BitVec.sub_add_cancel _ _
  · intro r hr
    change t.gpr r = s.gpr r
    rw [kept r (by revert r hr; decide) (by revert r hr; decide)]
    exact rest.gpr r (by revert r hr; decide)
  · have result := call_post h room args spU memU (selected_attempt_post.mp post)
    have out := result.output
    rw [← xeq, ← yeq] at out
    exact ⟨result.status, out⟩

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! ### `Ffdh.Arm.KeySearch.CallPublic`, which only this module used -/

section

/-! At equal public search positions, the selected attempt sees equal
public arguments, domain bytes, and its disclosed attempt status. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Spec.Ffdh

theorem call_public_plain {p : KeyPublic sampling} {used keys scalars : Nat} {s₁ s₂ original₁ original₂ u₁ u₂ : State}
    (live₁ : KeyLive p original₁ used keys scalars s₁) (live₂ : KeyLive p original₂ used keys scalars s₂)
    (room : used + p.len ≤ p.randLen)
    (args₁ : ArgumentContext p used keys scalars u₁) (args₂ : ArgumentContext p used keys scalars u₂)
    (sp₁ : u₁.sp = callSp p) (sp₂ : u₂.sp = callSp p)
    (mem₁ : u₁.mem = callMem p used s₁.mem (callSp p)) (mem₂ : u₂.mem = callMem p used s₂.mem (callSp p))
    (status : currentStatus p original₁ used = currentStatus p original₂ used) :
    (GenerationPolicy.attemptContract sampling abi 176).pub (callState p used u₁) (callState p used u₂) := by
  have facts := live₁.input.callFacts room
  have a0₁ := call_stackArg (j := 0) facts sp₁ mem₁ (by cases sampling <;> decide)
  have a1₁ := call_stackArg (j := 1) facts sp₁ mem₁ (by cases sampling <;> decide)
  have a2₁ := call_stackArg (j := 2) facts sp₁ mem₁ (by cases sampling <;> decide)
  have a3₁ := call_stackArg (j := 3) facts sp₁ mem₁ (by cases sampling <;> decide)
  have a4₁ := call_stackArg (j := 4) facts sp₁ mem₁ (by cases sampling <;> decide)
  have a5₁ := call_stackArg (j := 5) facts sp₁ mem₁ (by cases sampling <;> decide)
  have a6₁ := call_stackArg (j := 6) facts sp₁ mem₁ (by cases sampling <;> decide)
  have a0₂ := call_stackArg (j := 0) facts sp₂ mem₂ (by cases sampling <;> decide)
  have a1₂ := call_stackArg (j := 1) facts sp₂ mem₂ (by cases sampling <;> decide)
  have a2₂ := call_stackArg (j := 2) facts sp₂ mem₂ (by cases sampling <;> decide)
  have a3₂ := call_stackArg (j := 3) facts sp₂ mem₂ (by cases sampling <;> decide)
  have a4₂ := call_stackArg (j := 4) facts sp₂ mem₂ (by cases sampling <;> decide)
  have a5₂ := call_stackArg (j := 5) facts sp₂ mem₂ (by cases sampling <;> decide)
  have a6₂ := call_stackArg (j := 6) facts sp₂ mem₂ (by cases sampling <;> decide)
  simp only [callValue] at a0₁ a1₁ a2₁ a3₁ a4₁ a5₁ a6₁ a0₂ a1₂ a2₂ a3₂ a4₂ a5₂ a6₂
  have len : (BitVec.ofNat 32 p.len).toNat = p.len := Nat.mod_eq_of_lt facts.lenFits
  have dlen : (BitVec.ofNat 32 p.dlen).toNat = p.dlen := Nat.mod_eq_of_lt facts.domainLenFits
  have inputs₁ := live₁.call_inputs room mem₁
  have inputs₂ := live₂.call_inputs room mem₂
  simp only [State.addr] at inputs₁ inputs₂
  cases sampling with
  | full =>
    sig_pub [GenerationPolicy.attemptContract, GenerationPolicy.legacyAttemptContract, Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr]
    simp only [args₁.x, args₁.xlen, args₁.y, args₁.ylen, args₂.x, args₂.xlen, args₂.y, args₂.ylen,
      a0₁, a1₁, a2₁, a3₁, a4₁, a5₁, a6₁, a0₂, a1₂, a2₂, a3₂, a4₂, a5₂, a6₂, sp₁, sp₂, len, dlen]
    rw [inputs₁.1, inputs₁.2, inputs₂.1, inputs₂.2]
    change True ∧ (p.dom.map BitVec.toNat ++ [currentStatus p original₁ used] =
      p.dom.map BitVec.toNat ++ [currentStatus p original₂ used]) ∧ _
    rw [status]
    simp only [true_and]
  | vetted =>
    sig_pub [GenerationPolicy.attemptContract, GenerationPolicy.legacyAttemptContract, Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr]
    simp only [args₁.x, args₁.xlen, args₁.y, args₁.ylen, args₂.x, args₂.xlen, args₂.y, args₂.ylen,
      a0₁, a1₁, a2₁, a3₁, a4₁, a5₁, a6₁, a0₂, a1₂, a2₂, a3₂, a4₂, a5₂, a6₂, sp₁, sp₂, len, dlen]
    rw [inputs₁.1, inputs₁.2, inputs₂.1, inputs₂.2]
    change True ∧ (p.dom.map BitVec.toNat ++ [currentStatus p original₁ used] =
      p.dom.map BitVec.toNat ++ [currentStatus p original₂ used]) ∧ _
    rw [status]
    simp only [true_and]
  | cached =>
    have a7₁ := call_stackArg (j := 7) facts sp₁ mem₁ (by decide)
    have a7₂ := call_stackArg (j := 7) facts sp₂ mem₂ (by decide)
    have a8₁ := call_stackArg (j := 8) facts sp₁ mem₁ (by decide)
    have a8₂ := call_stackArg (j := 8) facts sp₂ mem₂ (by decide)
    simp only [callValue] at a7₁ a8₁ a7₂ a8₂
    sig_pub [GenerationPolicy.attemptContract, GenerationPolicy.legacyAttemptContract, Proof.Ffdh.cachedGenerateKeyContract, Proof.Ffdh.cachedGenerateKeySig, generateKeySig, abi, argRegs, reduceClassify, Loc.val, State.addr]
    simp only [args₁.x, args₁.xlen, args₁.y, args₁.ylen, args₂.x, args₂.xlen, args₂.y, args₂.ylen,
      a0₁, a1₁, a2₁, a3₁, a4₁, a5₁, a6₁, a0₂, a1₂, a2₂, a3₂, a4₂, a5₂, a6₂, a7₁, a8₁, a7₂, a8₂, sp₁, sp₂, len, dlen]
    rw [inputs₁.1, inputs₁.2, inputs₂.1, inputs₂.2]
    change True ∧ (p.dom.map BitVec.toNat ++ [currentStatus p original₁ used] =
      p.dom.map BitVec.toNat ++ [currentStatus p original₂ used]) ∧ _
    rw [status]
    simp only [true_and]

theorem call_public {p : KeyPublic sampling} {used keys scalars : Nat}
    {s₁ s₂ original₁ original₂ u₁ u₂ : State}
    (live₁ : KeyLive p original₁ used keys scalars s₁) (live₂ : KeyLive p original₂ used keys scalars s₂)
    (room : used + p.len ≤ p.randLen)
    (args₁ : ArgumentContext p used keys scalars u₁) (args₂ : ArgumentContext p used keys scalars u₂)
    (sp₁ : u₁.sp = callSp p) (sp₂ : u₂.sp = callSp p)
    (mem₁ : u₁.mem = callMem p used s₁.mem (callSp p)) (mem₂ : u₂.mem = callMem p used s₂.mem (callSp p))
    (syms₁ : u₁.syms = s₁.syms) (syms₂ : u₂.syms = s₂.syms)
    (status : currentStatus p original₁ used = currentStatus p original₂ used) :
    (GenerationPolicy.attemptContract sampling (KeyConstants.abi sampling) 176).pub
      (callState p used u₁) (callState p used u₂) := by
  apply selected_attempt_pub.mpr
  refine ⟨call_public_plain live₁ live₂ room args₁ args₂ sp₁ sp₂ mem₁ mem₂ status, ?_⟩
  have ptr₁ := (KeyConstants.tablePtr_of_syms (sampling := sampling) syms₁).trans live₁.tablePtr
  have ptr₂ := (KeyConstants.tablePtr_of_syms (sampling := sampling) syms₂).trans live₂.tablePtr
  change KeyConstants.tablePtr sampling u₁ = KeyConstants.tablePtr sampling u₂
  exact ptr₁.trans ptr₂.symm


end VG.Proof.Ffdh.Arm.KeySearch

end

end


/-! A native key attempt leaks only its public domain and the disclosed
status at the current search point, for every arithmetic backend. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm

private theorem call_ready {q : KeyPoint sampling} {u : State} (h : KeyCallCT q u) :
    (GenerationPolicy.attemptContract sampling (KeyConstants.abi sampling) 176).pre (callState q.inputs q.used u) ∧
      Covers (callRd q.inputs q.used ++ callWr q.inputs) (u.rd ++ u.wr) ∧ Covers (callWr q.inputs) u.wr := by
  obtain ⟨_, s, live, _, _, _, room, args, mem, rest, syms⟩ := h
  have sp := rest.sp.trans live.call_sp
  exact ⟨call_pre live room args sp mem syms,
    live.covers_reads room rest.rd rest.wr, live.covers_writes rest.wr⟩

private theorem call_pub {q : KeyPoint sampling} {u₁ u₂ : State} (h₁ : KeyCallCT q u₁) (h₂ : KeyCallCT q u₂) :
    (GenerationPolicy.attemptContract sampling (KeyConstants.abi sampling) 176).pub (callState q.inputs q.used u₁) (callState q.inputs q.used u₂) := by
  obtain ⟨_, _, live₁, statuses₁, keys₁, scalars₁, room₁, args₁, mem₁, rest₁, syms₁⟩ := h₁
  obtain ⟨_, _, live₂, statuses₂, keys₂, scalars₂, room₂, args₂, mem₂, rest₂, syms₂⟩ := h₂
  exact call_public live₁ live₂ room₁ args₁ args₂ (rest₁.sp.trans live₁.call_sp) (rest₂.sp.trans live₂.call_sp)
    mem₁ mem₂ syms₁ syms₂ ((attempt_status live₁ statuses₁ keys₁ scalars₁ room₁).trans
      (attempt_status live₂ statuses₂ keys₂ scalars₂ room₂).symm)

theorem attempt_call_ct (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) :
    RelCT isa (Two (KeyCallCT (sampling := sampling))) (.call backend.keyName backend.generateKey) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u v ⟨q, h₁, h₂, _⟩ e₁ e₂
  have ct : RelCT isa (fun s t => KeyCallCT q s ∧ KeyCallCT q t)
      (.call backend.keyName backend.generateKey) (fun _ _ => True) := by
    refine VG.Arm.RelCT.call backend.generateKey_verified.1 backend.generateKey_verified.2.1
      (callRd q.inputs q.used) (callWr q.inputs) ?_
    intro a b ⟨ha, hb⟩
    obtain ⟨pre₁, reads₁, writes₁⟩ := call_ready ha
    obtain ⟨pre₂, reads₂, writes₂⟩ := call_ready hb
    exact ⟨pre₁, pre₂, call_pub ha hb, reads₁, writes₁, reads₂, writes₂⟩
  exact ct _ _ _ _ _ _ ⟨h₁, h₂⟩ e₁ e₂

theorem attempt_run_ct (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) :
    RelCT isa (Two (KeyReady (sampling := sampling)))
      ((VG.Impl.Ffdh.Arm.KeySearch.attemptRunFor sampling.cachedContext) (.call backend.keyName backend.generateKey)) (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.KeySearch.attemptRunFor
  apply alloc_ct
  refine (RelCT.seq (two_post arguments_ct arguments_ready) (attempt_call_ct backend)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂, sp⟩, rfl, rfl⟩
  refine ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, ?_⟩
  change s.sp - BitVec.ofNat 32 (GenerationPolicy.argumentBytes sampling) = t.sp - BitVec.ofNat 32 (GenerationPolicy.argumentBytes sampling)
  rw [sp]

theorem attempt_ready (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) (q : KeyPoint sampling) (s : State) (h : KeyReady q s) :
    WP isa ((VG.Impl.Ffdh.Arm.KeySearch.attemptRunFor sampling.cachedContext) (.call backend.keyName backend.generateKey)) s (KeyAttempted q) := by
  obtain ⟨⟨original, live, statuses⟩, keys, scalars, room⟩ := h
  exact WP.mono (attemptRun_ok backend q.inputs original s q.used q.keys q.scalars live room)
    fun _ ⟨ready, post⟩ => ⟨original, ready, statuses, keys, scalars, room, post⟩

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! Native classification branches depend only on the disclosed attempt
status, with no additional dependence on the private scalar or public value. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm

theorem key_attempted_pins : Pins (KeyAttempted (sampling := sampling)) [.r4] := by
  intro q s t ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h₁.pointer.trans h₂.pointer.symm

def KeyGuard (k : Nat) (q : KeyPoint sampling) (s : State) : Prop :=
  KeyAny q.inputs s ∧ s.gpr .r9 = BitVec.ofNat 32 q.status ∧
    isa.eval .eq s = some (decide (q.status = k)) ∧ q.status < 4

private theorem first_ready (q : KeyPoint sampling) (s : State) (h : KeyAttempted q s) :
    WP isa (.block (VG.Impl.Ffdh.Arm.KeySearch.advance ++ ([.cmp .r9 (.imm 1)] : List Instr))) s (KeyGuard 1 q) := by
  obtain ⟨original, live, statuses, keys, scalars, room, post⟩ := h
  have disclosed := attempt_status live statuses keys scalars room
  have small : q.status < 4 := by
    rw [← disclosed]
    rcases currentStatus_cases q.inputs original q.used with eq | eq | eq <;> omega_using [eq]
  refine WP.mono (classify_head live room post) ?_
  rintro t ⟨ready, flag, value, _⟩
  refine ⟨⟨original, _, _, _, ready⟩, ?_, ?_, small⟩
  · rw [value, disclosed]
  · change some t.z = _
    rw [flag, disclosed]

private theorem next_ready (j k : Nat) (small : k < 4) (q : KeyPoint sampling) (s : State)
    (h : KeyGuard j q s ∧ isa.eval .eq s = some false) :
    WP isa (.block [.cmp .r9 (.imm (BitVec.ofNat 32 k))]) s (KeyGuard k q) := by
  obtain ⟨⟨⟨original, used, keys, scalars, live⟩, value, _, bound⟩, _⟩ := h
  refine WP.mono_syms (compareStatus_ok s bound small value) ?_
  rintro t ⟨⟨flag, mem⟩, rest⟩ syms
  refine ⟨⟨original, _, _, _, live.keep rest mem syms⟩, (rest.gpr .r9 (by simp)).trans value, ?_, bound⟩
  change some t.z = _
  rw [flag]

private theorem leaf {k : Nat} {b : Bool} {code : Prog isa}
    (ct : RelCT isa (Two (KeyAny (sampling := sampling))) code (fun _ _ => True)) :
    RelCT isa (Two fun (q : KeyPoint sampling) s => KeyGuard k q s ∧ isa.eval .eq s = some b) code (fun _ _ => True) :=
  ct.mono (fun _ _ ⟨q, h₁, h₂, sp⟩ => ⟨q.inputs, h₁.1.1, h₂.1.1, sp⟩) (fun _ _ h => h)

private theorem guard_eq (k : Nat) (q : KeyPoint sampling) (s t : State) (h₁ : KeyGuard k q s) (h₂ : KeyGuard k q t) :
    isa.eval .eq s = isa.eval .eq t := h₁.2.2.1.trans h₂.2.2.1.symm

private theorem no_pins {Φ : KeyPoint sampling → State → Prop} : Pins Φ [] := fun _ _ _ _ _ _ h => by cases h

theorem classify_ct : RelCT isa (Two (KeyAttempted (sampling := sampling))) VG.Impl.Ffdh.Arm.KeySearch.classify (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.KeySearch.classify
  refine RelCT.seq (two_piece [.r4] key_attempted_pins (by taint_decide) first_ready) ?_
  refine two_ite (guard_eq 1) (leaf accepted_ct) ?_
  refine RelCT.seq (two_post (two_taint [] no_pins (by taint_decide)) (next_ready 1 2 (by decide))) ?_
  refine two_ite (guard_eq 2) (leaf rejected_scalar_ct) ?_
  refine RelCT.seq (two_post (two_taint [] no_pins (by taint_decide)) (next_ready 2 3 (by decide))) ?_
  exact two_ite (guard_eq 3) (leaf rejected_public_ct) (leaf exhausted_ct)

end VG.Proof.Ffdh.Arm.KeySearch
