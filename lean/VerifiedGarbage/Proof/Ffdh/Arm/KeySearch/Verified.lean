module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBackend

import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Public
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Sat
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Push
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTAddresses
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTLoop
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Correct
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTPoint
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.PushedArguments
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Start
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Call
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTFinish
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Loop
/-! Complete native ARMv7 key generation, including bounded retries and
entropy refills, satisfies the shared correctness and timing contract. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/KeySearch/CTEntry.lean`, which only this module imported.
section

/-! The native entry has public stack/control addresses, even though it
saves arbitrary incoming register values in the outer frame. -/

section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.GenerationSearch

def KeyStart (a : KeyPublic sampling × List Nat) (s : State) : Prop :=
  KeyInput a.1 s ∧ (searchResult a.1 s).statuses = a.2

def PushedStart (a : KeyPublic sampling × List Nat) (s : State) : Prop :=
  ∃ original, KeyStart a original ∧ s = searchPushed original

def EntryPointer (a : KeyPublic sampling × List Nat) (s : State) : Prop := s.gpr .r4 = a.1.control

private theorem entry_pointer (a : KeyPublic sampling × List Nat) (s : State) (h : PushedStart a s) :
    WP isa (.block [.ldrSp .r4 56]) s (EntryPointer a) := by
  obtain ⟨original, ⟨input, _⟩, rfl⟩ := h
  refine wp_load_incoming .r4 (input.pushed_arguments.incoming 8 (by cases sampling <;> decide)) (by decide)
    (fun t value _ _ => WP.block_nil ?_)
  simpa only [EntryPointer, incomingValue] using value

private def entryCopies : List (Nat × Nat) := [(24, 15), (28, 7), (32, 8), (40, 9), (44, 10), (48, 12), (52, 13)]

private theorem copies_ct (copies : List (Nat × Nat)) : RelCT isa ControlAddress
    (.block (copies.flatMap (fun e => [.ldrSp .r3 e.1, VG.Impl.Ffdh.Arm.KeySearch.stf .r3 e.2]))) ControlAddress := by
  induction copies with
  | nil => exact RelCT.block_nil (fun _ _ h => h)
  | cons e rest ih => exact RelCT.block_append ((entryCopy_ct e.1 e.2).seq ih)

private theorem entry_tail_ct : RelCT isa ControlAddress
    (.block (VG.Impl.Ffdh.Arm.KeySearch.entry.drop 1)) ControlAddress := by
  have stores : RelCT isa ControlAddress (.block [VG.Impl.Ffdh.Arm.KeySearch.stf .r0 5,
      VG.Impl.Ffdh.Arm.KeySearch.stf .r2 6]) ControlAddress :=
    RelCT.block_append ((controlStore_ct .r0 40).seq (controlStore_ct .r2 48))
  change RelCT isa _ (.block (([VG.Impl.Ffdh.Arm.KeySearch.stf .r0 5, VG.Impl.Ffdh.Arm.KeySearch.stf .r2 6] ++
    entryCopies.flatMap (fun e => [.ldrSp .r3 e.1, VG.Impl.Ffdh.Arm.KeySearch.stf .r3 e.2])) ++
      [.mov .r3 (.imm 0), VG.Impl.Ffdh.Arm.KeySearch.stf .r3 11])) _
  exact RelCT.block_append ((RelCT.block_append (stores.seq (copies_ct entryCopies))).seq entryZero_ct)

private theorem entry_plain_ct : RelCT isa (Two (PushedStart (sampling := sampling))) (.block VG.Impl.Ffdh.Arm.KeySearch.entry) ControlAddress := by
  have load : RelCT isa (Two (PushedStart (sampling := sampling))) (.block [.ldrSp .r4 56]) (fun _ _ => True) :=
    (loadStack_ct .r4 56).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)
  change RelCT isa _ (.block ([.ldrSp .r4 56] ++ VG.Impl.Ffdh.Arm.KeySearch.entry.drop 1)) _
  refine RelCT.block_append (RelCT.seq (two_post load entry_pointer) ?_)
  exact entry_tail_ct.mono (fun _ _ ⟨_, pointer₁, pointer₂, sp⟩ => ⟨pointer₁.trans pointer₂.symm, sp⟩)
    (fun _ _ h => h)

theorem entry_ct : RelCT isa (Two (PushedStart (sampling := sampling)))
    (.block (VG.Impl.Ffdh.Arm.KeySearch.entryFor sampling.cachedContext)) (fun _ _ => True) := by
  have cached : RelCT isa ControlAddress
      (.block [.ldrSp .r3 60,.str .r3 .r4 32,.ldrSp .r3 64,.str .r3 .r4 36]) ControlAddress :=
    RelCT.block_append ((RelCT.block_append ((controlLoad_ct .r3 60 (by decide)).seq
      (controlStore_ct .r3 32))).seq (RelCT.block_append ((controlLoad_ct .r3 64 (by decide)).seq
      (controlStore_ct .r3 36))))
  unfold VG.Impl.Ffdh.Arm.KeySearch.entryFor
  cases flag : sampling.cachedContext
  · simpa only [Bool.false_eq_true,ite_false,List.append_nil] using
      (entry_plain_ct (sampling:=sampling)).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  · exact (RelCT.block_append ((entry_plain_ct (sampling:=sampling)).seq cached)).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)

def initialPoint (a : KeyPublic sampling × List Nat) : KeyPoint sampling := ⟨a.1, 0, a.1.keys, a.1.scalars, a.2⟩
def Entered (a : KeyPublic sampling × List Nat) (s : State) : Prop := KeyCTL (initialPoint a) s

theorem entry_ready (a : KeyPublic sampling × List Nat) (s : State) (h : PushedStart a s) :
    WP isa (.block (VG.Impl.Ffdh.Arm.KeySearch.entryFor sampling.cachedContext)) s (Entered a) := by
  obtain ⟨original, ⟨input, statuses⟩, rfl⟩ := h
  refine WP.mono (start_ok input) ?_
  intro t live
  refine ⟨original, live, ?_⟩
  simpa only [initialPoint, KeyPublic.tail, keyTail, after, List.drop_zero, searchResult] using statuses

end VG.Proof.Ffdh.Arm.KeySearch
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/KeySearch/CTFunction.lean`, which only this module imported.
section

/-! Native entry, bounded key search, result stores, and saved-register
frame compose without timing dependence beyond the disclosed search sampling. -/

section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm

private theorem loop_ready (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) (a : KeyPublic sampling × List Nat) (s : State)
    (h : Entered a s) :
    WP isa (.loop ((VG.Impl.Ffdh.Arm.KeySearch.iterationFor sampling.cachedContext) (.call backend.keyName backend.generateKey)) .eq)
      s (KeyCTDone a.1) := by
  obtain ⟨original, live, _⟩ := h
  refine WP.mono (loop backend (attemptRun_ok backend)
    (expected := a.1.tail (keyRand a.1 original) 0 a.1.keys a.1.scalars)
    (n := 128 * a.1.keys + a.1.scalars + 1) ?_) (fun _ result => ⟨original, _, result⟩)
  exact ⟨0, a.1.keys, a.1.scalars, rfl, live, rfl, rfl⟩

theorem body_ct (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) : RelCT isa (Two (PushedStart (sampling := sampling)))
    (.seq (.block (VG.Impl.Ffdh.Arm.KeySearch.entryFor sampling.cachedContext))
      (.seq (.loop ((VG.Impl.Ffdh.Arm.KeySearch.iterationFor sampling.cachedContext) (.call backend.keyName backend.generateKey)) .eq)
        (.block VG.Impl.Ffdh.Arm.KeySearch.finish))) (fun _ _ => True) := by
  refine RelCT.seq (two_post entry_ct entry_ready) ?_
  have loopCT : RelCT isa (Two (Entered (sampling := sampling)))
      (.loop ((VG.Impl.Ffdh.Arm.KeySearch.iterationFor sampling.cachedContext) (.call backend.keyName backend.generateKey)) .eq) (fun _ _ => True) :=
    (loop_ct backend).mono (fun _ _ ⟨a, h₁, h₂, sp⟩ => ⟨initialPoint a, h₁, h₂, sp⟩) (fun _ _ h => h)
  refine RelCT.seq (two_post loopCT (loop_ready backend)) ?_
  exact finish_ct.mono (fun _ _ ⟨a, h₁, h₂, sp⟩ => ⟨a.1, h₁, h₂, sp⟩) (fun _ _ h => h)

private theorem push_search_eq {s t : State}
    (h : isa.push (.push [.r4, .r9, .r10, .r11, .r12, .lr]) s = some t) : t = searchPushed s := by
  simp only [isa, push] at h
  split at h <;> cases h
  rfl

theorem function_ct (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) : RelCT isa (Two (KeyStart (sampling := sampling)))
    ((VG.Impl.Ffdh.Arm.KeySearch.codeFor sampling.cachedContext) (.call backend.keyName backend.generateKey)) (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.KeySearch.codeFor
  refine RelCT.frame (fun _ _ ⟨_, _, _, sp⟩ => sp) ?_
  refine (body_ct backend).mono ?_ (fun _ _ h => h)
  rintro a b ⟨s, t, ⟨q, h₁, h₂, sp⟩, push₁, push₂⟩
  have first := push_search_eq push₁
  have second := push_search_eq push₂
  subst first second
  refine ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, ?_⟩
  change s.sp - 24#32 = t.sp - 24#32
  rw [sp]

end VG.Proof.Ffdh.Arm.KeySearch
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Spec.Ffdh

theorem constantTime (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) :
    ConstantTime isa (GenerationPolicy.searchContract sampling (KeyConstants.abi sampling) (stackUse sampling)).pre (GenerationPolicy.searchContract sampling (KeyConstants.abi sampling) (stackUse sampling)).pub
      (VG.Impl.Ffdh.Arm.KeySearch.codeFor sampling.cachedContext (.call backend.keyName backend.generateKey)) := by
  intro s t tr₁ tr₂ u v hs ht pub e₁ e₂
  obtain ⟨p, inputS, inputT, statuses, sp⟩ := public_inputs hs ht pub
  exact (function_ct backend _ _ _ _ _ _
    ⟨(p, (searchResult p s).statuses), ⟨inputS, rfl⟩, ⟨inputT, statuses.symm⟩, sp⟩ e₁ e₂).1

/-- The native controller registered for this attempt backend. -/
def calledCode (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) : Prog VG.Arm.isa :=
  VG.Impl.Ffdh.Arm.KeySearch.codeFor sampling.cachedContext
    (.call backend.keyName backend.generateKey)

theorem verified (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) :
    Verified target (VG.Impl.Ffdh.Arm.KeySearch.codeFor sampling.cachedContext (.call backend.keyName backend.generateKey))
      (GenerationPolicy.searchContract sampling (KeyConstants.abi sampling) (stackUse sampling)) :=
  ⟨correct backend, constantTime backend, sat⟩

end VG.Proof.Ffdh.Arm.KeySearch
