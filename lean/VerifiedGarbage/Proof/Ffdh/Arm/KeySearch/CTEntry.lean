module

public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Push
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTAddresses
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTLoop
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Correct
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTPoint
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.PushedArguments
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Start

/-! The native entry has public stack/control addresses, even though it
saves arbitrary incoming register values in the outer frame. -/

@[expose] public section
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
  refine wp_load_incoming .r4 (input.pushed_arguments.incoming 8 (by decide)) (by decide)
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

theorem entry_ct : RelCT isa (Two (PushedStart (sampling := sampling))) (.block VG.Impl.Ffdh.Arm.KeySearch.entry) (fun _ _ => True) := by
  have load : RelCT isa (Two (PushedStart (sampling := sampling))) (.block [.ldrSp .r4 56]) (fun _ _ => True) :=
    (loadStack_ct .r4 56).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)
  change RelCT isa _ (.block ([.ldrSp .r4 56] ++ VG.Impl.Ffdh.Arm.KeySearch.entry.drop 1)) _
  refine RelCT.block_append (RelCT.seq (two_post load entry_pointer) ?_)
  exact entry_tail_ct.mono (fun _ _ ⟨_, pointer₁, pointer₂, sp⟩ => ⟨pointer₁.trans pointer₂.symm, sp⟩)
    (fun _ _ _ => trivial)

def initialPoint (a : KeyPublic sampling × List Nat) : KeyPoint sampling := ⟨a.1, 0, a.1.keys, a.1.scalars, a.2⟩
def Entered (a : KeyPublic sampling × List Nat) (s : State) : Prop := KeyCTL (initialPoint a) s

theorem entry_ready (a : KeyPublic sampling × List Nat) (s : State) (h : PushedStart a s) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.entry) s (Entered a) := by
  obtain ⟨original, ⟨input, statuses⟩, rfl⟩ := h
  refine WP.mono (start_ok input) ?_
  intro t live
  refine ⟨original, live, ?_⟩
  simpa only [initialPoint, KeyPublic.tail, keyTail, after, List.drop_zero, searchResult] using statuses

end VG.Proof.Ffdh.Arm.KeySearch
