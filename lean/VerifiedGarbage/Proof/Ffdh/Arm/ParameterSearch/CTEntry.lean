module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Start
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTState
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTAddresses
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! Native entry reads fixed public stack positions and writes fixed controller fields. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post ControlAddress controlStore_ct entryCopy_ct)

def EntryPointer (p : SearchParams) (s : State) : Prop := s.gpr .r4 = p.control

private theorem entry_pointer (p : SearchParams) (s : State) (h : SearchStart p s) :
    WP isa (.block [.ldrSp .r4 44]) s (EntryPointer p) := by
  refine wp_load_incoming .r4 (h.incoming.incoming 5 (by decide)) (by decide)
    (fun t value _ _ => WP.block_nil ?_)
  simpa only [EntryPointer, incomingValue] using value

private def entryCopies : List (Nat × Nat) := [(24, 8), (28, 9), (32, 10), (36, 11), (40, 12)]

private theorem copies_ct (copies : List (Nat × Nat)) : RelCT isa ControlAddress
    (.block (copies.flatMap (fun e => [.ldrSp .r3 e.1, VG.Impl.Ffdh.Arm.ParameterSearch.stf .r3 e.2]))) ControlAddress := by
  induction copies with
  | nil => exact RelCT.block_nil (fun _ _ h => h)
  | cons e rest ih => exact RelCT.block_append ((entryCopy_ct e.1 e.2).seq ih)

private theorem entry_tail_ct : RelCT isa ControlAddress
    (.block (VG.Impl.Ffdh.Arm.ParameterSearch.entry.drop 1)) (fun _ _ => True) := by
  have stores : RelCT isa ControlAddress (.block [VG.Impl.Ffdh.Arm.ParameterSearch.stf .r0 5,
      VG.Impl.Ffdh.Arm.ParameterSearch.stf .r2 6, VG.Impl.Ffdh.Arm.ParameterSearch.stf .r3 7]) ControlAddress :=
    RelCT.block_append ((controlStore_ct .r0 40).seq
      (RelCT.block_append ((controlStore_ct .r2 48).seq (controlStore_ct .r3 56))))
  have zero : RelCT isa ControlAddress (.block [.mov .r3 (.imm 0), VG.Impl.Ffdh.Arm.ParameterSearch.stf .r3 4])
      (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r4]) _ (by taint_decide)
    intro s t h
    exact Taint.agree_ofRegs (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact h.1)
  change RelCT isa _ (.block (([VG.Impl.Ffdh.Arm.ParameterSearch.stf .r0 5,
    VG.Impl.Ffdh.Arm.ParameterSearch.stf .r2 6, VG.Impl.Ffdh.Arm.ParameterSearch.stf .r3 7] ++
    entryCopies.flatMap (fun e => [.ldrSp .r3 e.1, VG.Impl.Ffdh.Arm.ParameterSearch.stf .r3 e.2])) ++
    [.mov .r3 (.imm 0), VG.Impl.Ffdh.Arm.ParameterSearch.stf .r3 4])) _
  exact RelCT.block_append ((RelCT.block_append (stores.seq (copies_ct entryCopies))).seq zero)

theorem entry_ct : RelCT isa (Two SearchStart) (.block VG.Impl.Ffdh.Arm.ParameterSearch.entry) (fun _ _ => True) := by
  have load : RelCT isa (Two SearchStart) (.block [.ldrSp .r4 44]) (fun _ _ => True) :=
    (loadStack_ct .r4 44).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)
  change RelCT isa _ (.block ([.ldrSp .r4 44] ++ VG.Impl.Ffdh.Arm.ParameterSearch.entry.drop 1)) _
  refine RelCT.block_append (RelCT.seq (two_post load entry_pointer) ?_)
  exact entry_tail_ct.mono (fun _ _ ⟨_, hs, ht, sp⟩ => ⟨hs.trans ht.symm, sp⟩) (fun _ _ _ => trivial)

def initialPoint (p : SearchParams) : SearchPoint := ⟨p, 0, p.attempts⟩

theorem entry_ready (p : SearchParams) (s : State) (h : SearchStart p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterSearch.entry) s (LiveCT (initialPoint p)) :=
  WP.mono h.entry fun _ ⟨live, _⟩ => live

end VG.Proof.Ffdh.Arm.ParameterSearch
