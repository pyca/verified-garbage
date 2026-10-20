module

public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingRows
import VerifiedGarbage.Proof.Mont.X86.Compact.TimingZero
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # The prepared product has a trace fixed by its public width and pointers -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Dsa.X86

def BasePair (g : Geometry) (s t : State) : Prop :=
  Pair g [.edi] s t ∧ PtrAt s g.W .edi g.S ∧ PtrAt t g.W .edi g.S

theorem scratchPointer_positioned_relCT {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g []) (.block Compact.scratchPtr) (BasePair g) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, P⟩ := scratchPointer_relCT v _ _ _ _ _ _ H E G
  have fit : 84 ≤ g.L := by have := v.lay.header; have := v.lay.scr; omega
  obtain ⟨Pu, _, _⟩ := wp_result (arrayPtr_ok H.1.ws H.1.args v.base (r := .edi) (j := 2) fit) E
  obtain ⟨Pz, _, _⟩ := wp_result (arrayPtr_ok H.2.1.ws H.2.1.args v.base (r := .edi) (j := 2) fit) G
  refine ⟨trace, P, ?_, ?_⟩
  · rw [PtrAt, Pu]; exact H.1.metadata.scratch
  · rw [PtrAt, Pz]; exact H.2.1.metadata.scratch

theorem accPointer_positioned_relCT {g : Geometry} (v : g.Valid) :
    RelCT isa (BasePair g) (.block Compact.accPtr) (WindowPair g (g.S + Compact.accOff)) := by
  have pos (s : State) : WP isa (.block Compact.accPtr) s fun t =>
      t.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 Compact.accOff ∧ Keeps [.ebp] s t := by
    unfold Compact.accPtr
    refine wp_movS rfl fun a A _ => wp_addS rfl fun t T _ => WP.block_nil ?_
    exact ⟨by rw [T.gpr, A.gpr], A.keeps.trans T.keeps⟩
  intro s t tr ur u z H E G
  obtain ⟨trace, P⟩ := accPointer_relCT v _ _ _ _ _ _ H.1 E G
  obtain ⟨Bu, Ku⟩ := wp_result (pos s) E
  obtain ⟨Bz, Kz⟩ := wp_result (pos t) G
  refine ⟨trace, P, ?_, ?_, ?_, ?_⟩
  · rw [PtrAt, Ku.1 .edi (by decide)]; exact H.2.1
  · rw [PtrAt, Kz.1 .edi (by decide)]; exact H.2.2
  · rw [PtrAt, Bu, ptr_add H.2.1]
    rfl
  · rw [PtrAt, Bz, ptr_add H.2.2]
    rfl

theorem rows_relCT {g : Geometry} (v : g.Valid) :
    RelCT isa (BasePair g) Compact.rows (WindowPair g (g.S + Compact.accOff + 4 * g.N)) := by
  unfold Compact.rows
  exact RelCT.seq (accPointer_positioned_relCT v) (rowLoop_relCT v)

theorem front_relCT {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g []) (.seq (.block Compact.scratchPtr) (.seq Compact.zeroAcc Compact.rows))
      (WindowPair g (g.S + Compact.accOff + 4 * g.N)) :=
  RelCT.seq (scratchPointer_positioned_relCT v) (RelCT.seq (zero_relCT v) (rows_relCT v))

end VG.Proof.Mont.X86.Compact
