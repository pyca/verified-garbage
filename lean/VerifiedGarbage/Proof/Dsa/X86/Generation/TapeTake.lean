module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.TapeLoop
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.Words32

/-! # Advance a complete tape chunk without changing the other frame words -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem tapeTake_ok {s : State} {base : Addr} {words : Nat → BitVec 32} {used : Nat}
    (F : SearchFrame s base) (R : FrameWords s.mem base words) (slots : TapeSlots) (width : Nat)
    (hb : slots.base < 37) (hu : slots.used < 37) (hp : slots.pointer < 37)
    (usedValue : words slots.used = BitVec.ofNat 32 used) :
    WP isa (.block (tapeTake slots width)) s fun t => SearchFrame t base ∧
      FrameWords t.mem base (frameUpdate (frameUpdate words slots.pointer
        (words slots.base + BitVec.ofNat 32 used)) slots.used (BitVec.ofNat 32 (used + width))) ∧
      Outside base 0 frameBytes s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
  unfold tapeTake
  refine wp_movS (F.readWord R hb) fun a sa _ => ?_
  have Fa := F.keeps sa.keeps (by decide)
  refine wp_movS (v := BitVec.ofNat 32 used)
    (by rw [Fa.readSlot hu, sa.mem, R _ hu, usedValue]) fun b ab _ =>
    wp_addS rfl fun c bc _ => wp_addi fun d cd => ?_
  have K : Keeps [.eax, .ecx] s d :=
    (((sa.keeps.mono (by decide)).trans (ab.keeps.mono (by decide))).trans
      (bc.keeps.mono (by decide))).trans (cd.keeps.mono (by decide))
  have Fd := F.keeps K (by decide)
  refine wp_storeS (Fd.ea hp) (Fd.writable hp) fun e de => ?_
  have Fe := Fd.keeps (de.keeps []) (by decide)
  refine wp_storeS (Fe.ea hu) (Fe.writable hu) fun t et => WP.block_nil ?_
  have valA : d.gpr .eax = words slots.base + BitVec.ofNat 32 used := by
    rw [cd.other _ (by decide), bc.gpr, ab.other _ (by decide), sa.gpr, ab.gpr]
  have valC : e.gpr .ecx = BitVec.ofNat 32 (used + width) := by
    rw [de.gpr, cd.gpr, bc.other _ (by decide), ab.gpr, BitVec.ofNat_add]
  have mem : t.mem = (s.mem.writeW (off base (4 * slots.pointer))
      (words slots.base + BitVec.ofNat 32 used)).writeW
        (off base (4 * slots.used)) (BitVec.ofNat 32 (used + width)) := by
    rw [et.mem, valC, de.mem, valA, cd.mem, bc.mem, ab.mem, sa.mem]
  have Kt := (K.trans (de.keeps _)).trans (et.keeps _)
  refine ⟨F.keeps Kt (by decide), ?_, ?_, Kt⟩
  · rw [mem]; exact (R.write hp _).write hu _
  · rw [mem]
    exact ((writeW32_outside _ base _ (d := 4 * slots.pointer) (by omega)).mono (by omega)
      (by unfold frameBytes; omega)).trans
      ((writeW32_outside _ base _ (d := 4 * slots.used) (by omega)).mono (by omega)
        (by unfold frameBytes; omega))
end VG.Proof.Dsa.X86.Generation
