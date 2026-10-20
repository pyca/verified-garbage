module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.DrawWitness
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Whole-draw consumption and the significant-byte slice passed to the copier -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86.Generation

theorem drawWitnessArgs_ok {s : State} {base : Addr} {size len draw used : Nat} {tape out : BitVec 32}
    (S : Scr s base size) (room : primeWitness + 4 ≤ size)
    (source : s.mem.readW (off base primeTape) 32 = tape)
    (consumed : s.mem.readW (off base primeUsed) 32 = BitVec.ofNat 32 used)
    (output : s.mem.readW (off base primeWitness) 32 = out) :
    WP isa (.block (drawWitnessArgs len draw)) s fun t =>
      t.gpr .esi = tape + BitVec.ofNat 32 (used + (draw - len)) ∧
      t.gpr .edx = out ∧ t.gpr .ecx = BitVec.ofNat 32 len ∧ t.gpr .ebx = BitVec.allOnes 32 ∧
      t.mem = s.mem.writeW (off base primeUsed) (BitVec.ofNat 32 (used + draw)) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := by
  have tapeRoom : primeTape + 4 ≤ size := by unfold primeTape primeWitness at *; omega
  have usedRoom : primeUsed + 4 ≤ size := by unfold primeUsed primeWitness at *; omega
  unfold drawWitnessArgs
  refine wp_movS (v := tape) (by rw [readSrc_sc S tapeRoom, source]) fun a sa _ => ?_
  have Sa := S.of_keeps sa.keeps (by decide)
  refine wp_movS (v := BitVec.ofNat 32 used) (by rw [readSrc_sc Sa usedRoom, sa.mem, consumed]) fun b ab _ =>
    wp_addS rfl fun c bc _ => wp_addi fun d cd => wp_addi fun e de => ?_
  have Ke : Keeps [.eax, .ebx, .ecx, .edx, .esi] s e :=
    ((((sa.keeps.mono (by decide)).widen ab.keeps).widen bc.keeps).widen cd.keeps).widen de.keeps
  have Se := S.of_keeps Ke (by decide)
  have usedValue : e.gpr .eax = BitVec.ofNat 32 (used + draw) := by
    rw [de.gpr, cd.other _ (by decide), bc.other _ (by decide), ab.gpr, ← BitVec.ofNat_add]
  have me : e.mem = s.mem := by rw [de.mem, cd.mem, bc.mem, ab.mem, sa.mem]
  refine wp_storeS (Se.ea (by omega)) (Se.write usedRoom) fun f ef => ?_
  have Kf := Ke.trans (ef.keeps _)
  have Sf := S.of_keeps Kf (by decide)
  have outRead : readSrc f (.mem (sc primeWitness)) = some out := by
    rw [readSrc_sc Sf room, ef.mem, Mem.readW_writeW_sep
      (Offset.sep base (by decide : primeWitness + 4 ≤ primeUsed ∨ primeUsed + 4 ≤ primeWitness)
        (by decide) (by decide)) (by decide), me, output]
  refine wp_movS outRead fun g fg _ => wp_movS rfl fun h gh _ => wp_movS rfl fun t ht _ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ht.gpr, ?_, ((Kf.widen fg.keeps).widen gh.keeps).widen ht.keeps⟩
  · rw [ht.other _ (by decide), gh.other _ (by decide), fg.other _ (by decide), ef.gpr,
      de.other _ (by decide), cd.gpr, bc.gpr, ab.other _ (by decide), sa.gpr, ab.gpr,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [ht.other _ (by decide), gh.other _ (by decide), fg.gpr]
  · rw [ht.other _ (by decide), gh.gpr]
  · rw [ht.mem, gh.mem, fg.mem, ef.mem, usedValue, me]
end VG.Proof.Dsa.X86.Generation
