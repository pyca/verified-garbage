module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialContext
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Load a trial divisor, reciprocal, candidate and chunk count -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86.Generation VG.Impl.RsaKeyGen

theorem trialCheckArgs_ok {s t : State} {base : Addr} {input table : BitVec 32} {len entries i : Nat}
    (R : TrialInputs s base input table len entries) (C : TrialContext s base t) (hi : i < entries)
    (src : trialSlot t.mem base 0 = input) (tab : trialSlot t.mem base 4 = table)
    (idx : trialSlot t.mem base 8 = BitVec.ofNat 32 i) :
    WP isa (.block (trialCheckArgs len)) t fun u => TrialContext s base u ∧ u.mem = t.mem ∧
      u.gpr .esi = BitVec.ofNat 32 (tabEntry i) ∧ u.gpr .edi = BitVec.ofNat 32 (2 ^ 32 / tabEntry i) ∧
      u.gpr .ebp = input ∧ u.gpr .ecx = BitVec.ofNat 32 (len / 2) := by
  have eb := R.entriesBound
  have fit := R.tableFit
  unfold trialCheckArgs
  refine wp_movS (v := BitVec.ofNat 32 i) (by rw [C.frame.read (by decide), idx]) fun a ta _ =>
    wp_addS rfl fun b ab _ => wp_addS rfl fun c bc _ => wp_addS rfl fun d cd _ => ?_
  have Ca := C.upd ta (by decide)
  have Cb := Ca.upd ab (by decide)
  have Cc := Cb.upd bc (by decide)
  have Cd := Cc.upd cd (by decide)
  have mt : d.mem = t.mem := by rw [cd.mem, bc.mem, ab.mem, ta.mem]
  refine wp_addS (v := table) (by rw [Cd.frame.read (by decide), mt, tab]) fun e de _ => ?_
  have Ce := Cd.upd de (by decide)
  have ax : e.gpr .eax = table + BitVec.ofNat 32 (8 * i) := by
    rw [de.gpr, cd.gpr, bc.gpr, ab.gpr, ta.gpr]
    simp only [← BitVec.ofNat_add]
    rw [show i + i + (i + i) + (i + i + (i + i)) = 8 * i by omega, BitVec.add_comm]
  have ptr0 : e.ea (at_ .eax 0) = off (table.setWidth 64) (8 * i) := by
    change (e.gpr .eax + 0#32).setWidth 64 = _
    rw [BitVec.add_zero, ax]; exact addr_eq (by omega)
  have read0 : readSrc e (.mem (at_ .eax 0)) = some (BitVec.ofNat 32 (tabEntry i)) := by
    show e.load32 (e.ea (at_ .eax 0)) = _
    have rd := R.tableRead (8 * i) (by omega)
    rw [← Ce.keeps.2.1, ← Ce.keeps.2.2] at rd
    rw [ptr0, State.load32, ite_eq_left rd, Ce.tableWord R (by omega), R.values.prime i hi]
  refine wp_movS read0 fun f ef _ => ?_
  have Cf := Ce.upd ef (by decide)
  have ptr4 : f.ea (at_ .eax 4) = off (table.setWidth 64) (8 * i + 4) := by
    change (f.gpr .eax + BitVec.ofNat 32 4).setWidth 64 = _
    rw [ef.other _ (by decide), ax, Offset.add_add]
    exact addr_eq (by omega)
  have read4 : readSrc f (.mem (at_ .eax 4)) = some (BitVec.ofNat 32 (2 ^ 32 / tabEntry i)) := by
    show f.load32 (f.ea (at_ .eax 4)) = _
    have rd := R.tableRead (8 * i + 4) (by omega)
    rw [← Cf.keeps.2.1, ← Cf.keeps.2.2] at rd
    rw [ptr4, State.load32, ite_eq_left rd, Cf.tableWord R (by omega), R.values.reciprocal i hi]
  refine wp_movS read4 fun g fg _ => ?_
  have Cg := Cf.upd fg (by decide)
  have mg : g.mem = t.mem := by rw [fg.mem, ef.mem, de.mem, mt]
  refine wp_movS (v := input) (by rw [Cg.frame.read (by decide), mg, src]) fun h gh _ =>
    wp_movS rfl fun u hu _ => WP.block_nil ?_
  exact ⟨(Cg.upd gh (by decide)).upd hu (by decide), by rw [hu.mem, gh.mem, mg],
    by rw [hu.other _ (by decide), gh.other _ (by decide), fg.other _ (by decide), ef.gpr],
    by rw [hu.other _ (by decide), gh.other _ (by decide), fg.gpr],
    by rw [hu.other _ (by decide), gh.gpr], hu.gpr⟩
end VG.Proof.Dsa.X86.Generation
