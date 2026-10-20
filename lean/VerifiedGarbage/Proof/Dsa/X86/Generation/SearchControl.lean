module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Search
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Native p-search counter initialization and bounded advancement -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86.Generation

theorem pSearchInit_ok {s : State} {base : Addr} {size : Nat} (S : Scr s base size) (room : 12 ≤ size) :
    WP isa (.block pSearchInit) s fun t => t.mem.readW (off base 0) 32 = 0 ∧
      t.mem.readW (off base 4) 32 = 1 ∧ Outside base 0 8 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold pSearchInit
  refine wp_movS rfl fun a sa _ => ?_
  have Sa := S.of_keeps sa.keeps (by decide)
  refine wp_storeS (Sa.ea (d := 0) (by omega)) (Sa.write (d := 0) (by omega)) fun b ab =>
    wp_movS rfl fun c bc _ => ?_
  have K : Keeps [.eax] s c := (sa.keeps.trans (ab.keeps _)).trans bc.keeps
  have Sc := S.of_keeps K (by decide)
  refine wp_storeS (Sc.ea (d := 4) (by omega)) (Sc.write (d := 4) (by omega)) fun t ct => WP.block_nil ?_
  have mb : b.mem = s.mem.writeW (off base 0) (0 : BitVec 32) := by rw [ab.mem, sa.gpr, sa.mem]
  have mt : t.mem = b.mem.writeW (off base 4) (1 : BitVec 32) := by rw [ct.mem, bc.gpr, bc.mem]
  have Ot : Outside base 4 4 b.mem t.mem := by rw [mt]; exact writeW32_outside _ _ _ (by decide)
  refine ⟨?_, by rw [mt, Mem.readW_writeW_self32], ?_, K.trans (ct.keeps _)⟩
  · have eq : t.mem.readW (off base 0) 32 = b.mem.readW (off base 0) 32 := by
      apply BitVec.eq_of_toNat_eq; exact Ot.w32 (by decide) (by decide)
    rw [eq, mb, Mem.readW_writeW_self32]
  · have Ob : Outside base 0 4 s.mem b.mem := by rw [mb]; exact writeW32_outside _ _ _ (by decide)
    exact (Ob.mono (by omega) (by omega)).trans (Ot.mono (by omega) (by omega))

theorem pSearchAdvanceHead_ok {s : State} {base : Addr} {size index offset limit stride : Nat}
    (S : Scr s base size) (room : 12 ≤ size) (indexBound : index + 1 < 2 ^ 32)
    (limitBound : limit < 2 ^ 32)
    (counter : s.mem.readW (off base 0) 32 = BitVec.ofNat 32 index)
    (position : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 offset) :
    WP isa (.block (pSearchAdvanceHead limit stride)) s fun t =>
      t.mem.readW (off base 0) 32 = BitVec.ofNat 32 (index + 1) ∧
      t.mem.readW (off base 4) 32 = BitVec.ofNat 32 (offset + stride) ∧
      t.cf = some (decide (index + 1 < limit)) ∧ Outside base 0 8 s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
  unfold pSearchAdvanceHead
  refine wp_movS (v := BitVec.ofNat 32 index) (by rw [readSrc_sc S (d := 0) (by omega), counter])
    fun a sa _ => wp_addi fun b ab => ?_
  have Kb : Keeps [.eax, .ecx] s b := (sa.keeps.mono (by decide)).trans (ab.keeps.mono (by decide))
  have Sb := S.of_keeps Kb (by decide)
  refine wp_storeS (Sb.ea (d := 0) (by omega)) (Sb.write (d := 0) (by omega)) fun c bc => ?_
  have vc : b.gpr .eax = BitVec.ofNat 32 (index + 1) := by rw [ab.gpr, sa.gpr]; exact (BitVec.ofNat_add _ _).symm
  have mc : c.mem = s.mem.writeW (off base 0) (BitVec.ofNat 32 (index + 1)) := by rw [bc.mem, vc, ab.mem, sa.mem]
  have Oc : Outside base 0 4 s.mem c.mem := by rw [mc]; exact writeW32_outside _ _ _ (by decide)
  have posc : c.mem.readW (off base 4) 32 = BitVec.ofNat 32 offset := by
    apply Eq.trans ?_ position
    apply BitVec.eq_of_toNat_eq; exact Oc.w32 (by decide) (by decide)
  have Kc := Kb.trans (bc.keeps _)
  refine wp_movS (v := BitVec.ofNat 32 offset) (by rw [readSrc_sc (S.of_keeps Kc (by decide)) (d := 4) (by omega), posc])
    fun d cd _ => wp_addi fun e de => ?_
  have Ke := (Kc.trans (cd.keeps.mono (by decide))).trans (de.keeps.mono (by decide))
  have Se := S.of_keeps Ke (by decide)
  refine wp_storeS (Se.ea (d := 4) (by omega)) (Se.write (d := 4) (by omega)) fun f ef =>
    wp_cmpi fun t ft cf _ => WP.block_nil ?_
  have ve : e.gpr .ecx = BitVec.ofNat 32 (offset + stride) := by rw [de.gpr, cd.gpr, ← BitVec.ofNat_add]
  have mt : t.mem = c.mem.writeW (off base 4) (BitVec.ofNat 32 (offset + stride)) := by rw [ft.mem, ef.mem, ve, de.mem, cd.mem]
  have Ot : Outside base 4 4 c.mem t.mem := by rw [mt]; exact writeW32_outside _ _ _ (by decide)
  refine ⟨?_, by rw [mt, Mem.readW_writeW_self32], ?_,
    (Oc.mono (by omega) (by omega)).trans (Ot.mono (by omega) (by omega)), Ke.trans ((ef.keeps _).trans (ft.keeps _))⟩
  · have eq : t.mem.readW (off base 0) 32 = c.mem.readW (off base 0) 32 := by
      apply BitVec.eq_of_toNat_eq; exact Ot.w32 (by decide) (by decide)
    rw [eq, mc, Mem.readW_writeW_self32]
  · rw [cf, ef.gpr, de.other _ (by decide), cd.other _ (by decide), bc.gpr, vc,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt indexBound, Nat.mod_eq_of_lt limitBound]
end VG.Proof.Dsa.X86.Generation
