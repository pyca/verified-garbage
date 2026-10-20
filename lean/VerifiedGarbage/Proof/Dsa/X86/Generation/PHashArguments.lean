module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PHashes
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Frame
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Semantics

/-! # Load one contribution's arguments from the persistent search frame -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86.Generation

theorem pContributionArgs_ok {s : State} {base : Addr} (F : SearchFrame s base) (len count j : Nat) :
    WP isa (.block (pContributionArgs len count j)) s fun t =>
      t.gpr .esi = s.mem.readW (off base 4) 32 ∧
      t.gpr .edi = s.mem.readW (off base 12) 32 ∧
      t.gpr .eax = s.mem.readW (off base 8) 32 + BitVec.ofNat 32 j ∧
      t.gpr .edx = s.mem.readW (off base 16) 32 + BitVec.ofNat 32 ((count - j) * len) ∧
      t.gpr .ebp = s.mem.readW (off base 56) 32 ∧ t.mem = s.mem ∧
      Keeps [.eax, .edx, .esi, .edi, .ebp] s t := by
  have read {t : State} (K : Keeps [.eax, .edx, .esi, .edi, .ebp] s t) (mem : t.mem = s.mem)
      (i : Nat) (hi : i < 37) : readSrc t (.mem (frameSlot i)) = some (s.mem.readW (off base (4 * i)) 32) := by
    rw [(F.keeps K (by decide)).readSlot hi, mem]
  unfold pContributionArgs
  refine wp_movS (F.readSlot (i := 1) (by decide)) fun a sa _ => ?_
  have Ka : Keeps [.eax, .edx, .esi, .edi, .ebp] s a := sa.keeps.mono (by decide)
  refine wp_movS (read Ka sa.mem 3 (by decide)) fun b ab _ => ?_
  have Kb := Ka.trans (ab.keeps.mono (by decide))
  have mb := ab.mem.trans sa.mem
  refine wp_movS (read Kb mb 2 (by decide)) fun c bc _ => wp_addi fun d cd => ?_
  have Kd := (Kb.trans (bc.keeps.mono (by decide))).trans (cd.keeps.mono (by decide))
  have md := cd.mem.trans (bc.mem.trans mb)
  refine wp_movS (read Kd md 4 (by decide)) fun e de _ => wp_addi fun f ef => ?_
  have Kf := (Kd.trans (de.keeps.mono (by decide))).trans (ef.keeps.mono (by decide))
  have mf := ef.mem.trans (de.mem.trans md)
  refine wp_movS (read Kf mf 14 (by decide)) fun t ft _ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ft.gpr, ft.mem.trans mf, Kf.trans (ft.keeps.mono (by decide))⟩
  · rw [ft.other _ (by decide), ef.other _ (by decide), de.other _ (by decide), cd.other _ (by decide),
      bc.other _ (by decide), ab.other _ (by decide), sa.gpr]
  · rw [ft.other _ (by decide), ef.other _ (by decide), de.other _ (by decide), cd.other _ (by decide),
      bc.other _ (by decide), ab.gpr]
  · rw [ft.other _ (by decide), ef.other _ (by decide), de.other _ (by decide), cd.gpr, bc.gpr]
  · rw [ft.other _ (by decide), ef.gpr, de.gpr]
end VG.Proof.Dsa.X86.Generation
