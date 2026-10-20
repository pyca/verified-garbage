module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SaveFrame
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Restore the callee-saved registers without changing the returned status -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86.Generation

theorem restoreRegisters_ok {original s : State} {base : Addr} (F : SaveFrame s base)
    (saved : SavedRegisters original base s.mem) :
    WP isa (.block restoreRegisters) s fun t =>
      t.gpr .ebx = original.gpr .ebx ∧ t.gpr .ebp = original.gpr .ebp ∧
      t.gpr .esi = original.gpr .esi ∧ t.gpr .edi = original.gpr .edi ∧
      t.mem = s.mem ∧ Keeps [.ebx, .ebp, .esi, .edi] s t := by
  change WP isa (.block [.mov .ebx (.mem (VG.Impl.Mont.X86.at_ .esp 0)),
    .mov .ebp (.mem (VG.Impl.Mont.X86.at_ .esp 4)), .mov .esi (.mem (VG.Impl.Mont.X86.at_ .esp 8)),
    .mov .edi (.mem (VG.Impl.Mont.X86.at_ .esp 12))]) s _
  refine wp_movS (by rw [F.read (by decide : 0 < 4), saved.1]) fun a sa _ => ?_
  have Fa := F.keep sa.keeps (by decide)
  refine wp_movS (by rw [Fa.read (by decide : 1 < 4), sa.mem, saved.2.1]) fun b ab _ => ?_
  have Fb := Fa.keep ab.keeps (by decide)
  refine wp_movS (by rw [Fb.read (by decide : 2 < 4), ab.mem, sa.mem, saved.2.2.1]) fun c bc _ => ?_
  have Fc := Fb.keep bc.keeps (by decide)
  refine wp_movS (by rw [Fc.read (by decide : 3 < 4), bc.mem, ab.mem, sa.mem, saved.2.2.2]) fun t ct _ => WP.block_nil ?_
  exact ⟨(ct.other _ (by decide)).trans ((bc.other _ (by decide)).trans ((ab.other _ (by decide)).trans sa.gpr)),
    (ct.other _ (by decide)).trans ((bc.other _ (by decide)).trans ab.gpr),
    (ct.other _ (by decide)).trans bc.gpr, ct.gpr, ct.mem.trans (bc.mem.trans (ab.mem.trans sa.mem)),
    (sa.keeps.mono (by decide)).trans ((ab.keeps.mono (by decide)).trans
      ((bc.keeps.mono (by decide)).trans (ct.keeps.mono (by decide))))⟩
end VG.Proof.Dsa.X86.Generation
