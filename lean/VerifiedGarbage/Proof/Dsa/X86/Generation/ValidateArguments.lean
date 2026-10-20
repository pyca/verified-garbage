module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Validate
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ValidateLayout
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArenaReady
import VerifiedGarbage.Proof.Dsa.X86.Generation.BufferArgs

/-! # Prepare the six public arguments without overwriting the persistent frame -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86.Generation

def ValidateRegs (G : GenerationGeometry) (s : State) : Prop :=
  ∀ i < 6, s.gpr (validateReg i) = validateValue G i

theorem validateArgs_ok {G : GenerationGeometry} {s : State} (R : ArenaReady G s)
    (parent : s.mem.readW (off G.frameBase 20) 32 = G.parent) :
    WP isa (.block (validateArgs G.pLen G.qLen)) s fun t => ValidateRegs G t ∧ t.mem = s.mem ∧
      Keeps [.ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  unfold validateArgs
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (bufferPointer_ok R.frame parent .esi _) fun a ⟨si, ma, Ka⟩ => ?_)
  refine WP.block_append (WP.mono (bufferPointer_ok (parent := G.parent) (R.frame.keeps Ka (by decide))
    (by rw [ma]; exact parent) .edi _) fun b ⟨di, mb, Kb⟩ => ?_)
  refine wp_movS rfl fun c bc _ => wp_movS rfl fun d cd _ =>
    wp_movS rfl fun e de _ => wp_movS rfl fun t et _ => WP.block_nil ?_
  have tail : Keeps [.ebx, .ecx, .edx, .ebp] b t :=
    ((bc.keeps.mono (by decide)).trans (cd.keeps.mono (by decide))).trans
      ((de.keeps.mono (by decide)).trans (et.keeps.mono (by decide)))
  refine ⟨?_, et.mem.trans (de.mem.trans (cd.mem.trans (bc.mem.trans (mb.trans ma)))),
    (Ka.mono (by decide)).trans ((Kb.mono (by decide)).trans (tail.mono (by decide)))⟩
  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (tail.1 _ (by decide)).trans ((Kb.1 _ (by decide)).trans si)
  · exact (et.other _ (by decide)).trans ((de.other _ (by decide)).trans ((cd.other _ (by decide)).trans bc.gpr))
  · exact (et.other _ (by decide)).trans ((de.other _ (by decide)).trans cd.gpr)
  · exact (et.other _ (by decide)).trans de.gpr
  · exact (tail.1 _ (by decide)).trans di
  · exact et.gpr
end VG.Proof.Dsa.X86.Generation
