module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleMemory
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeArguments
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Dsa.X86.Generation.BufferArgs
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameToWorkspace

/-! # Populate the prime engine's tape header from the persistent cursor -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem primeTapeArgs_ok {s : State} {frame base : Addr} {size : Nat} {words : Nat → BitVec 32}
    (F : SearchFrame s frame) (S : Scr s base size) (R : FrameWords s.mem frame words)
    (room : primeWitness + 4 ≤ size) (apart : Region.Disjoint ⟨frame, frameBytes⟩ ⟨base, size⟩) :
    WP isa (.block primeTapeArgs) s fun t =>
      SearchFrame t frame ∧ Scr t base size ∧ FrameWords t.mem frame words ∧
      t.mem = (((s.mem.writeW (off base primeTape) (words 13)).writeW
        (off base primeTapeLen) (words 15)).writeW (off base primeUsed) (words 16)).writeW
          (off base primeWitness) (words 5 + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.witness) ∧
      Outside base primeUsed 24 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold primeTapeArgs
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (frameToWorkspace_ok F S R (by decide : 13 < 37)
    (by unfold primeTape primeWitness at *; omega) apart) fun a ⟨Fa, Sa, Ra, ma, Oa, Ka⟩ => ?_)
  refine WP.block_append (WP.mono (frameToWorkspace_ok Fa Sa Ra (by decide : 15 < 37)
    (by unfold primeTapeLen primeWitness at *; omega) apart) fun b ⟨Fb, Sb, Rb, mb, Ob, Kb⟩ => ?_)
  refine WP.block_append (WP.mono (frameToWorkspace_ok Fb Sb Rb (by decide : 16 < 37)
    (by unfold primeUsed primeWitness at *; omega) apart) fun c ⟨Fc, Sc, Rc, mc, Oc, Kc⟩ => ?_)
  refine WP.block_append (WP.mono (bufferPointer_ok Fc (Rc 5 (by decide)) .eax _) fun d ⟨ax, md, Kd⟩ => ?_)
  have Sd := Sc.of_keeps Kd (by decide)
  refine wp_storeS (Sd.ea (by omega)) (Sd.write room) fun t dt => WP.block_nil ?_
  have K := (((Ka.trans Kb).trans Kc).trans Kd).trans (dt.keeps [.eax])
  have Odt : Outside base primeWitness 4 c.mem t.mem := by
    rw [dt.mem, md]; exact writeW32_outside _ _ _ (by have := S.nowrap; omega)
  have mem : t.mem = (((s.mem.writeW (off base primeTape) (words 13)).writeW
        (off base primeTapeLen) (words 15)).writeW (off base primeUsed) (words 16)).writeW
          (off base primeWitness) (words 5 + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.witness) := by
    rw [dt.mem, ax, md, mc, mb, ma]
  have O : Outside base primeUsed 24 s.mem t.mem :=
    (((Oa.mono (by unfold primeUsed primeTape; omega) (by unfold primeUsed primeTape; omega)).trans
      (Ob.mono (by unfold primeUsed primeTapeLen; omega) (by unfold primeUsed primeTapeLen; omega))).trans
      (Oc.mono (by omega) (by omega))).trans
      (Odt.mono (by unfold primeUsed primeWitness; omega) (by unfold primeUsed primeWitness; omega))
  have frame : Frame [⟨off base primeUsed, 24⟩] s.mem t.mem := by
    exact sampleOuts_frame (Outs.of_outside O (rs := [(primeUsed, 24)]) (by simp)) (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      decide)
  exact ⟨F.keeps K (by decide), S.of_keeps K (by decide), R.keep frame (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact apart.sub_right (Offset.sub_base _ (by unfold primeUsed primeWitness at *; omega))), mem, O, K⟩
end VG.Proof.Dsa.X86.Generation
