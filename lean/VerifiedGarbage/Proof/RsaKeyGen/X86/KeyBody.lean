module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySized
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEntry
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyFront
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyScratchFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry

/-! # Native cdecl argument entry composes with the complete key body -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys

structure EntryInput (E : Environment) (p : BitVec 32) (s : State) : Prop where
  arguments : KeyArgs.Entry E.base E.size p E.argument s
  outWrite : ∀ i < 7, InRegions s.wr (E.outputRegion i).base (E.outputRegion i).len
  exponentRead : InRegions (s.rd ++ s.wr) E.exponentRegion.base E.exponentRegion.len
  argsOutput : ∀ i < 7, (KeyArgs.argsRegion p).Disjoint (E.outputRegion i)

def bodyClob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi]

theorem enter_input_ok {E : Environment} {p : BitVec 32} {s : State} (v : E.Valid) (I : EntryInput E p s) :
    WP isa VG.Impl.RsaKeyGen.X86.Key.enter s fun t =>
      Input E t ∧ Frame [E.workspaceRegion] s.mem t.mem ∧ Keeps [.eax, .edi] s t := by
  refine WP.mono (KeyArgs.enter_ok I.arguments) fun t ⟨C, header, O, K⟩ => ?_
  have dimensions := v.widths
  have ws : Ws t E.base E.size E.n 32 :=
    ⟨C.scratch, v.bankFit, by omega, by omega⟩
  have input : Input E t := by
    refine ⟨v, ws, header, ?_, ?_⟩
    · intro i hi
      rw [K.2.2]
      exact I.outWrite i hi
    · rw [K.2.1, K.2.2]
      exact I.exponentRead
  have frame : Frame [E.workspaceRegion] s.mem t.mem :=
    outs_scratch_frame (by have := C.scratch.nowrap; omega)
      (Outs.of_outside (rs := [(0, 72)]) O (List.mem_singleton_self _))
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; change 0 + 72 ≤ E.size; exact I.arguments.header)
  exact ⟨input, frame, K⟩

theorem body_ok {E : Environment} {p : BitVec 32} {s : State} (v : E.Valid) (I : EntryInput E p s) :
    WP isa VG.Impl.RsaKeyGen.X86.Key.body s fun t =>
      Ws t E.base E.size E.n 32 ∧ BodyOutcome E s.mem t ∧
      Frame E.outputs.writes s.mem t.mem ∧ Keeps bodyClob s t := by
  unfold VG.Impl.RsaKeyGen.X86.Key.body
  refine WP.seq (WP.mono (enter_input_ok v I) fun a ⟨Ia, F, K⟩ => ?_)
  refine WP.mono (front_ok Ia) fun t ⟨ht, result, Ft, Kt⟩ => ?_
  unfold BodyOutcome at result
  rw [Ia.exponent_preserved F, Ia.output_preserved (by decide : 2 < 7) F,
    Ia.output_preserved (by decide : 3 < 7) F] at result
  refine ⟨ht, result, ?_, (K.mono (by unfold bodyClob; decide)).trans (Kt.mono (by unfold bodyClob; decide))⟩
  exact (F.mono (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact List.mem_cons_self ..)).trans Ft

end VG.Proof.RsaKeyGen.X86.Key
