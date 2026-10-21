module

public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingLift
import VerifiedGarbage.Proof.Mont.X86.Compact.Digit
import VerifiedGarbage.Proof.Mont.X86.Compact.TimingKernels
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # A reduction digit keeps its data secret and its row position public -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Dsa.X86

theorem digit_relCT {g : Geometry} (v : g.Valid) (w : Nat)
    (high : w + 4 ≤ g.S + 8 * g.N + 28) :
    RelCT isa (WindowPair g w) (.block Compact.redDigit) (WindowPair g w) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, A⟩ := redDigit_relCT _ _ _ _ _ _ H.1.2.2 E G
  have fit := v.lay.scr
  have header := v.lay.header
  have mult : Rt.multOff = 20 := rfl
  obtain ⟨_, Ku, Ou⟩ := wp_result (redDigit_ok H.1.1.ws H.1.1.args v.base H.2.1 H.2.2.2.1
    (by omega) (by omega) (by omega)) E
  obtain ⟨_, Kz, Oz⟩ := wp_result (redDigit_ok H.1.2.1.ws H.1.2.1.args v.base H.2.2.1 H.2.2.2.2
    (by omega) (by omega) (by omega)) G
  have writes {m m' : Mem} (O : Outside g.W (g.S + Rt.multOff) 4 m m') : Outs g.W g.writes m m' :=
    Outs.widen (Outs.of_outside O (List.mem_singleton_self _)) fun x hx r hr => by
      have outside := hx _ (List.mem_cons_self ..)
      simp only [List.mem_singleton] at hr
      subst hr
      dsimp only at *
      omega
  refine ⟨trace, ⟨H.1.1.keep v Ku (by decide) (writes Ou) (timing_wf_regs A.wf₁),
    H.1.2.1.keep v Kz (by decide) (writes Oz) (timing_wf_regs A.wf₂), A⟩, ?_, ?_, ?_, ?_⟩
  · rw [PtrAt, Ku.1 .edi (by decide)]; exact H.2.1
  · rw [PtrAt, Kz.1 .edi (by decide)]; exact H.2.2.1
  · rw [PtrAt, Ku.1 .ebp (by decide)]; exact H.2.2.2.1
  · rw [PtrAt, Kz.1 .ebp (by decide)]; exact H.2.2.2.2

end VG.Proof.Mont.X86.Compact
