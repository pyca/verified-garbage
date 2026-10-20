module

public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingContext
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
import VerifiedGarbage.Proof.Mont.X86.Compact.PairFrame
import VerifiedGarbage.Proof.Mont.X86.Compact.TimingKernels
public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingLift
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Paired rows retain the public prepared header while multiplying secrets -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Dsa.X86

structure RowPointers (g : Geometry) (bx w : Nat) (s : State) : Prop where
  edi : PtrAt s g.W .edi g.S
  ebp : PtrAt s g.W .ebp w
  ecx : PtrAt s g.W .ecx bx
  esi : (s.gpr .esi).toNat = 4 * g.N

theorem pairLoop_relCT {g : Geometry} (v : g.Valid) (bx w : Nat)
    (srcFit : bx + 4 * g.N ≤ g.L) (windowLow : g.S ≤ w)
    (windowHigh : w + 4 * g.N ≤ g.S + 8 * g.N + 28) :
    RelCT isa (fun s t => Pair g [.edi, .ebp, .ecx, .esi] s t ∧ RowPointers g bx w s ∧ RowPointers g bx w t)
      (.loop (.block Rt.pairStep) .ne)
      (fun s t => Pair g [.edi, .ebp, .ecx, .esi] s t ∧
        PtrAt s g.W .ebp (w + 4 * g.N) ∧ PtrAt t g.W .ebp (w + 4 * g.N)) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, A⟩ := pairLoop_relCT_raw _ _ _ _ _ _ H.1.2.2 E G
  have even : g.N % 2 = 0 := by have := H.1.1.metadata.width; omega
  have fit := v.lay.scr
  have mult : Rt.multOff = 20 := rfl
  obtain ⟨Ou, Pu, _, _, Ku⟩ := wp_result (pairLoop_frame H.1.1.ws v.positive even
    H.2.1.edi H.2.1.ecx H.2.1.ebp H.2.1.esi (by omega) srcFit (by omega)) E
  obtain ⟨Oz, Pz, _, _, Kz⟩ := wp_result (pairLoop_frame H.1.2.1.ws v.positive even
    H.2.2.edi H.2.2.ecx H.2.2.ebp H.2.2.esi (by omega) srcFit (by omega)) G
  have writes {m m' : Mem} (O : Outside g.W w (4 * g.N) m m') : Outs g.W g.writes m m' :=
    Outs.widen (Outs.of_outside O (List.mem_singleton_self _)) fun x hx r hr => by
      have outside := hx _ (List.mem_cons_self ..)
      simp only [List.mem_singleton] at hr
      subst hr
      dsimp only at *
      omega
  exact ⟨trace, ⟨H.1.1.keep v Ku (by decide) (writes Ou) (timing_wf_regs A.wf₁),
    H.1.2.1.keep v Kz (by decide) (writes Oz) (timing_wf_regs A.wf₂), A⟩, Pu, Pz⟩

end VG.Proof.Mont.X86.Compact
